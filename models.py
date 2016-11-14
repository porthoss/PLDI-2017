import sys
sys.path.append('./src')
from programs import *
from time import time
from satRels import *
from random import choice

def PowerConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    t0 = time()
    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTrans('idd', eventsLPerThread))
    enc = And(enc, satIntersection('idd^+', 'RW', events, 'data'))

    ### Fences in Power
    enc = And(enc, satUnion('sync', 'ffence', events))
    enc = And(enc, satMinus('lwsync', 'WR', events, 'lwfence'))
    enc = And(enc, satUnion('ffence', 'lwfence', events, 'fence'))

    ### Some other relations
    enc = And(enc, satEmpty('addr', events))
    enc = And(enc, satUnion('addr', 'data', events, 'dp'))
    for l in locs:
        eventsPerLoc = [e for e in events if e.loc == l]
        enc = And(enc, satCompFreRfe(eventsPerLoc))
        enc = And(enc, satCompWseRfe(eventsPerLoc))
    enc = And(enc, satIntersection('poloc', '(fre;rfe)', events, 'rdw'))
    enc = And(enc, satIntersection('poloc', '(wse;rfe)', events, 'detour'))

    ### Base case for the recursion
    enc = And(enc, satUnion('dp', 'rdw', events))
    enc = And(enc, satUnion('(dp+rdw)', 'rfi', events, 'ii0'))
    enc = And(enc, satEmpty('ic0', events))
    enc = And(enc, satUnion('ctrlisync', 'detour', events, 'ci0'))
    enc = And(enc, satUnion('dp', 'poloc', events))
    enc = And(enc, satUnion('(dp+poloc)', 'ctrl', events))
    for t in threads:
        eventsPerThread = [e for e in events if e.thread == t]
        enc = And(enc, satComp('addr', 'po', eventsPerThread))
        ### Recursive
        enc = And(enc, satPowerPPO(eventsPerThread))
    enc = And(enc, satUnion('((dp+poloc)+ctrl)', '(addr;po)', events, 'cc0'))

    ### PPO for Power
    enc = And(enc, satIntersection('RR', 'ii', events))
    enc = And(enc, satIntersection('RW', 'ic', events))
    enc = And(enc, satUnion('(RR&ii)', '(RW&ic)', events, 'ppoW'))

    ### Thin air check
    enc = And(enc, satUnion('ppoW', 'rfe', events))
    enc = And(enc, satUnion('(ppoW+rfe)', 'fence', events, 'hbW'))
    enc = And(enc, satAcyclic('hbW', events))

    ### Prop-base
    enc = And(enc, satCompRfeFence(events))
    enc = And(enc, satUnion('fence', '(rfe;fence)', events))
    enc = And(enc, satTransRef('hbW', events))
    enc = And(enc, satComp('(fence+(rfe;fence))', '(hbW)*', events, 'prop-base'))

    ### Prop for Power
    for l in locs:
        eventsPerLoc = [e for e in events if e.loc == l]
        enc = And(enc, satTransRef('com', eventsPerLoc))
    enc = And(enc, satTransRef('prop-base', events))
    enc = And(enc, satCompComProp(events))
    enc = And(enc, satCompComPropSync(events))
    enc = And(enc, satComp('(((com)*;(prop-base)*);sync)', '(hbW)*', events))
    enc = And(enc, satIntersection('WW', 'prop-base', events))
    enc = And(enc, satUnion('(WW&prop-base)', '((((com)*;(prop-base)*);sync);(hbW)*)', events, 'prop'))

    ### Observation check
    enc = And(enc, satCompFreProp(events))
    enc = And(enc, satCompFrePropHb(events))
    enc = And(enc, satIrref('((fre;prop);(hbW)*)', events))

    ### Propagation check
    enc = And(enc, satUnion('ws', 'prop', events))
    enc = And(enc, satAcyclic('(ws+prop)', events))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    return enc 

def CavConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    ### PPO for CAV
    enc = True
    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTrans('idd', eventsLPerThread))
        enc = And(enc, satIntersection('idd^+', 'RW', eventsLPerThread, 'data'))
        enc = And(enc, satIntersection('poloc', 'WR', eventsLPerThread))
        enc = And(enc, satUnion('data', '(poloc&WR)', eventsLPerThread))
        enc = And(enc, satTrans('(data+(poloc&WR))', eventsLPerThread))
        enc = And(enc, satIntersection('(data+(poloc&WR))^+', 'RM', eventsLPerThread))
        enc = And(enc, satUnion('ctrl', 'isync', eventsLPerThread))
        enc = And(enc, satUnion('(ctrl+isync)', '((data+(poloc&WR))^+&RM)', eventsLPerThread, 'ppoW'))

    ### Fences for CAV
    enc = And(enc, satFencesCAV(events))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    ### CAV happens Before
    enc = And(enc, satUnion('(ws+fr)', 'fenceCAV', events))
    enc = And(enc, satUnion('((ws+fr)+fenceCAV)', 'ppoW', events, 'ghbS'))
    enc = And(enc, satAcyclic('ghbW', events))

    return enc 

def AlphaConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    ### Thin air
    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTransFixPoint('idd', eventsLPerThread))
    enc = And(enc, satIntersection('idd^+', 'RW', events, 'data'))
    enc = And(enc, satUnion('rf', 'data', events))
    enc = And(enc, satAcyclic('(rf+data)', events))

    ### Alpha
    enc = And(enc, satUnion('WW', 'RM', events))
    enc = And(enc, satIntersection('(WW+RM)', 'loc', events))
    enc = And(enc, satIntersection('po', '((WW+RM)&loc)', events, 'ppoW'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
    enc = And(enc, satAcyclic('ghbW', events))

    return enc

def RmoConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satMinus('poloc', 'RR', events))
    enc = And(enc, satUnion('(poloc\RR)', 'com', events))
    enc = And(enc, satAcyclic('((poloc\RR)+com)', events))

    ### RMO
    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTrans('idd', eventsLPerThread))
    enc = And(enc, satIntersection('idd^+', 'RW', events, 'data'))
    enc = And(enc, satEmpty('addr', events))
    enc = And(enc, satUnion('addr', 'data', events, 'ppoW'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
    enc = And(enc, satAcyclic('ghbW', events))

    return enc

def PsoConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    ### PSO
    enc = And(enc, satIntersection('po', 'RM', events, 'ppoW'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
    enc = And(enc, satAcyclic('ghbW', events))

    return enc

def TsoConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    ### TSO
    enc = And(enc, satMinus('po', 'WR', events, 'ppoW'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
    enc = And(enc, satAcyclic('ghbW', events))

    return enc

def TsoToplasConsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    ### TSO
    enc = And(enc, satMinus('po', 'WR', events, 'ppoW'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('ppoW', 'fence', events))
    enc = And(enc, satUnion('(ppoW+fence)', 'rfe', events, 'hbW'))
    enc = And(enc, satUnion('hbW', 'fr', events, 'prop'))

    ### Thin Air
    enc = And(enc, satAcyclic('hbW', events))

    ### Observation
    enc = And(enc, satComp('fre', 'prop', events))
    enc = And(enc, satTransRef('hbW', events))
    enc = And(enc, satComp('(fre;prop)', '(hbW)*', events))
    enc = And(enc, satIrref('((fre;prop);(hbW)*)', events))

    ### Propagation
    enc = And(enc, satUnion('ws', 'prop', events))
    enc = And(enc, satAcyclic('(ws+prop)', events))

    return enc

def PowerInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    t0 = time()
    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTrans('idd', eventsLPerThread))
    enc = And(enc, satIntersection('idd^+', 'RW', events, 'data'))

    ### Fences in Power
    enc = And(enc, satUnion('sync', 'ffence', events))
    enc = And(enc, satMinus('lwsync', 'WR', events, 'lwfence'))
    enc = And(enc, satUnion('ffence', 'lwfence', events, 'fence'))

    ### Some other relations
    enc = And(enc, satEmpty('addr', events))
    enc = And(enc, satUnion('addr', 'data', events, 'dp'))
    for l in locs:
        eventsPerLoc = [e for e in events if e.loc == l]
        enc = And(enc, satCompFreRfe(eventsPerLoc))
        enc = And(enc, satCompWseRfe(eventsPerLoc))
    enc = And(enc, satIntersection('poloc', '(fre;rfe)', events, 'rdw'))
    enc = And(enc, satIntersection('poloc', '(wse;rfe)', events, 'detour'))

    ### Base case for the recursion
    enc = And(enc, satUnion('dp', 'rdw', events))
    enc = And(enc, satUnion('(dp+rdw)', 'rfi', events, 'ii0'))
    enc = And(enc, satEmpty('ic0', events))
    enc = And(enc, satUnion('ctrlisync', 'detour', events, 'ci0'))
    enc = And(enc, satUnion('dp', 'poloc', events))
    enc = And(enc, satUnion('(dp+poloc)', 'ctrl', events))
    for t in threads:
        eventsPerThread = [e for e in events if e.thread == t]
        enc = And(enc, satComp('addr', 'po', eventsPerThread))
        ### Recursive
        enc = And(enc, satPowerPPO(eventsPerThread))
    enc = And(enc, satUnion('((dp+poloc)+ctrl)', '(addr;po)', events, 'cc0'))

    ### PPO for Power
    enc = And(enc, satIntersection('RR', 'ii', events))
    enc = And(enc, satIntersection('RW', 'ic', events))
    enc = And(enc, satUnion('(RR&ii)', '(RW&ic)', events, 'ppoS'))

    ### Thin air check
    enc = And(enc, satUnion('ppoS', 'rfe', events))
    enc = And(enc, satUnion('(ppoS+rfe)', 'fence', events, 'hbS'))

    ### Prop-base
    enc = And(enc, satCompRfeFence(events))
    enc = And(enc, satUnion('fence', '(rfe;fence)', events))
    enc = And(enc, satTransRef('hbS', events))
    enc = And(enc, satComp('(fence+(rfe;fence))', '(hbS)*', events, 'prop-base'))

    ### Prop for Power
    for l in locs:
        eventsPerLoc = [e for e in events if e.loc == l]
        enc = And(enc, satTransRef('com', eventsPerLoc))
    enc = And(enc, satTransRef('prop-base', events))
    enc = And(enc, satCompComProp(events))
    enc = And(enc, satCompComPropSync(events))
    enc = And(enc, satComp('(((com)*;(prop-base)*);sync)', '(hbS)*', events))
    enc = And(enc, satIntersection('WW', 'prop-base', events))
    enc = And(enc, satUnion('(WW&prop-base)', '((((com)*;(prop-base)*);sync);(hbS)*)', events, 'prop'))

    ### Observation check
    enc = And(enc, satCompFreProp(events))
    enc = And(enc, satCompFrePropHb(events))

    ### Propagation check
    enc = And(enc, satUnion('ws', 'prop', events))

    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))

    ### Axiom violation
    enc = And(enc, Or(satCycle('hbS', events), satCycle('(ws+prop)', events), satCycle('(poloc+com)', events), satRef('((fre;prop);(hbS)*)', events)))

    return enc 
    

def CavInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    ### PPO for CAV
    enc = True
    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTrans('idd', eventsLPerThread))
        enc = And(enc, satIntersection('idd^+', 'RW', eventsLPerThread, 'data'))
        enc = And(enc, satIntersection('poloc', 'WR', eventsLPerThread))
        enc = And(enc, satUnion('data', '(poloc&WR)', eventsLPerThread))
        enc = And(enc, satTrans('(data+(poloc&WR))', eventsLPerThread))
        enc = And(enc, satIntersection('(data+(poloc&WR))^+', 'RM', eventsLPerThread))
        enc = And(enc, satUnion('ctrl', 'isync', eventsLPerThread))
        enc = And(enc, satUnion('(ctrl+isync)', '((data+(poloc&WR))^+&RM)', eventsLPerThread, 'ppoS'))

    ### Fences for CAV
    enc = And(enc, satFencesCAV(events))
    
    ### SC per location
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events, 'com'))
    enc = And(enc, satUnion('poloc', 'com', events))
    enc = And(enc, satAcyclic('(poloc+com)', events))

    ### Cycle detection
    enc = And(enc, satUnion('(ws+fr)', 'fenceCAV', events))
    enc = And(enc, satUnion('((ws+fr)+fenceCAV)', 'ppoS', events, 'ghbS'))
    enc = And(enc, satCycle('ghbS', events))

    return enc 


def AlphaInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    enc = encodeDomain(events, barriers, eventsL)
    enc = And(enc, encode(m))

    ### Thin air
    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTrans('idd', eventsLPerThread))
    enc = And(enc, satIntersection('idd^+', 'RW', events, 'data'))
    enc = And(enc, satUnion('data', 'ctrl', events, 'dp'))
    enc = And(enc, satUnion('rf', 'dp', events))
    enc = And(enc, satAcyclic('(rf+dp)', events))

    ### Alpha
    enc = And(enc, satUnion('WW', 'RM', events))
    enc = And(enc, satIntersection('(WW+RM)', 'loc', events))
    enc = And(enc, satIntersection('po', '((WW+RM)&loc)', events, 'ppoS'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoS', events, 'ghbS'))
    enc = And(enc, satCycle('ghbS', events))

    return enc

def RmoInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    enc = True
    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        enc = And(enc, satTransFixPoint('idd', eventsLPerThread))
    enc = And(enc, satIntersection('idd^+', 'RW', events, 'data'))
    enc = And(enc, satEmpty('addr', events))
    enc = And(enc, satUnion('addr', 'data', events, 'ppoS'))
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoS', events, 'ghbS'))
    enc = And(enc, satCycle('ghbS', events))

    return enc

def PsoInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]

    enc = satIntersection('po', 'RM', events, 'ppoS')
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoS', events, 'ghbS'))
    enc = And(enc, satCycle('ghbS', events))

    return enc

def TsoInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]

    enc = satMinus('po', 'WR', events, 'ppoS')
    enc = And(enc, satEq('mfence', 'fence', events))
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    enc = And(enc, satUnion('((ws+fr)+rfe)', 'fence', events))
    enc = And(enc, satUnion('(((ws+fr)+rfe)+fence)', 'ppoS', events, 'ghbS'))
    enc = And(enc, satCycle('ghbS', events))

    return enc

def ScInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]

    enc = satEq('po', 'ppoS', events)
    enc = And(enc, satUnion('ws', 'fr', events))
    enc = And(enc, satUnion('(ws+fr)', 'rf', events))
    enc = And(enc, satUnion('((ws+fr)+rf)', 'ppoS', events, 'ghbS'))
    enc = And(enc, satCycle('ghbS', events))

    return enc

def McaInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]

    ### New to handle RF not reading from init
    enc = satMinus('rf', 'IM', events, 'rf2')
    enc = And(enc, satMinus('rfe', 'IM', events, 'rfe2'))
    enc = And(enc, satIntersection('id', 'RR', events, '[R]'))
    enc = And(enc, satIntersection('id', 'WW', events, '[W]'))
    enc = And(enc, satInverse('rf2', events))
    enc = And(enc, satComp('(rf2)^-1', 'rf2', events))
    enc = And(enc, satMinus('[R]', '((rf2)^-1;rf2)', events))
    enc = And(enc, satComp('([R]\((rf2)^-1;rf2))', 'loc', events))
    enc = And(enc, satComp('(([R]\((rf2)^-1;rf2));loc)', '[W]', events, 'frinit'))

    ### WO-PPO cycle detection
    enc = And(enc, satComp('rfe2', 'ppoW', events))
    enc = And(enc, satInverse('rfe2', events))
    enc = And(enc, satComp('(rfe2;ppoW)', '(rfe2)^-1', events))
    enc = And(enc, satMinus('((rfe2;ppoW);(rfe2)^-1)', 'id', events))
    enc = And(enc, satComp('(((rfe2;ppoW);(rfe2)^-1)\id)', 'ws', events))
    enc = And(enc, satComp('(rfe2;ppoW)', 'frinit', events))
    enc = And(enc, satUnion('((((rfe2;ppoW);(rfe2)^-1)\id);ws)', '((rfe2;ppoW);frinit)', events, 'cycle1'))
    enc = And(enc, satUnion('poloc', 'ws', events, 'cycle2'))
    enc = And(enc, Or(satCycle('cycle1', events), satCycle('cycle2', events)))

    return enc

def Dead(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]

    ### New to handle RF not reading from init
    enc = satMinus('rf', 'IM', events, 'rf2')
    enc = And(enc, satMinus('ws', 'IM', events, 'ws2'))

    ### Dead (35)
    enc = And(enc, satDomRanIncl('ctrl', 'rf2', events))

    ### Dead (36.1)
    enc = And(enc, satImm('ws2', events))
    enc = And(enc, satComp('imm(ws2)', 'imm(ws2)', events))
    enc = And(enc, satInverse('ws2', events))
    enc = And(enc, satImm('(ws2)^-1', events))
    enc = And(enc, satComp('(imm(ws2);imm(ws2))', 'imm((ws2)^-1)', events))

    ### Dead (36.2)
    enc = And(enc, satRefClos('rf2', events))
    enc = And(enc, satInverse('rf2', events))
    enc = And(enc, satRefClos('(rf2)^-1', events))
    enc = And(enc, satComp('po', '((rf2)^-1)?', events))
    enc = And(enc, satRefClos('(po;((rf2)^-1)?)', events))
    enc = And(enc, satComp('(rf2)?', '((po;((rf2)^-1)?))?', events))

    ### Dead (36.3)
    enc = And(enc, satIncl('((imm(ws2);imm(ws2));imm((ws2)^-1))', '((rf2)?;((po;((rf2)^-1)?))?)', events))

    return enc

def PowerSC(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(ScInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 13)

    return res

def PowerTSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(TsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 14)

    return res

def PowerPSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(PsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 15)

    return res

def PowerRMO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(RmoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 16)

    return res

def PowerAlpha(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(AlphaInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 17)

    return res

def PowerCAV(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(CavInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    return res

def PowerMCA(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PowerConsistent(m))
    s.add(McaInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    return res

def CAVPower(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(CavConsistent(m))
    s.add(PowerInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    return res

def AlphaSC(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(AlphaConsistent(m))
    s.add(ScInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 5)

    return res

def AlphaTSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(AlphaConsistent(m))
    s.add(TsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 8)

    return res

def AlphaPSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(AlphaConsistent(m))
    s.add(PsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 10)

    return res

def AlphaRMO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(AlphaConsistent(m))
    s.add(RmoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 11)

    return res

def RMOSC(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(RmoConsistent(m))
    s.add(ScInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 4)

    return res

def RMOTSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(RmoConsistent(m))
    s.add(TsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 7)

    return res

def RMOPSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(RmoConsistent(m))
    s.add(PsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 9)

    return res

def RMOAlpha(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(RmoConsistent(m))
    s.add(AlphaInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 12)

    return res

def PSOSC(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PsoConsistent(m))
    s.add(ScInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 3)

    return res

def PSOTSO(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(PsoConsistent(m))
    s.add(TsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 6)

    return res

def ToplasThesisTSO(m, dead=False, verbose=False):

    s = Solver()
    t0 = time()
    s.add(TsoToplasConsistent(m))
    enc = And(enc, satUnion('(ws+fr)', 'rfe', events))
    s.add(TsoInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    return res

def TSOMCA(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(TsoConsistent(m))
    s.add(McaInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    return res

def TSOSC(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(TsoConsistent(m))
    s.add(ScInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 2)

    return res

def ToplasTSOSC(m, dead=False, write=False):

    s = Solver()
    t0 = time()
    s.add(TsoToplasConsistent(m))
    s.add(ScInconsistent(m))
    text = ""
    if dead:
        s.add(Dead(m))
        text = " (Dead)"

    t1 = time()
    res = s.check()
    t2 = time()

    if write:
        writeColumn(m.name, res == unsat, t1-t0, t2-t1, 3)

    return res

#def ToplasPowerSC(m):
def TestPower(m):

    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

    s = Solver()

    t0 = time()
    s.add(encodeDom(events, barriers, eventsL))
#    s.add(encodeDomain(events, barriers, eventsL))
    s.add(encode(m))

    for t in threads:
        eventsLPerThread = [e for e in eventsL if e.thread == t]
        s.add(satTrans('idd', eventsLPerThread))
    s.add(satIntersection('idd^+', 'RW', events, 'data'))

    ### Fences in Power
    s.add(satEq('sync', 'ffence', events))
    s.add(satMinus('lwsync', 'WR', events, 'lwfence'))
    s.add(satUnion('ffence', 'lwfence', events, 'fence'))

    ### Some other relations
    s.add(satEmpty('addr', events))
    s.add(satUnion('addr', 'data', events, 'dp'))

    t0 = time()
    s.add(satComp('fre', 'rfe', events))
    t1 = time()
    print "Old: %.2f" %(t1-t0)
    (dom, mid, ran) = satApprox('fre', 'rfe', events)
    print dom
    print mid
    print ran
    print events
    s.add(satComp2('fre', 'rfe', dom, mid, ran))
    t2 = time()
    print "New: %.2f" %(t2-t1)
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
##        s.add(satComp('fre', 'rfe', eventsPerLoc))
#        s.add(satCompFreRfe(eventsPerLoc))
##        s.add(satComp('wse', 'rfe', eventsPerLoc))
#        s.add(satCompWseRfe(eventsPerLoc))
    s.add(satIntersection('poloc', '(fre;rfe)', events, 'rdw'))
    s.add(satIntersection('poloc', '(wse;rfe)', events, 'detour'))

    ### Base case for the recursion
    s.add(satUnion('dp', 'rdw', events))
    s.add(satUnion('(dp+rdw)', 'rfi', events, 'ii0'))
    s.add(satEmpty('ic0', events))
    s.add(satUnion('ctrlisync', 'detour', events, 'ci0'))
    s.add(satUnion('dp', 'poloc', events))
    s.add(satUnion('(dp+poloc)', 'ctrl', events))
    for t in threads:
        eventsPerThread = [e for e in events if e.thread == t]
        s.add(satComp('addr', 'po', eventsPerThread))
        ### Recursive
        s.add(satPowerPPO(eventsPerThread))
    s.add(satUnion('((dp+poloc)+ctrl)', '(addr;po)', events, 'cc0'))

    ### PPO for Power
    s.add(satIntersection('RR', 'ii', events))
    s.add(satIntersection('RW', 'ic', events))
    s.add(satUnion('(RR&ii)', '(RW&ic)', events, 'ppoW'))

    ### Thin air check
    s.add(satUnion('ppoW', 'rfe', events))
    s.add(satUnion('(ppoW+rfe)', 'fence', events, 'hbW'))
    s.add(satAcyclic('hbW', events))

    ### Prop-base
#    s.add(satComp('rfe', 'fence', events))
    s.add(satCompRfeFence(events))
    s.add(satUnion('fence', '(rfe;fence)', events))
    s.add(satTransRef('hbW', events))
    s.add(satComp('(fence+(rfe;fence))', '(hbW)*', events, 'prop-base'))

    ### Prop for Power
    for l in locs:
        eventsPerLoc = [e for e in events if e.loc == l]
        s.add(satTransRef('com', eventsPerLoc))
    s.add(satTransRef('prop-base', events))
#    s.add(satComp('(com)*', '(prop-base)*', events))
    s.add(satCompComProp(events))
#    s.add(satComp('((com)*;(prop-base)*)', 'sync', events))
    s.add(satCompComPropSync(events))
    s.add(satComp('(((com)*;(prop-base)*);sync)', '(hbW)*', events))
    s.add(satIntersection('WW', 'prop-base', events))
    s.add(satUnion('(WW&prop-base)', '((((com)*;(prop-base)*);sync);(hbW)*)', events, 'prop'))

    ### Observation check
#    s.add(satComp('fre', 'prop', events))
    s.add(satCompFreProp(events))
#    s.add(satComp('(fre;prop)', '(hbW)*', events))
    s.add(satCompFrePropHb(events))
    s.add(satIrref('((fre;prop);(hbW)*)', events))

    ### Propagation check
    s.add(satUnion('ws', 'prop', events))
    s.add(satAcyclic('(ws+prop)', events))

    ### SC per location
    s.add(satUnion('ws', 'rf', events))
    s.add(satUnion('(ws+rf)', 'fr', events, 'com'))
    s.add(satUnion('poloc', 'com', events))
    s.add(satAcyclic('(poloc+com)', events))

    ###########################
    ### SC with cycle detection
    s.add(satEq('po', 'ppoS', events))
    s.add(satUnion('ws', 'fr', events))
    s.add(satUnion('(ws+fr)', 'rf', events))
    s.add(satUnion('((ws+fr)+rf)', 'ppoS', events, 'ghbS'))
    s.add(satCycle('ghbS', events))

    t1 = time()
    res = s.check()
    print res
    t2 = time()
    print "Encoding: %.2f" %(t1-t0)
    print "Solving: %.2f" %(t2-t1)

    return res
#
#def ToplasPowerMCA(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
#    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))
#
#    s = Solver()
#
#    t0 = time()
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### NEW: to handle no Init
#    s.add(satMinus('fr', 'IM', events, 'fr2'))
#    s.add(satMinus('fre', 'IM', events, 'fre2'))
#    s.add(satMinus('rf2', 'MI', events, 'rf2'))
#    s.add(satMinus('rfe2', 'MI', events, 'rfe2'))
#    s.add(satMinus('rfi2', 'MI', events, 'rfi2'))
#
#    for t in threads:
#        eventsLPerThread = [e for e in eventsL if e.thread == t]
#        s.add(satTrans('idd', eventsLPerThread))
#    s.add(satIntersection('idd^+', 'RW', events, 'data'))
#
#    ### Fences in Power
#    s.add(satEq('sync', 'ffence', events))
#    s.add(satMinus('lwsync', 'WR', events, 'lwfence'))
#    s.add(satUnion('ffence', 'lwfence', events, 'fence'))
#
#    ### Some other relations
#    s.add(satEmpty('addr', events))
#    s.add(satUnion('addr', 'data', events, 'dp'))
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
#        s.add(satComp('fre2', 'rfe2', eventsPerLoc))
#        s.add(satComp('wse', 'rfe2', eventsPerLoc))
#    s.add(satIntersection('poloc', '(fre2;rfe2)', events, 'rdw'))
#    s.add(satIntersection('poloc', '(wse;rfe2)', events, 'detour'))
#
#    ### Base case for the recursion
#    s.add(satUnion('dp', 'rdw', events))
#    s.add(satUnion('(dp+rdw)', 'rfi2', events, 'ii0'))
#    s.add(satEmpty('ic0', events))
#    s.add(satUnion('ctrlisync', 'detour', events, 'ci0'))
#    s.add(satUnion('dp', 'poloc', events))
#    s.add(satUnion('(dp+poloc)', 'ctrl', events))
#    for t in threads:
#        eventsPerThread = [e for e in events if e.thread == t]
#        s.add(satComp('addr', 'po', eventsPerThread))
#        ### Recursive
#        s.add(satPowerPPO(eventsPerThread))
#    s.add(satUnion('((dp+poloc)+ctrl)', '(addr;po)', events, 'cc0'))
#
#    ### PPO for Power
#    s.add(satIntersection('RR', 'ii', events))
#    s.add(satIntersection('RW', 'ic', events))
#    s.add(satUnion('(RR&ii)', '(RW&ic)', events, 'ppoW'))
#
#    ### Thin air check
#    s.add(satUnion('ppoW', 'rfe2', events))
#    s.add(satUnion('(ppoW+rfe2)', 'fence', events, 'hbW'))
#    s.add(satAcyclic('hbW', events))
#
#    ### Prop-base
#    s.add(satComp('rfe2', 'fence', events))
#    s.add(satUnion('fence', '(rfe2;fence)', events))
#    s.add(satTransRef('hbW', events))
#    s.add(satComp('(fence+(rfe2;fence))', '(hbW)*', events, 'prop-base'))
#
#    ### Prop for Power
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
#        s.add(satTransRef('com', eventsPerLoc))
#    s.add(satTransRef('prop-base', events))
#    s.add(satComp('(com)*', '(prop-base)*', events))
#    s.add(satComp('((com)*;(prop-base)*)', 'sync', events))
#    s.add(satComp('(((com)*;(prop-base)*);sync)', '(hbW)*', events))
#    s.add(satIntersection('WW', 'prop-base', events))
#    s.add(satUnion('(WW&prop-base)', '((((com)*;(prop-base)*);sync);(hbW)*)', events, 'prop'))
#
#    ### Observation check
#    s.add(satComp('fre2', 'prop', events))
#    s.add(satComp('(fre2;prop)', '(hbW)*', events))
#    s.add(satIrref('((fre2;prop);(hbW)*)', events))
#
#    ### Propagation check
#    s.add(satUnion('ws', 'prop', events))
#    s.add(satAcyclic('(ws+prop)', events))
#
#    ### SC per location
#    s.add(satUnion('ws', 'rf2', events))
#    s.add(satUnion('(ws+rf2)', 'fr2', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ###########################
#    ### WO-PPO cycle detection
#    s.add(satComp('rfe2', 'ppoW', events))
#    s.add(satInverse('rfe2', events))
#    s.add(satComp('(rfe2;ppoW)', '(rfe2)^-1', events))
#    s.add(satMinus('((rfe2;ppoW);(rfe2)^-1)', 'id', events))
#    s.add(satComp('(((rfe2;ppoW);(rfe2)^-1)\id)', 'ws', events))
#    s.add(satFRInit(events))
#    s.add(satComp('(rfe2;ppoW)', 'frinit', events))
#    s.add(satUnion('((((rfe2;ppoW);(rfe2)^-1)\id);ws)', '((rfe2;ppoW);frinit)', events, 'cycle1'))
#    s.add(satUnion('poloc', 'ws', events, 'cycle2'))
#    s.add(Or(satCycle('cycle1', events), satCycle('cycle2', events)))
#
#    t1 = time()
#    res = s.check()
#    print res
#    t2 = time()
#    print "Encoding: %.2f" %(t1-t0)
#    print "Solving: %.2f" %(t2-t1)
#
#    return res
#
#
#def ToplasPowerTSO(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
#    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    for t in threads:
#        eventsLPerThread = [e for e in eventsL if e.thread == t]
#        s.add(satTrans('idd', eventsLPerThread))
#    s.add(satIntersection('idd^+', 'RW', events, 'data'))
#
#    ### Fences in Power
#    s.add(satEq('sync', 'ffence', events))
#    s.add(satMinus('lwsync', 'WR', events, 'lwfence'))
#    s.add(satUnion('ffence', 'lwfence', events, 'fence'))
#
#    ### Some other relations
#    s.add(satEmpty('addr', events))
#    s.add(satUnion('addr', 'data', events, 'dp'))
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
#        s.add(satCompFreRfe(eventsPerLoc))
#        s.add(satCompWseRfe(eventsPerLoc))
#    s.add(satIntersection('poloc', '(fre;rfe)', events, 'rdw'))
#    s.add(satIntersection('poloc', '(wse;rfe)', events, 'detour'))
#
#    ### Base case for the recursion
#    s.add(satUnion('dp', 'rdw', events))
#    s.add(satUnion('(dp+rdw)', 'rfi', events, 'ii0'))
#    s.add(satEmpty('ic0', events))
#    s.add(satUnion('ctrlisync', 'detour', events, 'ci0'))
#    s.add(satUnion('dp', 'poloc', events))
#    s.add(satUnion('(dp+poloc)', 'ctrl', events))
#    for t in threads:
#        eventsPerThread = [e for e in events if e.thread == t]
#        s.add(satComp('addr', 'po', eventsPerThread))
#        ### Recursive
#        s.add(satPowerPPO(eventsPerThread))
#    s.add(satUnion('((dp+poloc)+ctrl)', '(addr;po)', events, 'cc0'))
#
#    ### PPO for Power
#    s.add(satIntersection('RR', 'ii', events))
#    s.add(satIntersection('RW', 'ic', events))
#    s.add(satUnion('(RR&ii)', '(RW&ic)', events, 'ppoW'))
#
#    ### Thin air check
#    s.add(satUnion('ppoW', 'rfe', events))
#    s.add(satUnion('(ppoW+rfe)', 'fence', events, 'hbW'))
#    s.add(satAcyclic('hbW', events))
#
#    ### Prop-base
#    s.add(satCompRfeFence(events))
#    s.add(satUnion('fence', '(rfe;fence)', events))
#    s.add(satTransRef('hbW', events))
#    s.add(satComp('(fence+(rfe;fence))', '(hbW)*', events, 'prop-base'))
#
#    ### Prop for Power
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
#        s.add(satTransRef('com', eventsPerLoc))
#    s.add(satTransRef('prop-base', events))
#    s.add(satCompComProp(events))
#    s.add(satCompComPropSync(events))
#    s.add(satComp('(((com)*;(prop-base)*);sync)', '(hbW)*', events))
#    s.add(satIntersection('WW', 'prop-base', events))
#    s.add(satUnion('(WW&prop-base)', '((((com)*;(prop-base)*);sync);(hbW)*)', events, 'prop'))
#
#    ### Observation check
#    s.add(satCompFreProp(events))
#    s.add(satCompFrePropHb(events))
#    s.add(satIrref('((fre;prop);(hbW)*)', events))
#
#    ### Propagation check
#    s.add(satUnion('ws', 'prop', events))
#    s.add(satAcyclic('(ws+prop)', events))
#
#    ### SC per location
#    s.add(satUnion('ws', 'rf', events))
#    s.add(satUnion('(ws+rf)', 'fr', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ###########################
#    ### TSO with cycle detection
#    s.add(satMinus('po', 'WR', events, 'ppoS'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'fence', events))
#    s.add(satUnion('(((ws+fr)+rfe)+fence)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
#
#def ToplasPowerPSO(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
#    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    for t in threads:
#        eventsLPerThread = [e for e in eventsL if e.thread == t]
#        s.add(satTrans('idd', eventsLPerThread))
#    s.add(satIntersection('idd^+', 'RW', events, 'data'))
#
#    ### Fences in Power
#    s.add(satEq('sync', 'ffence', events))
#    s.add(satMinus('lwsync', 'WR', events, 'lwfence'))
#    s.add(satUnion('ffence', 'lwfence', events, 'fence'))
#
#    ### Some other relations
#    s.add(satEmpty('addr', events))
#    s.add(satUnion('addr', 'data', events, 'dp'))
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
#        s.add(satCompFreRfe(eventsPerLoc))
#        s.add(satCompWseRfe(eventsPerLoc))
#    s.add(satIntersection('poloc', '(fre;rfe)', events, 'rdw'))
#    s.add(satIntersection('poloc', '(wse;rfe)', events, 'detour'))
#
#    ### Base case for the recursion
#    s.add(satUnion('dp', 'rdw', events))
#    s.add(satUnion('(dp+rdw)', 'rfi', events, 'ii0'))
#    s.add(satEmpty('ic0', events))
#    s.add(satUnion('ctrlisync', 'detour', events, 'ci0'))
#    s.add(satUnion('dp', 'poloc', events))
#    s.add(satUnion('(dp+poloc)', 'ctrl', events))
#    for t in threads:
#        eventsPerThread = [e for e in events if e.thread == t]
#        s.add(satComp('addr', 'po', eventsPerThread))
#        ### Recursive
#        s.add(satPowerPPO(eventsPerThread))
#    s.add(satUnion('((dp+poloc)+ctrl)', '(addr;po)', events, 'cc0'))
#
#    ### PPO for Power
#    s.add(satIntersection('RR', 'ii', events))
#    s.add(satIntersection('RW', 'ic', events))
#    s.add(satUnion('(RR&ii)', '(RW&ic)', events, 'ppoW'))
#
#    ### Thin air check
#    s.add(satUnion('ppoW', 'rfe', events))
#    s.add(satUnion('(ppoW+rfe)', 'fence', events, 'hbW'))
#    s.add(satAcyclic('hbW', events))
#
#    ### Prop-base
#    s.add(satCompRfeFence(events))
#    s.add(satUnion('fence', '(rfe;fence)', events))
#    s.add(satTransRef('hbW', events))
#    s.add(satComp('(fence+(rfe;fence))', '(hbW)*', events, 'prop-base'))
#
#    ### Prop for Power
#    for l in locs:
#        eventsPerLoc = [e for e in events if e.loc == l]
#        s.add(satTransRef('com', eventsPerLoc))
#    s.add(satTransRef('prop-base', events))
#    s.add(satCompComProp(events))
#    s.add(satCompComPropSync(events))
#    s.add(satComp('(((com)*;(prop-base)*);sync)', '(hbW)*', events))
#    s.add(satIntersection('WW', 'prop-base', events))
#    s.add(satUnion('(WW&prop-base)', '((((com)*;(prop-base)*);sync);(hbW)*)', events, 'prop'))
#
#    ### Observation check
#    s.add(satCompFreProp(events))
#    s.add(satCompFrePropHb(events))
#    s.add(satIrref('((fre;prop);(hbW)*)', events))
#
#    ### Propagation check
#    s.add(satUnion('ws', 'prop', events))
#    s.add(satAcyclic('(ws+prop)', events))
#
#    ### SC per location
#    s.add(satUnion('ws', 'rf', events))
#    s.add(satUnion('(ws+rf)', 'fr', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ###########################
#    ### PSO with cycle detection
#    s.add(satIntersection('po', 'RM', events, 'ppoS'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'fence', events))
#    s.add(satUnion('(((ws+fr)+rfe)+fence)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
#
#
#def TSOMCA(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### New to handle RF not reading from init
#    s.add(satMinus('rf', 'IM', events, 'rf2'))
#    s.add(satMinus('rfe', 'IM', events, 'rfe2'))
#    s.add(satIntersection('id', 'RR', events, '[R]'))
#    s.add(satIntersection('id', 'WW', events, '[W]'))
#    s.add(satInverse('rf2', events))
#    s.add(satComp('(rf2)^-1', 'rf2', events))
#    s.add(satMinus('[R]', '((rf2)^-1;rf2)', events))
#    s.add(satComp('([R]\((rf2)^-1;rf2))', 'loc', events))
#    s.add(satComp('(([R]\((rf2)^-1;rf2));loc)', '[W]', events, 'frinit'))
#
#    ### SC per location
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rf', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ### TSO
#    s.add(satMinus('po', 'WR', events))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('(po\WR)', 'fence', events, 'ppo'))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'ppo', events, 'ghb'))
#    s.add(satAcyclic('ghb', events))
#
#    ###########################
#    ### WO-PPO cycle detection
#    s.add(satComp('rfe2', 'ppo', events))
#    s.add(satInverse('rfe2', events))
#    s.add(satComp('(rfe2;ppo)', '(rfe2)^-1', events))
#    s.add(satMinus('((rfe2;ppo);(rfe2)^-1)', 'id', events))
#    s.add(satComp('(((rfe2;ppo);(rfe2)^-1)\id)', 'ws', events))
##    s.add(satFRInit(events))
#    s.add(satComp('(rfe2;ppo)', 'frinit', events))
#    s.add(satUnion('((((rfe2;ppo);(rfe2)^-1)\id);ws)', '((rfe2;ppo);frinit)', events, 'cycle1'))
#    s.add(satUnion('poloc', 'ws', events, 'cycle2'))
#    s.add(Or(satCycle('cycle1', events), satCycle('cycle2', events)))
#
#    res = s.check()
#    print ' %s' %res
#
#    return res
#
#def TSOSC(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### SC per location
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rf', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ### TSO
#    s.add(satMinus('po', 'WR', events, 'ppoW'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'fence', events))
#    s.add(satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
#    s.add(satAcyclic('ghbW', events))
#
#    ###########################
#    ### SC with cycle detection
#    s.add(satEq('po', 'ppoS', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
#
#def TSOSC_Dead(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### New to handle RF not reading from init
#    s.add(satMinus('rf', 'IM', events, 'rf2'))
#    s.add(satMinus('ws', 'IM', events, 'ws2'))
#
#    ### Dead (35)
#    s.add(satDomRanIncl('ctrl', 'rf2', events))
#
#    ### Dead (36.1)
#    s.add(satImm('ws2', events))
#    s.add(satComp('imm(ws2)', 'imm(ws2)', events))
#    s.add(satInverse('ws2', events))
#    s.add(satImm('(ws2)^-1', events))
#    s.add(satComp('(imm(ws2);imm(ws2))', 'imm((ws2)^-1)', events))
#
#    ### Dead (36.2)
#    s.add(satRefClos('rf2', events))
#    s.add(satInverse('rf2', events))
#    s.add(satRefClos('(rf2)^-1', events))
#    s.add(satComp('po', '((rf2)^-1)?', events))
#    s.add(satRefClos('(po;((rf2)^-1)?)', events))
#    s.add(satComp('(rf2)?', '((po;((rf2)^-1)?))?', events))
#
#    ### Dead (36.3)
#    s.add(satIncl('((imm(ws2);imm(ws2));imm((ws2)^-1))', '((rf2)?;((po;((rf2)^-1)?))?)', events))
#
#    ### SC per location
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rf', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ### TSO
#    s.add(satMinus('po', 'WR', events, 'ppoW'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'fence', events))
#    s.add(satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
#    s.add(satAcyclic('ghbW', events))
#
#    ###########################
#    ### SC with cycle detection
#    s.add(satEq('po', 'ppoS', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
#
#def PSOSC(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### SC per location
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rf', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ### PSO
#    s.add(satIntersection('po', 'RM', events, 'ppoW'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'fence', events))
#    s.add(satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
#    s.add(satAcyclic('ghbW', events))
#
#    ###########################
#    ### SC with cycle detection
#    s.add(satEq('po', 'ppoS', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
#
#def PSOSC_Dead(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### New to handle RF not reading from init
#    s.add(satMinus('rf', 'IM', events, 'rf2'))
#    s.add(satMinus('ws', 'IM', events, 'ws2'))
#
#    ### Dead (35)
#    s.add(satDomRanIncl('ctrl', 'rf2', events))
#
#    ### Dead (36.1)
#    s.add(satImm('ws2', events))
#    s.add(satComp('imm(ws2)', 'imm(ws2)', events))
#    s.add(satInverse('ws2', events))
#    s.add(satImm('(ws2)^-1', events))
#    s.add(satComp('(imm(ws2);imm(ws2))', 'imm((ws2)^-1)', events))
#
#    ### Dead (36.2)
#    s.add(satRefClos('rf2', events))
#    s.add(satInverse('rf2', events))
#    s.add(satRefClos('(rf2)^-1', events))
#    s.add(satComp('po', '((rf2)^-1)?', events))
#    s.add(satRefClos('(po;((rf2)^-1)?)', events))
#    s.add(satComp('(rf2)?', '((po;((rf2)^-1)?))?', events))
#
#    ### Dead (36.3)
#    s.add(satIncl('((imm(ws2);imm(ws2));imm((ws2)^-1))', '((rf2)?;((po;((rf2)^-1)?))?)', events))
#
#    ### SC per location
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rf', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ### PSO
#    s.add(satIntersection('po', 'RM', events, 'ppoW'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('(ws+fr)', 'rfe', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'fence', events))
#    s.add(satUnion('(((ws+fr)+rfe)+fence)', 'ppoW', events, 'ghbW'))
#    s.add(satAcyclic('ghbW', events))
#
#    ###########################
#    ### SC with cycle detection
#    s.add(satEq('po', 'ppoS', events))
#    s.add(satUnion('((ws+fr)+rfe)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
#
#def PSOTSO(m):
#
#    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
#    barriers = [e for e in m.events() if isinstance(e, Barrier)]
#    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]
#
#    s = Solver()
#
#    s.add(encodeDomain(events, barriers, eventsL))
#    s.add(encode(m))
#
#    ### SC per location
#    s.add(satUnion('ws', 'fr', events))
#    s.add(satUnion('(ws+fr)', 'rf', events, 'com'))
#    s.add(satUnion('poloc', 'com', events))
#    s.add(satAcyclic('(poloc+com)', events))
#
#    ### PSO
#    s.add(satIntersection('po', 'RM', events, 'ppoW'))
#    s.add(satEq('mfence', 'fence', events))
#    s.add(satUnion('(ws+fr)', 'fence', events))
#    s.add(satUnion('((ws+fr)+fence)', 'rfe', events))
#    s.add(satUnion('(((ws+fr)+fence)+rfe)', 'ppoW', events, 'ghbW'))
#    s.add(satAcyclic('ghbW', events))
#
#    ### TSO
#    s.add(satMinus('po', 'WR', events, 'ppoS'))
#    s.add(satUnion('(((ws+fr)+fence)+rfe)', 'ppoS', events, 'ghbS'))
#    s.add(satCycle('ghbS', events))
#
#    res = s.check()
#
#    return res
