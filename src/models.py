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

def PowerInconsistent(m):
    events = [e for e in m.events() if isinstance(e, (Load, Store, Init))]
    barriers = [e for e in m.events() if isinstance(e, Barrier)]
    eventsL = [e for e in m.events() if not isinstance(e, Barrier)]

    locs = list(set([e.loc for e in events if not isinstance(e, Barrier)]))
    threads = list(set([e.thread for e in events if not isinstance(e, Init)]))

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

    if dead:
        print 'Checking portability from SC to Power with dead executions'
    else:
        print 'Checking portability from SC to Power'

    s = Solver()
    s.add(PowerConsistent(m))
    s.add(ScInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return

def PowerTSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from TSO to Power with dead executions'
    else:
        print 'Checking portability from TSO to Power'

    s = Solver()
    s.add(PowerConsistent(m))
    s.add(TsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def PowerPSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from PSO to Power with dead executions'
    else:
        print 'Checking portability from PSO to Power'

    s = Solver()
    s.add(PowerConsistent(m))
    s.add(PsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def PowerRMO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from RMO to Power with dead executions'
    else:
        print 'Checking portability from RMO to Power'

    s = Solver()
    s.add(PowerConsistent(m))
    s.add(RmoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def PowerAlpha(m, dead=False, write=False):

    if dead:
        print 'Checking portability from Alpha to Power with dead executions'
    else:
        print 'Checking portability from Alpha to Power'

    s = Solver()
    s.add(PowerConsistent(m))
    s.add(AlphaInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def PowerCAV(m, dead=False, write=False):

    if dead:
        print 'Checking portability from CAV10 to Power with dead executions'
    else:
        print 'Checking portability from CAV10 to Power'

    s = Solver()
    s.add(PowerConsistent(m))
    s.add(CavInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def CAVPower(m, dead=False, write=False):

    if dead:
        print 'Checking portability from Power to CAV10 with dead executions'
    else:
        print 'Checking portability from Power to CAV10'

    s = Solver()
    s.add(CavConsistent(m))
    s.add(PowerInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def AlphaSC(m, dead=False, write=False):

    if dead:
        print 'Checking portability from SC to Alpha with dead executions'
    else:
        print 'Checking portability from SC to Alpha'

    s = Solver()
    s.add(AlphaConsistent(m))
    s.add(ScInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def AlphaTSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from TSO to Alpha with dead executions'
    else:
        print 'Checking portability from TSO to Alpha'

    s = Solver()
    s.add(AlphaConsistent(m))
    s.add(TsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'
            
    return


def AlphaPSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from PSO to Alpha with dead executions'
    else:
        print 'Checking portability from PSO to Alpha'

    s = Solver()
    s.add(AlphaConsistent(m))
    s.add(PsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def AlphaRMO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from RMO to Alpha with dead executions'
    else:
        print 'Checking portability from RMO to Alpha'

    s = Solver()
    s.add(AlphaConsistent(m))
    s.add(RmoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def RMOSC(m, dead=False, write=False):

    if dead:
        print 'Checking portability from SC to RMO with dead executions'
    else:
        print 'Checking portability from SC to RMO'

    s = Solver()
    s.add(RmoConsistent(m))
    s.add(ScInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def RMOTSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from TSO to RMO with dead executions'
    else:
        print 'Checking portability from TSO to RMO'

    s = Solver()
    s.add(RmoConsistent(m))
    s.add(TsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def RMOPSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from PSO to RMO with dead executions'
    else:
        print 'Checking portability from PSO to RMO'

    s = Solver()
    s.add(RmoConsistent(m))
    s.add(PsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def RMOAlpha(m, dead=False, write=False):

    if dead:
        print 'Checking portability from Alpha to RMO with dead executions'
    else:
        print 'Checking portability from Alpha to RMO'

    s = Solver()
    s.add(RmoConsistent(m))
    s.add(AlphaInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def PSOSC(m, dead=False, write=False):

    if dead:
        print 'Checking portability from SC to PSO with dead executions'
    else:
        print 'Checking portability from SC to PSO'

    s = Solver()
    s.add(PsoConsistent(m))
    s.add(ScInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def PSOTSO(m, dead=False, write=False):

    if dead:
        print 'Checking portability from TSO to PSO with dead executions'
    else:
        print 'Checking portability from TSO to PSO'

    s = Solver()
    s.add(PsoConsistent(m))
    s.add(TsoInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return


def TSOSC(m, dead=False, write=False):

    if dead:
        print 'Checking portability from SC to TSO with dead executions'
    else:
        print 'Checking portability from SC to TSO'

    s = Solver()
    s.add(TsoConsistent(m))
    s.add(ScInconsistent(m))
    if dead:
        s.add(Dead(m))

    res = s.check()

    if res == sat:
        print '\tThe program is not portable'
    else:
        print '\tThe program is portable'

    return res