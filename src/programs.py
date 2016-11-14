from z3 import *
from types import *
import copy
from itertools import product, combinations
from time import time
import random
import collections

numOperations = ["+", "-", "*", "/", "%", "xor"]
numComparisons = ["==", "!=", "<", "<=", ">", ">=",]
boolOperations = ["and", "or", "not"]

### Integer variable to encode that ws is a total order
def wsVar(e): return Int("ws:L%s(%s)" %(e.loc, ev(e)))

### Integer variable to encode that po is a total order
def poVar(e, arch): return Int("%s_po:T%s(%s)" %(arch, e.thread, ev(e)))

### Integer variable to encode that ghb is a partial order
def ghbVar(e): return Int("ghb(%s)" %(ev(e)))

### Integer variable to encode that uniProc is acylic
def uniProcVar(e): return Int("up(%s)" %(ev(e)))

### Bool variable to encode that two events are related under rel
def edge(rel, e1, e2, arch=""): return Bool("%s%s(%s,%s)" %(rel, arch, ev(e1), ev(e2)))

### Bool variable to encode the edges of the cycle
def cycleEdge(rel, x, y): return Bool("Cycle:%s(%s,%s)" %(rel, ev(x), ev(y)))

### Bool variable to encode the nodes (events) of the cycle
def cycleVar(x): return Bool("Cycle(%s)" %(ev(x)))

def encodeALO(l):
    """ Encodes that AT LEAST ONE element in the list can be true. """
    assert(isinstance(l, list))
    if l == []: return False
    return Or(l)

def encodeEO(l):
    """ Encodes that EXACTLY one element in the list can be true. """
    assert(isinstance(l, list))
    if l == []: return False
    encoding = False
    for i in range(len(l)):
        rest = l[:i] + l[i+1:]
        rest = map(lambda e : Not(e), rest)
        rest.append(l[i])
        encoding = Or(encoding, And(rest))
    return encoding

def getLast(x, mapping):
    """ Returns the last set value of x in mapping. """
    if not x in mapping.keys(): mapping[x] = 0
    return mapping[x]

def getFresh(x, mapping):
    """ Returns a fresh value for x and set it in mapping. """
    if not x in mapping.keys(): mapping[x] = 0
    else: mapping[x] += 1
    return mapping[x]

def mergeMaps(map1, map2):
    """ Returns a new map that merges the two inputs, i.e. for each key it returns the maximal value. """
    ### This is used to update the mapping of an if thread after each sub-thread updated its local copy of the map
    newMap = {}
    for k in map1.keys():
        if k in map2.keys(): newMap[k] = max(map1[k], map2[k])
        else: newMap[k] = map1[k]
    for k in map2.keys():
        if k in map1.keys(): newMap[k] = max(map1[k], map2[k])
        else: newMap[k] = map2[k]

    return newMap

def encodeMissingIndexes(t, indexes1, indexes2):
    ### Returns a constraint that updates the unused variables in some branches of the if thread (x_{i+1} == x_i)
    ### (see for example page 191 of the paper "Exploration of the Capabilities of Constraint Programming")
    new = True
    for k in indexes1.keys():
        k1 = getLast(k, indexes1)
        k2 = getLast(k, indexes2)
        if k1 > k2:
            if isinstance(k, Register):
                index = And(map(lambda i : Int("T%s_%s%s" %(str(t.thread), str(k), str(i+1))) == Int("T%s_%s%s" %(str(t.thread), str(k), str(i))), range(k2, k1)))
            elif isinstance(k, Location):
                index = And(map(lambda i : Int(str(k) + str(i+1)) == Int(str(k) + str(i)), range(k2, k1)))
            else: raise Exception("Type error")
            new = And(Implies(Not(Bool(repr(t.t1))), index), new)
    for k in indexes2.keys(): 
        k1 = getLast(k, indexes1)
        k2 = getLast(k, indexes2)
        if k2 > k1:
            if isinstance(k, Register):
                index = And(map(lambda i : Int("T%s_%s%s" %(str(t.thread), str(k), str(i+1))) == Int("T%s_%s%s" %(str(t.thread), str(k), str(i))), range(k1, k2)))
            elif isinstance(k, Location):
                index = And(map(lambda i : Int(str(k) + str(i+1)) == Int(str(k) + str(i)), range(k2, k1)))
            else: raise Exception("Type error")
            new = And(Implies(Not(Bool(repr(t.t2))), index), new)
    return new

### Predicate := Bool | Expression | Predicate And Predicate | Predicate Or Predicate | Not Predicate
class Predicate:

    def __init__(self, p1, op=None, p2=None):
        assert(isinstance(p1, (bool, Predicate)))
        assert(isinstance(p2, (bool, Predicate, NoneType)))
        assert(op in numComparisons if isinstance(p1, Expression) and isinstance(p2, Expression) else op in boolOperations or op == None)
        assert(p2 == None if op == "not" else True)
        assert(isinstance(p1, bool) and p2 == None if op == None else True)
        self.op = op
        self.p1 = p1
        self.p2 = p2

    def __str__(self):
        if self.p2 != None: return "%s %s %s" % (str(self.p1), self.op, str(self.p2))
        elif self.op == "not": return "%s (%s)" % (self.op, str(self.p1))
        else: return str(self.p1)

    def encode(self, mapping):
        """ Returns a constraint representing the predicate and renaming the variables to satisfy SA. """
        ### The mapping is used for the renaming
        p1 = self.p1.encode(mapping) if not isinstance(self.p1, bool) else self.p1
        p2 = self.p2.encode(mapping) if not isinstance(self.p2, (bool, NoneType)) else self.p2
        if self.op == None: return self.p1
        if self.op == "==": return p1 == p2
        elif self.op == "!=": return p1 != p2
        elif self.op == ">": return p1 > p2
        elif self.op == ">=": return p1 >= p2
        elif self.op == "<": return p1 < p2
        elif self.op == "<=": return p1 <= p2
        elif self.op == "and": return And(p1, p2)
        elif self.op == "or": return Or(p1, p2)
        elif self.op == "not": return Not(p1, p2)
        else: raise Exception("Type error in Predicate encode")

### Expression := Int | Location | Register | Expression Op Expression.
class Expression(Predicate):

    def __init__(self, v1, op=None, v2=None):
        assert(isinstance(v1, (int, Expression)))
        assert(isinstance(v2, (int, Expression, NoneType)))
        assert(op in numOperations or op == None)
        assert(isinstance(v1, int) and v2 == None if op == None else True)
        self.op = op
        self.v1 = v1
        self.v2 = v2

    def __str__(self):
        if self.op == None: return str(self.v1)
        else: return "(%s %s %s)" % (str(self.v1), self.op, str(self.v2))

    def encode(self, mapping):
        """ Returns a constraint representing the expression and renaming the variables to satisfy SA. """
        ### The mapping is used for the renaming
        v1 = self.v1.encode(mapping) if not isinstance(self.v1, int) else self.v1
        v2 = self.v2.encode(mapping) if not isinstance(self.v2, (int, NoneType)) else self.v2
        if self.op == None: return v1
        else:
             if self.op == "+": return v1 + v2
             elif self.op == "-": return v1 - v2
             elif self.op == "*": return v1 * v2
             elif self.op == "/": return v1 / v2
             elif self.op == "%": return v1 % v2
             elif self.op == "xor": return 1 if (v1 == 0 and v2 == 1) or (v1 == 1 and v2 == 0) else 0
             else: raise Exception("Type error in Expression encode")

def getRegs(exp):
#    assert(isinstance(exp, (int, Expression)))
    if isinstance(exp, int): return set()
    if isinstance(exp, Register): return set([exp])
    if isinstance(exp, Expression) and isinstance(exp.v1, int): return set()
    elif isinstance(exp, Expression): return getRegs(exp.v1).union(getRegs(exp.v2))
    elif isinstance(exp, Predicate): return getRegs(exp.p1).union(getRegs(exp.p2))
    else: raise Exception("Problem with getRegs")

class Location:

    def __init__(self, name):
        assert(type(name) is StringType)
        self.name = name

    def __repr__(self):
        return self.name

    def __str__(self):
        return self.name

    ### For unrolling the while, we need to create deep copies of the sub-thread and this might create
    ### copies of the location, therefore we override the __deepcopy__ method for this class
    def __deepcopy__(self, memo):
        return self

    ### Returns a constraint representing the location after renaming to satisfy SA. It is alwasy a fresh variable
    ### since SA get fresh ones on the left and we get fresh ones on the right to allow reading from any event
    def encode(self, mapping): return Int("%s%s" %(str(self.name), str(getFresh(self, mapping))))

class Register(Expression):

    def __init__(self, name):
        assert(type(name) is StringType)
        self.name = name
        self.thread = None

    def __repr__(self):
        return self.name

    def __str__(self):
        return self.name

    ### For unrolling the while, we need to create deep copies of the sub-thread and this might create
    ### copies of the register, therefore we override the __deepcopy__ method for this class
    def __deepcopy__(self, memo):
        return self

    ### Since registers are local per thread, we assign a thread to them to use in the renaming
    ### We do not assign the whole thread, but its pid
    def setThread(self, t):
#        assert (self.thread == None or self.thread == t.pid)
        self.thread = t.pid
        return self

    ### Returns a constraint representing the register after renaming to satisfy SA
    def encode(self, mapping):
        if self.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        return Int("T%s_%s%s" %(str(self.thread), str(self.name), str(getLast(self, mapping))))

### Thread := Event | Skip | If Predicate Thread Thread | Seq Thread Thread.
class Thread:

    ### It does not have an __init__ since the corresponding one from Load, Store, etc should be used

    def __str__(self): return "P%s" % self.pid

    def __repr__(self): return "P%s" % self.pid

    ### All the events "belong" to the "highest" thread in the sub-typing chain, i.e. they belong to the
    ### thread that is added to the multithreaded program
    ### We do not assign the whole thread, but its pid
    def setThread(self, t):
        self.thread = t.pid
        if isinstance(self, (If, Seq)):
            self.t1.setThread(t)
            self.t2.setThread(t)
#        for e in getEvents(self):
#            e.thread = self.pid
        return self

class Skip(Thread):

    def __init__(self):
        self.pid = None
        self.thread = None
        ### The conditional level is used for pretty printing
        self.condLevel = 0

    def __str__(self):
        return "%sskip" %("  "*self.condLevel)

    def incCondLevel(self):
        """ Increments its conditional level. """
        self.condLevel += 1
        return self

    def decCondLevel(self):
        """ Decrements its conditional level. """
        self.condLevel -= 1
        return self

    def setProgramsID(self, x):
        """ Sets its pid. """
        self.pid = x
        return x + 1

    def setEventsID(self, x):
        ### Since it dos not have sub-threads and it is not an event, it does nothing
        return x

    def unroll(self, bound):
        return self

    def setMapLastMod(self, mapping): return mapping

    def setCondReg(self, regs): return self

class While(Thread):

    def __init__(self, pred, t):
        assert(isinstance(pred, Predicate) and isinstance(t, Thread))
        self.pred = pred
        self.t1 = t
        self.pid = None
        ### The conditional level is used for pretty printing
        self.condLevel = 0
        self.t1.incCondLevel()
 
    def __str__(self):
        return "%sWhile (%s)\n%s" % ("  "*self.condLevel, str(self.pred), str(self.t1))

    def incCondLevel(self):
        """ Increments the conditional level of itself and its sub-threads. """
        self.condLevel += 1
        self.t1.incCondLevel()
        return self

    def decCondLevel(self):
        """ Decrements the conditional level of itself and its sub-threads. """
        self.condLevel -= 1
        self.t1.decCondLevel()
        return self

    def setProgramsID(self, x):
        """ Sets the pid of itself and its sub-threads. """
        ### Each x is different, that's why we return it and updated on the left side
        x = self.t1.setProgramsID(x)
        self.pid = x
        return x + 1

    def setEventsID(self, x):
        """ Sets the eid of its sub-threads. """
        ### Each x is different, that's why we return it and updated on the left side
        x = self.t1.setEventsID(x)
        return x

    def unroll(self, bound):
        if bound == 0:
            cLevel = self.condLevel
            self = Skip()
            ### The skip inherits the condLevel
            self.conLevel = cLevel
        else:
            t = copy.deepcopy(self.t1)
            t.decCondLevel()
            t = t.unroll(bound)
            cLevel = self.condLevel
            self = If(self.pred, Seq(t, self.unroll(bound - 1)), Skip())
            ### The if inherits the conLevel of the While
            self.condLevel = cLevel
        return self

class If(Thread):

    def __init__(self, pred, t1, t2):
        assert(isinstance(pred, Predicate) and isinstance(t1, Thread) and isinstance(t2, Thread))
        self.pred = pred
        self.t1 = t1
        self.t2 = t2
        self.pid = None
        self.thread = None
        ### The conditional level is used for pretty printing
        self.condLevel = 0
        self.t1.incCondLevel()
        self.t2.incCondLevel()

    def __str__(self):
        if isinstance(self.t2, Skip):
            return "%sif (%s)\n%s" % ("  "*self.condLevel, str(self.pred), str(self.t1))
        return "%sif (%s)\n%s\n%selse\n%s" % ("  "*self.condLevel, str(self.pred), str(self.t1), "  "*self.condLevel, str(self.t2))

    def incCondLevel(self):
        """ Increments the conditional level of itself and its sub-threads. """
        self.condLevel += 1
        self.t1.incCondLevel()
        self.t2.incCondLevel()
        return self

    def decCondLevel(self):
        """ Decrements the conditional level of itself and its sub-threads. """
        self.condLevel -= 1
        self.t1.decCondLevel()
        self.t2.decCondLevel()
        return self

    def setProgramsID(self, x):
        """ Sets the pid of itself and its sub-threads. """
        ### Each x is different, that's why we return it and updated on the left side
        x = self.t1.setProgramsID(x)
        x = self.t2.setProgramsID(x)
        self.pid = x
        return x + 1

    def setEventsID(self, x):
        """ Sets the eid of its sub-threads. """
        ### Each x is different, that's why we return it and updated on the left side
        x = self.t1.setEventsID(x)
        x = self.t2.setEventsID(x)
        return x

    def unroll(self, bound):
        self.t1 = self.t1.unroll(bound)
        self.t2 = self.t2.unroll(bound)
        return self

    def setMapLastMod(self, mapping={}):
        map1 = self.t1.setMapLastMod(copy.copy(mapping))
        map2 = self.t2.setMapLastMod(copy.copy(mapping))
        return mergeMapLastMod(map1, map2)

    def setCondReg(self, regs):
        newRegs = regs.union(getRegs(self.pred))
        self.t1.setCondReg(newRegs)
        self.t2.setCondReg(newRegs)
        return self

def mergeMapLastMod(map1, map2):
    newMap = copy.copy(map1)
    for x in map2.keys():
        if x in newMap.keys(): newMap[x] = newMap[x].union(map2[x])
        else: newMap[x] = map2[x]
    return newMap

class Seq(Thread):

    def __init__(self, t1, t2):
        assert(isinstance(t1, Thread) and isinstance(t2, Thread))
        self.t1 = t1
        self.t2 = t2
        self.pid = None
        self.thread = None
        self.condLevel = 0

    def __str__(self):
        if isinstance(self.t2, Skip):
            return str(self.t1)
        return "%s;\n%s" % (str(self.t1), str(self.t2))
    
    def incCondLevel(self):
        """ Increments the conditional level of itself and its sub-threads. """
        self.condLevel += 1
        self.t1.incCondLevel()
        self.t2.incCondLevel()
        return self

    def decCondLevel(self):
        """ Decrements the conditional level of itself and its sub-threads. """
        self.condLevel -= 1
        self.t1.decCondLevel()
        self.t2.decCondLevel()
        return self

    def setProgramsID(self, x):
        """ Sets the pid of itself and its sub-threads. """
        ### Each x is different, that's why we return it and updated on the left side
        x = self.t1.setProgramsID(x)
        x = self.t2.setProgramsID(x)
        self.pid = x
        return x + 1

    def setEventsID(self, x):
        """ Sets the eid of its sub-threads. """
        ### Each x is different, that's why we return it and updated on the left side
        x = self.t1.setEventsID(x)
        x = self.t2.setEventsID(x)
        return x

    def unroll(self, bound):
        self.t1 = self.t1.unroll(bound)
        self.t2 = self.t2.unroll(bound)
        return self

    def setMapLastMod(self, mapping={}):
        newMapping = self.t1.setMapLastMod(mapping)
        return self.t2.setMapLastMod(newMapping)

    def setCondReg(self, regs):
        self.t1.setCondReg(regs)
        self.t2.setCondReg(regs)
        return self

### Event := Local | Load | Store
class Event(Thread):

    ### It does not have an __init__ since the corresponding one from Load or Store should be used

    def incCondLevel(self):
        """ Increments its conditional level. """
        self.condLevel += 1
        return self 

    def decCondLevel(self):
        """ Decrements the conditional level of itself and its sub-threads. """
        self.condLevel -= 1
        return self

    def setProgramsID(self, x):
        """ Sets its pid. """
        self.pid = x
        return x + 1

    def setEventsID(self, x):
        """ Stes its eid. """
        self.eid = x
        return x + 1

    def unroll(self, bound):
        return self

    def setCondReg(self, regs):
        self.condReg = regs
        return self

### This is a kind of representative for the events
def ev(e):
    assert(isinstance(e, Event))
    return "E%s" %(e.eid)

class Barrier(Event):

    def __init__(self):
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0
        self.mapLastMod = {}

    def __str__(self):
        return "%sfence" %("  "*self.condLevel)

    def __repr__(self):
        return "P%s" % str(self.pid)

    def setMapLastMod(self, mapping):
        self.mapLastMod = mapping
        return self.mapLastMod

class Mfence(Barrier):

    def __init__(self):
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0

    def __str__(self):
        return "%smfence" %("  "*self.condLevel)

class Sync(Barrier):

    def __init__(self):
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0

    def __str__(self):
        return "%ssync" %("  "*self.condLevel)

class Lwsync(Barrier):

    def __init__(self):
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0

    def __str__(self):
        return "%slwsync" %("  "*self.condLevel)

class Isync(Barrier):

    def __init__(self):
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0

    def __str__(self):
        return "%sisync" %("  "*self.condLevel)

class Init(Event):

    def __init__(self, loc):
        assert(isinstance(loc, Location))
        self.loc = loc
        self.pid = None
        self.eid = None
        self.thread = None
        ### When the dataflow is encoded, we save the variable numbering for future uses, for example to encode
        ### that if a load read-from a store, then the values of the locations coincide
        self.SAloc = None
        self.mapLastMod = {}
        self.condReg = None

    def __str__(self):
        return "%s := 0" %(self.loc)

    def __repr__(self):
        return "P%s" % str(self.pid)

    def setMapLastMod(self, mapping={}):
        self.mapLastMod = mapping
        res = copy.copy(self.mapLastMod)
        res[self.loc] = set([self])
        return res

### Loads can only read from locations, any other kinf od thing (reg = Int or reg = Exp) is consider local 
class Load(Event):

    def __init__(self, reg, loc):
        assert(isinstance(reg, Register) and isinstance(loc, Location))
        self.reg = reg
        self.loc = loc
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0
        self.SAreg = None
        self.SAloc = None
        self.mapLastMod = {}
        self.condReg = None

    def __str__(self):
        return "%s%s <- %s" % ("  "*self.condLevel, str(self.reg), str(self.loc))

    def __repr__(self):
        return "E%s" % str(self.eid)

    def setMapLastMod(self, mapping={}):
        self.mapLastMod = mapping
        res = copy.copy(self.mapLastMod)
        res[self.reg] = set([self])
        return res

    def getMapLastMod(self): return self.mapLastMod

    def getLastMod():
        if self.loc in self.mapLastMod.keys(): return set([self.mapLastMod[self.loc]])
        else: raise Exception('Problem with mapLastMod')

class Local(Event):

    def __init__(self, reg, exp):
        assert(isinstance(reg, Register) and isinstance(exp, Expression))
        self.reg = reg
        self.exp = exp
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0
        self.SAreg = None
        self.SAexp = None
        self.mapLastMod = {}
        self.condReg = None

    def __str__(self):
        return "%s%s <- %s" % ("  "*self.condLevel, str(self.reg), str(self.exp))

    def __repr__(self):
        return "E%s" % str(self.eid)

    def setMapLastMod(self, mapping={}):
        self.mapLastMod = mapping
        res = copy.copy(self.mapLastMod)
        res[self.reg] = set([self])
        return res

    def getMapLastMod(self): return self.mapLastMod

    def getLastMod():
        res = []
        for r in self.exp.getRegs():
            if r in self.mapLastMod.keys(): res.append(r)
            else: raise Exception('Problem with mapLastMod')
        return set(res)

class Store(Event):

    def __init__(self, loc, reg):
        assert(isinstance(reg, Register) and isinstance(loc, Location))
        self.loc = loc
        self.reg = reg
        self.pid = None
        self.eid = None
        self.thread = None
        self.condLevel = 0
        self.SALoc = None
        self.SAreg = None
        self.mapLastMod = {}
        self.condReg = None

    def __str__(self):
        return "%s%s := %s" % ("  "*self.condLevel, str(self.loc), str(self.reg))

    def __repr__(self):
        return "E%s" % str(self.eid)

    def setMapLastMod(self, mapping):
        self.mapLastMod = mapping
        res = copy.copy(self.mapLastMod)
        res[self.loc] = set([self])
        return res

    def getMapLastMod(self): return self.mapLastMod

    def getLastMod():
        if self.reg in self.mapLastMod.keys(): return set([self.mapLastMod[self.reg]])
        else: raise Exception('Problem with mapLastMod')

def getEvents(t):
    assert(isinstance(t, Thread))
    if isinstance(t, Event): return [t]
    elif isinstance(t, Skip): return []
    elif isinstance(t, While): return getEvents(t.t1)
    elif isinstance(t, (If, Seq)): return getEvents(t.t1) + getEvents(t.t2)
    else: raise Exception ("Type error in getEvents")

def encodeCF(t):
    """ Encodes the control flow of the program. """
    assert(isinstance(t, Thread))
    if isinstance(t, Seq):
        ### If some sub-thread is active, the sequence is active
        ### If the sequence is active, both sub-threadss are active
        ### And we encode recursively for the sub-threads
        return And(Implies(Or(Bool(repr(t.t1)), Bool(repr(t.t2))), Bool(repr(t))),
                   Implies(Bool(repr(t)), And(Bool(repr(t.t1)), Bool(repr(t.t2)))),
                   encodeCF(t.t1),
                   encodeCF(t.t2))
    elif isinstance(t, If):
        ### When the if is active, exaclty one of the sub-threads is active
        ### When some sub-thread is active, then the if is active
        ### And we encode recursively for the sub-threadss
        return And(Implies(Bool(repr(t)), Xor(Bool(repr(t.t1)), Bool(repr(t.t2)))),
                   Implies(Or(Bool(repr(t.t1)), Bool(repr(t.t2))), Bool(repr(t))),
                   encodeCF(t.t1),
                   encodeCF(t.t2))
    elif isinstance(t, Event):
        ### The thread is active iff the event is active
        return Bool(repr(t)) == Bool(ev(t))
    elif isinstance(t, Skip):
        ### Skip programs do not impose things in the control flow
        return True
    else: raise Exception("Type error in encodeCF()")

def encodeDF(t, localMap):
    """ Encodes the data flow of the thread. """
    ### The localMap is used to rename variables to satisfy dymanic single assignement
    ### i.e. variables can have the same value if they belong to different branchees of an if
    ### For this we need to copy the localMap to pass to the differen sub-threads of an if
    ### and we need to merge the copies of the maps with the maximal values (this is done by mergeMaps)
    ### We need to return also the map for the merging
    ### Since one branch may have less occurences of a variable than other, we might need to encode
    ### x_{i+1} = x_i in some cases (this is done by encodeMissingIndexes). See page 191 of the paper 
    ### "Exploration of the Capabilities of Constraint Programming for Software Verification" for details

    assert(isinstance(t, Thread))
    if isinstance(t, Init):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### Since init events are always active, the value of the location is 0
        loc = Int("%s%s" %(str(t.loc), str(getFresh(t.loc, localMap))))
        enc = loc == 0
        t.SAloc = loc
    elif isinstance(t, Store):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### If the event is active, the value of the location and the register coincide
        reg = Int("T%s_%s%s" %(str(t.thread), str(t.reg), str(getLast(t.reg, localMap))))
        loc = Int("%s%s" %(str(t.loc), str(getFresh(t.loc, localMap))))
        enc = Implies(Bool(ev(t)), loc == reg)
        t.SAreg = reg
        t.SAloc = loc
    elif isinstance(t, Local):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### If the event is active, the value of the register and the expression coincide
        exp = t.exp.encode(localMap)
        reg = Int("T%s_%s%s" %(str(t.thread), str(t.reg), str(getFresh(t.reg, localMap))))
        enc = Implies(Bool(ev(t)), reg == exp)
        t.SAreg = reg
        t.SAexp = exp
    elif isinstance(t, Load):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### If the event is active, the value of the register and the location coincide
        loc = t.loc.encode(localMap)
        reg = Int("T%s_%s%s" %(str(t.thread), str(t.reg), str(getFresh(t.reg, localMap))))
        enc = Implies(Bool(ev(t)), reg == loc)
        t.SAreg = reg
        t.SAloc = loc
    elif isinstance(t, Seq):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### The data flow of a sequences is the conjuction of the dataflow of its sub-threads
        (enc1, localMap) = encodeDF(t.t1, localMap)
        (enc2, localMap) = encodeDF(t.t2, localMap)
        enc =  And(enc1, enc2)
    elif isinstance(t, If):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### If sub-thread t1 is active, then the predicate is true, if t2 is active then the predicate is false
        enc = And(Implies(Bool(repr(t.t1)), t.pred.encode(localMap)), Implies(Bool(repr(t.t2)), Not(t.pred.encode(localMap))))
        ### For the recursive calls we make copies of the map
        indexes1 = copy.copy(localMap)
        (enc1, indexes1) = encodeDF(t.t1, indexes1)
        indexes2 = copy.copy(localMap)
        (enc2, indexes2) = encodeDF(t.t2, indexes2)
        enc = And(enc, enc1, enc2)
        ### We encode any missing variable in some branch
        enc = And(encodeMissingIndexes(t, indexes1, indexes2), enc)
        ### And finally merge the local copies of the maps
        localMap = mergeMaps(indexes1, indexes2)
    elif isinstance(t, Skip):
        if t.thread == None: raise Exception("Threads should be assigned to events and registers before calling encode()")
        ### Skip programs do not contribute to the data flow
        enc = True
    elif isinstance(t, Barrier):
        enc = True
    elif isinstance(t, While): raise Exception("The program should be unrolled before calling to encode")
    else: raise Exception("Type error in encodeDF()")
    return (enc, localMap)

class Program:

    def __init__(self, name=''):
        self.threads = list()
        self.name = name

    def __str__(self):
        return "\n".join("\nThread %d\n%s" % (i, str(x)) for i,x in enumerate(self.threads) if not isinstance(x, Init))

    def add(self, t):
        assert(isinstance(t, Thread))
        self.threads.append(t)
        return self

    def setID(self):
        pid, eid = 1, 1
        for t in self.threads:
            pid = t.setProgramsID(pid)
            eid = t.setEventsID(eid)
        return self

    def initialize(self, bound=1):
        #### add initialization of regs
        """ It initializes a multi-threaded program by setting locations to 0, adding IDs to threads and events and setting threads for events and registers. """
        unrolledThreads = list()
        for t in self.threads:
            newT = t.unroll(bound)
            unrolledThreads.append(newT)
        self.threads = unrolledThreads
        ### It adds events initializing the locations to 0
        locs = set([x.loc for x in filter(lambda e: isinstance(e, (Load, Store)), self.events())])
        for l in locs:
            self.add(Init(l))
        ### And then sets the IDs
        self.setID()
        for t in self.threads:
            t.setThread(t)
            t.setMapLastMod({})
            t.setCondReg(set())
            regs = set([x.reg for x in filter(lambda e: isinstance(e, (Local, Load, Store)), getEvents(t))])
            for r in regs: r.setThread(t)
        return self

    def events(self): return sum(map(getEvents, self.threads), [])

    def initEvents(self): return filter(lambda e: isinstance(e, Init), self.events())

    def storeEvents(self): return filter(lambda e: isinstance(e, Store), self.events())

    def loadEvents(self): return filter(lambda e: isinstance(e, Load), self.events())

    def encodeDF_RF(self):
        """ Encodes the fact that if a load read from store, then the values of the locations coincide. """
        enc = True
        for r in self.loadEvents():
            writeSameLoc = filter(lambda w: w.loc == r.loc, self.storeEvents() + self.initEvents())
            sameValues = And(map(lambda w: Implies(edge("rf", w, r), r.SAloc == w.SAloc), writeSameLoc))
            enc = And(enc, sameValues)
        return enc

#    def encodeMM(self):
#        """ Encodes all the relations and the cycle for checking robusteness between SC and TSO. """
#
#        ### Local events are not considered observables
#        obsEvents = filter(lambda e: isinstance(e, (Load, Store, Init, Barrier)), self.events()) 
#
#        ### We assign integers to write and init events to encode that WS is a total order
#        wsOrd = And(map(lambda w: Implies(Bool(ev(w)), wsVar(w) >= 2), self.storeEvents()))
#        ### Init events are the first in the order
#        wsInit = And(map(lambda i: wsVar(i) == 1, self.initEvents()))
#        ### We assign integers to observable events to encode that PO is a total order in both SC and TSO
#        poSCOrd = And(map(lambda e: Implies(Bool(ev(e)), poVar(e, "SC") >= 1), obsEvents))
#        poTSOOrd = And(map(lambda e: Implies(Bool(ev(e)), poVar(e, "TSO") >= 1), obsEvents))
#        ### We assign integers to observable events to encode that GHB is a partial order
#        ghbOrd = And(map(lambda e: Implies(Bool(ev(e)), ghbVar(e) >= 1), obsEvents))
#        ### We assign integers to observable events to encode that uniProc is acyclic
#        uniProcOrd = And(map(lambda e: Implies(Bool(ev(e)), uniProcVar(e) >= 1), obsEvents))
#
#        enc = And(wsOrd, wsInit, poSCOrd, poTSOOrd, ghbOrd, uniProcOrd)
#
#        ### We encode all the possible relation between observale events
#        for e1, e2 in product(obsEvents, obsEvents):
#            ### Events can be related only if they are both active
#            for rel in ["ws", "rf", "fr", "po", "ab"]:
#                enc = And(enc, Implies(edge(rel, e1, e2), And(Bool(ev(e1)), Bool(ev(e2)))))
#
#            ## Restrics the domain of WS
#            if not isinstance(e1, (Store, Init)) or not isinstance(e2, (Store, Init)) or e1.loc != e2.loc or e1 == e2:
#                enc = And(enc, Not(edge("ws", e1, e2)))
#            ## WS is a total order between ACTIVE writes for each location
#            if isinstance(e1, (Store, Init)) and isinstance(e2, (Store, Init)) and e1.loc == e2.loc and e1 != e2:
#                enc = And(enc, Implies(And(Bool(ev(e1)), Bool(ev(e2))), (Or(edge("ws", e1, e2), edge("ws", e2, e1)))))
#                enc = And(enc, Implies(edge("ws", e1, e2), wsVar(e1) < wsVar(e2)))
#                enc = And(enc, wsVar(e1) != wsVar(e2))
#            ## WS is global
#            enc = And(enc, Implies(edge("ws", e1, e2), ghbVar(e1) < ghbVar(e2)))
#            ## WS is part of uniproc
#            enc = And(enc, Implies(edge("ws", e1, e2), uniProcVar(e1) < uniProcVar(e2)))
#
#            ## Restrics the domain of RF
#            if not isinstance(e1, (Store, Init)) or not isinstance(e2, Load) or e1.loc != e2.loc:
#                enc = And(enc, Not(edge("rf", e1, e2)))
#            ## Read are either external or internal
#            enc = And(enc, Implies(edge("rf", e1, e2), Or(edge("rfe", e1, e2), edge("rfi", e1, e2))))
#            ## Restrics the domain of RFI
#            if e1.thread != e2.thread:
#                enc = And(enc, Not(edge("rfi", e1, e2)))
#            ## RFI is a subset of RF
#            enc = And(enc, Implies(edge("rfi", e1, e2), edge("rf", e1, e2)))
#            ## Restrics the domain of RFE
#            if e1.thread == e2.thread:
#                enc = And(enc, Not(edge("rfe", e1, e2)))
#            ## RFE is a subset of RF
#            enc = And(enc, Implies(edge("rfe", e1, e2), edge("rf", e1, e2)))
#            ## RFE is global in TSO
#            enc = And(enc, Implies(edge("rfe", e1, e2), ghbVar(e1) < ghbVar(e2)))
#            ## RF is part of uniproc
#            enc = And(enc, Implies(edge("rf", e1, e2), uniProcVar(e1) < uniProcVar(e2)))
#
#            ## Restrics the domain of FR
#            if not isinstance(e1, Load) or not isinstance(e2, (Store, Init)) or e1.loc != e2.loc:
#                enc = And(enc, Not(edge("fr", e1, e2)))
#            ## FR is global
#            enc = And(enc, Implies(edge("fr", e1, e2), ghbVar(e1) < ghbVar(e2)))
#            ## FR is part of uniproc
#            enc = And(enc, Implies(edge("fr", e1, e2), uniProcVar(e1) < uniProcVar(e2)))
#
#            ## Restrics the domain of PO
#            ## This PO is preserved program order (PPO)
#            if e1.thread != e2.thread or isinstance(e1, Init) or isinstance(e2, Init):
#                enc = And(enc, Not(edge("po", e1, e2)))
#            ## PO is a total order for each thread between ACTIVE events
#            if e1 != e2 and e1.thread == e2.thread and not isinstance(e1, Init) and not isinstance(e2, Init):
#                enc = And(enc, Implies(And(Bool(ev(e1)), Bool(ev(e2))), Or(edge("po", e1, e2), edge("po", e2, e1))))
#                enc = And(enc, Implies(edge("po", e1, e2,"SC"), poVar(e1,"SC") < poVar(e2,"SC")))
#                enc = And(enc, Implies(edge("po", e1, e2,"TSO"), poVar(e1,"TSO") < poVar(e2,"TSO")))
#                enc = And(enc, poVar(e1,"SC") != poVar(e2,"SC"))
#                enc = And(enc, poVar(e1,"TSO") != poVar(e2,"TSO"))
#            ## Restrics the domain of POLOC
#            if not isinstance(e1, Barrier) and not isinstance(e2, Barrier) and e1.loc != e2.loc:
#                enc = And(enc, Not(edge("poloc", e1, e2)))
#            ## POLOC is a subset of PO
#            enc = And(enc, Implies(edge("poloc", e1, e2), edge("po", e1, e2)))
#            ## PO-SC is a subset of PO
#            enc = And(enc, Implies(edge("po", e1, e2,"SC"), edge("po", e1, e2)))
#            ## PO-TSO is a subset of PO
#            enc = And(enc, Implies(edge("po", e1, e2,"TSO"), edge("po", e1, e2)))
#            ## PO-TSO is global in TSO
#            enc = And(enc, Implies(edge("po", e1, e2,"TSO"), ghbVar(e1) < ghbVar(e2)))
#            ## POLOC is part of uniproc
#            enc = And(enc, Implies(edge("poloc", e1, e2), uniProcVar(e1) < uniProcVar(e2)))
#
#            ## Restricts the domain of AB
#            if e1.thread != e2.thread or (e1.thread == e2.thread and e1.eid > e2.eid):
#                enc = And(enc, Not(edge("ab", e1, e2)))
#            ## AB is global
#            enc = And(enc, Implies(edge("ab", e1, e2), ghbVar(e1) < ghbVar(e2)))
# 
#        locs = set([x.loc for x in filter(lambda e: isinstance(e, (Load, Store)), self.events())])
#
#        ## Each ACTIVE read event RF exaclty one write
#        for l in locs:
#            writesLoc = filter(lambda e : e.loc == l, self.storeEvents() + self.initEvents())
#            readsLoc = filter(lambda e : e.loc == l, self.loadEvents())
#            for er in readsLoc:
#                target = []
#                for ew in writesLoc:
#                    target.append(edge("rf", ew, er))
#                enc = And(enc, Implies(Bool(repr(er)), encodeEO(target)))
#
#        ## WS and FR implies FR
#        for l in locs:
#            writesLoc = filter(lambda e : e.loc == l, self.storeEvents() + self.initEvents())
#            readsLoc = filter(lambda e : e.loc == l, self.loadEvents())
#            for er in readsLoc:
#                for ew1, ew2 in product(writesLoc, writesLoc):
#                        enc = And(enc, Implies(And(edge("rf", ew2, er), edge("ws", ew2, ew1)), edge("fr", er, ew1)))
#
#        ## Constrains coming from PO
#        for t in self.threads:
#            eventsProc = filter(lambda e : e.thread == t.pid, obsEvents)
#            for e1 in eventsProc:
#                for e2 in eventsProc:
#                    if e1.eid < e2.eid:
#                        assert(not isinstance(e1, Init) and not isinstance(e2, Init))
#                        ## PO respects instructions order in SC for ACTIVE events
#                        enc = And(enc, Implies(And(Bool(ev(e1)), Bool(ev(e2))), edge("po", e1, e2,"SC")))
#                        if isinstance(e1, Load) or (isinstance(e1, Store) and isinstance(e2, Store)):
#                            ## TSO cannot reorder RM or WW pairs of ACTIVE events
#                            enc = And(enc, Implies(And(Bool(ev(e1)), Bool(ev(e2))),edge("po", e1, e2,"TSO")))
#                        if not isinstance(e1, Barrier) and not isinstance(e2, Barrier) and e1.loc == e2.loc:
#                            ## Uniprocessor check for ACTIVE events
#                            enc = And(enc, Implies(And(Bool(ev(e1)), Bool(ev(e2))),edge("poloc", e1, e2)))
#
#        ## Constraints from the barriers
#        for t in self.threads:
#            eventsProc = filter(lambda e : e.thread == t.pid, obsEvents)
#            for e1 in eventsProc:
#                for e2 in eventsProc:
#                    if (isinstance(e1, Barrier) or isinstance(e2, Barrier)) and e1.eid < e2.eid:
#                        ## Non-comulative barriers
#                        enc = And(enc, Implies((And(Bool(ev(e1)), Bool(ev(e2)))), edge("ab", e1, e2)))
#
#        ## We guess the events and arcs of the cycle
#        for e1 in obsEvents:
#            target, source = [], []
#            for e2 in obsEvents:
#                if e1 != e2:
#                    for rel in ["ws","rf","fr","po"]:
#                        target.append(cycleEdge(rel, e2, e1))
#                        source.append(cycleEdge(rel, e1, e2))
#                        ## If an edge belong to the cycle, then the is an arc for some relation
#                        if rel == "po":
#                            enc = And(enc, Implies(cycleEdge(rel, e1, e2), edge(rel, e1, e2, "SC")))
#                        else:
#                            enc = And(enc, Implies(cycleEdge(rel, e1, e2), edge(rel, e1, e2)))
#                        ## If an edge belong to the cycle, then both nodes belong too
#                        enc = And(enc, Implies(cycleEdge(rel, e1, e2), And(cycleVar(e1), cycleVar(e2))))
#            ## If an event belong to the cycle, then there is an incoming and an outgoing edge in the cycle
#            enc = And(enc, Implies(cycleVar(e1), encodeALO(target)))
#            enc = And(enc, Implies(cycleVar(e1), encodeALO(source)))
#        ## There should be at least one event in the cycle
#        enc = And(enc, Or(map(lambda e : cycleVar(e), obsEvents)))
#
#        return enc

def encode(p):
    assert(isinstance(p, Program))
    ### This is the global mapping used for renaming the variables
    indexes = {}
    ### DF encodes the relations between variables in different threads
    DF = True
    for t in p.threads:
        (enc, indexes) = encodeDF(t, indexes)
        DF = And(DF, enc)
    ### We encode control flow, dataflow within and between threads, the memory model and the fact that
    ### the "highest" threads are active
    return And(And([encodeCF(t) for t in p.threads]),
               DF, p.encodeDF_RF(), #p.encodeMM(),
               And([Bool(repr(t)) for t in  p.threads]))

def randomProg(locs, regs, thrds, inst):

    locsPool = []
    for x in locs:
        locsPool.append(Location(x))

    regsPool = []
    for x in regs:
        regsPool.append(Register(x))

    usedRegsPool = {}
    for i in range(thrds):
        usedRegsPool[i] = []

    dic = {}
    for t in range(thrds):
        dic[t] = None

    for i in range(inst):
	if i < thrds: proc = i
	else: proc = random.randrange(0, thrds)
        if usedRegsPool[proc] != []:
            weighted_choices = [('W', 4), ('R', 3), ('L', 2), ('B', 1)]
        else:
            weighted_choices = [('R', 3), ('L', 3)]
        population = [val for val, cnt in weighted_choices for i in range(cnt)]
        op = random.choice(population)
        loc = random.choice(locsPool)
        reg = random.choice(regsPool)
	if op == "B": e = Mfence()
        if op == "SF": e = Sync()
        if op == "WF": e = Lwsync()
        elif op == "W": e = Store(loc, random.choice(usedRegsPool[proc]))
        elif op == "R": e = Load(reg, loc)
        elif op == "L": e = Local(reg, Expression(random.choice([1,2,3,4,5])))
        if dic[proc] == None:
            dic[proc] = Local(reg, Expression(random.choice([1,2,3,4,5])))
            usedRegsPool[proc].append(reg)
        else: dic[proc] = Seq(dic[proc], e)

    pr = Program()
    for d in dic.keys():
        pr.add(dic[d])

    return pr

def exportLitmus(m, name, satSolution):
    events = m.events()
    locs = set([x.loc for x in filter(lambda e: isinstance(e, (Load, Store, Init)), m.events())])

    procDic = collections.defaultdict(dict)
    regsDic = collections.defaultdict(dict)
    for t in m.threads:
        procDic[t.pid] = collections.defaultdict(dict)
        regsDic[t.pid] = set()
    for e in events:
        if isinstance(e, Init): continue
        elif isinstance(e, Sync):
                procDic[e.thread][e.eid] = "sync"
        elif isinstance(e, Lwsync):
                procDic[e.thread][e.eid] = "lwsync"
        elif isinstance(e, Mfence):
		procDic[e.thread][e.eid] = "MFENCE"
	elif isinstance(e, Load):
            procDic[e.thread][e.eid] = "MOV %s,[%s]" % (e.reg.name, e.loc.name)
            regsDic[e.thread].add(e.reg)
        elif isinstance(e, Store):
	    procDic[e.thread][e.eid] = "MOV [%s],%s" % (e.loc.name, e.reg.name)
            regsDic[e.thread].add(e.reg)
	if isinstance(e, Local):
	    procDic[e.thread][e.eid] = "MOV %s,$%s" % (e.reg.name, str(e.exp))
            (regsDic[e.thread]).add(e.reg)

    count = 0
    regs = []
    for t in regsDic.keys():
        for r in regsDic[t]:
            regs.append((count, r))
        count += 1

    litmus = "X86 " + name + "-" + satSolution + "\n"
    litmus += "{ \n"
    for l in locs:
        litmus += l.name + "=0; "
    litmus += "\n}\n "
    for pid, p in enumerate(filter(lambda e: not isinstance(e, Init), m.threads)): 
        if p == m.threads[0]:
            litmus += "P" + str(pid) + "\t\t"
        else:
            litmus += "| P" + str(pid) + "\t\t"
    litmus += ";\n"
    for i in range(len(filter(lambda e : not isinstance(e, Init), events))):
        for t in filter(lambda e: not isinstance(e, Init), m.threads):
            if t == m.threads[0]:
                if procDic[t.pid][i+1] == "MFENCE":
                    litmus += " " + procDic[t.pid][i+1] + "\t\t"
                elif procDic[t.pid][i+1] != {}:
                    litmus += " " + procDic[t.pid][i+1] + "\t"
                else:
                    litmus += "\t\t"
            else:
                if procDic[t.pid][i+1] != {}:
                    litmus += "| " + procDic[t.pid][i+1] + "\t"
                else:
                    litmus += "| \t\t"
        litmus += ";\n"
    writeLocs = "\nlocations ["
    for l in locs:
        writeLocs += '%s;' %str(l)
    litmus += '%s]\n' %writeLocs        
#    writeRegs = "exists (%s:%s=0" %(regs[0][0], regs[0][1])
#    for r in regs[1:]:
#        writeRegs += "/\ %s:%s=0" %(r[0], r[1])
#    litmus += '%s)\n' %writeRegs

    return litmus

