#!/usr/bin/python

import sys, getopt
from programs import *
from myparser import *
from models import *
from z3 import sat, unsat

def main(argv):

    inputfile = None
    source = None
    target = None
    dead = False
    try:
        opts, args = getopt.getopt(argv,"i:s:t:d")
    except getopt.GetoptError:
        sys.exit(2)
    for opt, arg in opts:
        if opt == "-i":
            inputfile = arg
	elif opt == "-s":
            source = arg
        elif opt == "-t":
            target = arg
        elif opt == "-d":
            dead = True
    if inputfile == None:
	raise Exception("No input file loaded")
    if not (inputfile.endswith('.litmus')):
        raise Exception('Input is not a .litmus file')
    if not (source in ["sc", "tso", "pso", "rmo", "alpha", "power", "cav10"]):
        raise Exception('Source model is not valid. Select between sc, tso, pso, rmo, alpha, power, cav10')
    if not (target in ["tso", "pso", "rmo", "alpha", "power", "cav10"]):
        raise Exception('Target model is not valid. Select between tso, pso, rmo, alpha, power, cav10')

    litmus = parseLitmus(inputfile)

    if dead:
        print 'Checking portability from %s to %s with dead executions' %(source, target)
    else:
        print 'Checking portability from %s to %s' %(source, target)

    if source == "sc" and target == "tso":
        sol = TSOSC(litmus, dead)
    elif source == "sc" and target == "pso":
        sol = PSOSC(litmus, dead)
    elif source == "sc" and target == "rmo":
        sol = RMOSC(litmus, dead)
    elif source == "sc" and target == "alpha":
        sol = AlphaSC(litmus, dead)
    elif source == "sc" and target == "power":
        sol = PowerSC(litmus, dead)

    elif source == "tso" and target == "pso":
        sol = PSOTSO(litmus, dead)
    elif source == "tso" and target == "rmo":
        sol = RMOTSO(litmus, dead)
    elif source == "tso" and target == "alpha":
        sol = AlphaTSO(litmus, dead)
    elif source == "tso" and target == "power":
        sol = PowerTSO(litmus, dead)

    elif source == "pso" and target == "rmo":
        sol = RMOPSO(litmus, dead)
    elif source == "pso" and target == "alpha":
        sol = AlphaPSO(litmus, dead)
    elif source == "pso" and target == "power":
        sol = PowerPSO(litmus, dead)

    elif source == "rmo" and target == "alpha":
        sol = AlphaRMO(litmus, dead)
    elif source == "rmo" and target == "power":
        sol = PowerRMO(litmus, dead)

    elif source == "alpha" and target == "rmo":
        sol = RMOAlpha(litmus, dead)
    elif source == "alpha" and target == "power":
        sol = PowerAlpha(litmus, dead)

    elif source == "cav10" and target == "power":
        sol = PowerCAV(litmus, dead)
    elif source == "power" and target == "cav10":
        sol = CAVPower(litmus, dead)

    else:
        print 'The model combination is not allowed. Plase selet one combination from the paper.'
        return

    if sol == sat:
        print 'The program is not portable'
    else:
        print 'The program is portable'

    return

if __name__ == "__main__":
    main(sys.argv[1:])
