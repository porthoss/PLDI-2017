#PLDI-2017

The Porthos tool implementing the results of the article **"Portability Analysis for Axiomatic Memory Models"**.

===

To run the litmus tests in the /Litmus folder run: 

```
./porthos.py -i <input> -s <source> -t <target>
```

where \<source> and \<target> must be one of the following MCMs: 
- sc
- tso
- pso
- rmo
- alpha
- power
- cav10

To run the mutual exclusion algorithms benchmarks run:

```
./testMutual.py
```
===

Note that Porthos uses Microsoft's Z3 SMT solver, which is not free for commercial use. Please see src/z3/LICENSE.txt for further information.
