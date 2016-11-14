# PLDI-2017
The Porthos tool implementing the results of the submitted article **"Portability Analysis for Axiomatic Memory Models"**
========

To run the litmus tests in the /Litmus folder run: 

```./porthos.py -i \<input> -s \<source> -t \<target>```

where \<source> and \<target> must be one of sc, tso, pso, rmo, alpha, power, cav10

To run the mutual exclusion algorithms benchmakrs run:

``````
./testMutual.py
