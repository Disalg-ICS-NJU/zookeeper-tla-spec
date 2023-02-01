# ZooKeeper's Test Specification of TLA+

## Overview

The test specification is developed to guide the explorative testing of ZooKeeper. 

Taking advantage of the TLC model checking tools, we can efficiently produce traces that can serve as test cases for testing. 

The testing specification can be derived based on the system specification by tuning the abstraction levels of different aspects of contents according to the testing target and exploration strategy.

Inspired by the Interaction-Preserving Abstraction (IPA) framework, we can partition the system specification into modules, and exercise compositional checking by further refining core modules and abstracting non-core modules.

We mainly focus on Zab’s recovery logic in its SYNC phase for the following reasons. First, the SYNC logic is optimized a lot in the implementation compared to its original design, which is under full verification. Second, the SYNC logic is unstable and continously changing as the system evolves without long-term testing. What’s more, the SYNC logic is complex and error-prone according to our knowledge and years of issue reports on ZooKeeper’s issue tracking system. 



## MET

The [Model Checking-driven Explorative Testing (MET)](https://github.com/Lingzhi-Ouyang/MET) framework aims to combine the advantages of both model verification and testing. 

Experiment details and results can be found [here](experiment.md).

