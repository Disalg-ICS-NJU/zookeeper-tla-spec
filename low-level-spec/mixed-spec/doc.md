# ZooKeeper's mixed-grained specification of TLA+

## Overview

The mixed-grained specification is developed to cope with the model-code gaps as well as accelerate the verification of target modules in ZooKeeper. It can be derived by composing multi-grained specifications with different granularities for different modules.

Here we mainly focus on the log replication logic (especially the SYNC phase) in ZooKeeper for the following reasons. First, the SYNC logic is optimized a lot in the implementation compared to its original design in Zab, which is lack of sufficient verification. Second, the log replication logic is critical to ensure the core properties of Zab; however, it is unstable and keeps continously changing as the system evolves without long-term testing. What’s more, the  log replication logic is complex and error-prone according to our knowledge on ZooKeeper and years of issue reports on ZooKeeper’s issue tracking system. 


