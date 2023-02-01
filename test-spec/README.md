# ZooKeeper's Test Specification of TLA+

## Overview

The test specification is developed to guide the explorative testing of ZooKeeper. 

Taking advantage of the TLC model checking tools, we can efficiently produce traces that can serve as test cases for testing. 

The testing specification can be derived based on the system specification by tuning the abstraction levels of different aspects of contents according to the testing target and exploration strategy.

Inspired by the Interaction-Preserving Abstraction (IPA) framework, we can partition the system specification into modules, and exercise compositional checking by further refining core modules and abstracting non-core modules.

We mainly focus on Zab’s recovery logic in its SYNC phase for the following reasons. First, the SYNC logic is optimized a lot in the implementation compared to its original design, which is under full verification. Second, the SYNC logic is unstable and continously changing as the system evolves without long-term testing. What’s more, the SYNC logic is complex and error-prone according to our knowledge and years of issue reports on ZooKeeper’s issue tracking system. 



## MET

The [Model Checking-driven Explorative Testing (MET)](https://github.com/Lingzhi-Ouyang/MET) framework aims to combine the advantages of both model verification and testing.



## Experiment

### Configuration



### State Space Constraints

* 3 servers
* TimeoutThresh: 6
* TxnNum: 2
* EpochThresh: 4
* CrashThresh: 5
* PartitionThresh: 5



### Invariants to Check

* Core correctness conditions: *Integrity*, *Agreement*, *TotalOrder*, *LocalPrimaryOrder*, *GlobalPrimaryOrder*, ...

* Invariant properties: 

  * Checked inside the action: *StateConsistent*, *ProposalConsistent*,*CommitConsistent*, *AckConsistent*, *MessageLegal*, ...

  * Checked after the action: SingleLeader, *PrefixConsistency*, *CommittedLogMonotonicity*, *ProcessConsistency*, ...



### Results

#### Invariant Violations

* 808 / 160,007 ≈ 0.5%  traces violate *committedLogMonotonicity*
* 2087 / 160007 ≈ 1.3% traces violate *processConsistency*



#### Triggering of Deep Bugs

Following the Model checking-driven explorative testing (MET) framework, we have reproduced several old deep bugs and uncovered several new deep bugs in ZooKeeper. These subtle bugs will lead to critical property violations like data inconsistency or data loss. However, they are hard to be found, because the timing of the environment failures is quite subtle, and it requires more than ten steps to trigger them. Bugs triggered with our test specifications include: 

* [ZK-3911](https://issues.apache.org/jira/browse/ZOOKEEPER-3911): Data inconsistency caused by DIFF sync uncommitted log. 
  * It will cause committed logs to be lost. 
  * This bug violates *CommittedLogMonotonicity* specified in the spec [ZkV3_4_10.tla](ZkV3_4_10.tla). 
* [ZK-2845](https://issues.apache.org/jira/browse/ZOOKEEPER-2845): Data inconsistency issue due to retain database in leader election. 
  * It will cause transaction logs to be inconsistent. 
  * This bug violates *ProcessConsistency* specified in the spec [ZkV3_4_10.tla](ZkV3_4_10.tla).
* [ZK-4643](https://issues.apache.org/jira/browse/ZOOKEEPER-4643): Committed txns may be improperly truncated if follower crashes right after updating currentEpoch but before persisting txns to disk.  
  * It will cause committed logs to be lost. 
  * It is a violation of the atomicity of two actions that is guaranteed at the protocol level.
  * This issue can be triggered using the spec ?
* [ZK-4646](https://issues.apache.org/jira/browse/ZOOKEEPER-4646): Committed txns may still be lost if followers crash after replying ACK-LD but before writing txns to disk. 
  * It will cause committed logs to be lost. 
  * It is related to the asynchronous execution by multi-thread implementation. It shows that the asynchronous logging of transactions may violate the atomicity of actions. 
  * This issue can be triggered using the spec ?
* ...