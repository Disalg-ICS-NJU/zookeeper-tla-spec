# ZooKeeper's System Specification of TLA+

## Overview

ZooKeeper's system specification of TLA+ focuses on the implementation of the Zookeeper Atomic Broadcast(ZAB) consensus protocol (or, [ZAB1.0](https://cwiki.apache.org/confluence/display/ZOOKEEPER/Zab1.0)). 

As is shown by the informal description of [ZAB1.0](https://cwiki.apache.org/confluence/display/ZOOKEEPER/Zab1.0), the implementation of ZAB that used in ZooKeeper production differs a lot from its original design.

We make this system specification to grasp the core logic of the ZAB's implementation especially. 

The [sysetm specification](ZabWithFLEAndSYNC.tla) written in TLA+ is precise without ambiguity, and testable with existed tools like the TLC model checker. (We have done a certain scale of model checking to verify its correctness!) 

The system specification can serve as the super-doc supplementing detailed system documentation for the ZooKeeper developers. It can evolve incrementally without high cost as the system develops over time, continually ensuring correctness for both the design and the implementation.

We have also made a formal [specification](FastLeaderElection.tla) for Fast Leader Election in Zab since ZAB 1.0 depends on FLE to complete the election phase.

If you have any question or find any problem of the specification, please contact us.



## Feedbacks of Community

The ZooKeeper community show great interest in developing TLA+ specification for ZooKeeper and Zab.

On Apache's issue tracking system, the request of [write a TLA+ specification to verify Zab protocol](https://issues.apache.org/jira/browse/ZOOKEEPER-3615) has been raised early in 2019. 

We submit a [PR](https://github.com/apache/zookeeper/pull/1690) of providing formal specification and verification for Zab-pre1.0 and Zab-1.0 ( corresponding to protocol specification and system specification, respectively ).

As the conversation on the [PR](https://github.com/apache/zookeeper/pull/1690) link desplays, the specification receives a lot of warm discussions and positive feedbacks from ZooKeeper's designers and developers. 

Their advice like ”implement the minimum required”, ”keep things simpler” and ”reduce the state space” guided us to continuously adjust and improve the specification to an appropriate abstraction level. 

Recently, we are told that our specification PR is expected to be reviewed and merged soon (https://lists.apache.org/thread/x622jkntmj81tg44n5lo4lvpx0b000d7). 





