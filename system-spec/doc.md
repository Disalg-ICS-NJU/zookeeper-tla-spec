# ZooKeeper's System Specification of TLA+

## Overview

ZooKeeper's system specification of TLA+ focuses on the implementation of the Zookeeper Atomic Broadcast(ZAB) consensus protocol (or, [ZAB1.0](https://cwiki.apache.org/confluence/display/ZOOKEEPER/Zab1.0)). 

As is shown by the informal description of [ZAB1.0](https://cwiki.apache.org/confluence/display/ZOOKEEPER/Zab1.0), the implementation of ZAB that used in ZooKeeper production differs a lot from its original design.

We make this system specification to grasp the core logic of the ZAB's implementation especially. 

The [sysetm specification](zk-3.7/ZkV3_7_0.tla) written in TLA+ is precise without ambiguity, and testable with existed tools like the TLC model checker. (We have done a certain scale of model checking to verify its correctness!) 

The system specification can serve as the super-doc supplementing detailed system documentation for the ZooKeeper developers. It can evolve incrementally without high cost as the system develops over time, continually ensuring correctness for both the design and the implementation.

We have also made a formal [specification](zk-3.7/FastLeaderElection.tla) for Fast Leader Election in Zab since ZAB 1.0 depends on FLE to complete the election phase.

If you have any question or find any problem of the specification, please contact us.



## Quality Ensurance

The system specification serving as a super-doc is supposed to describe the core logic of implementation precisely.

Model checking is not sufficient to guarantee the quality of a system specification as there may still exist some critical gaps between the specification and the implementation.

We conduct [conformance checking](conformance-checking.md) to deal with this problem. 



## Feedbacks from Community

We submit a [PR](https://github.com/apache/zookeeper/pull/1690) of providing formal specification and verification for Zab-pre1.0 and Zab-1.0 ( corresponding to protocol specification and system specification, respectively ).

This PR aims at fulfilling the request of [write a TLA+ specification to verify Zab protocol](https://issues.apache.org/jira/browse/ZOOKEEPER-3615) raised in 2019.

As the conversation on the [PR](https://github.com/apache/zookeeper/pull/1690) link desplays, the specifications have received a lot of warm discussions and positive feedbacks from ZooKeeper committee and community developers. 

These feedbacks guide us to continuously adjust and improve the specification to an appropriate abstraction level. 

Recently, we are told that our specification PR is expected to be reviewed and merged soon (https://lists.apache.org/thread/x622jkntmj81tg44n5lo4lvpx0b000d7). 

