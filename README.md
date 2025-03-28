# ZooKeeper's TLA+ Specification

This project is about the development and evaluations of TLA+ specifications of ZooKeeper and its core consensus protocol called *Zab (Zookeeper Atomic Broadcast)*. The specifications help us discover several [ambiguities](high-level-spec/issues.md) of Zab's informal description and some [deep bugs](low-level-spec/mixed-spec/deep-bugs.md) in multiple versions of ZooKeeper (including the latest version 3.8.0 at the time of writing). 

More details can be found on the [arXiv](https://arxiv.org/abs/2409.14301). The formal specifications have been merged to the [Apache ZooKeeper project](https://github.com/apache/zookeeper). 



## Overview

The ZooKeeper community show great interest in developing TLA+ specification for ZooKeeper and Zab. On Apache's issue tracking system, the request of [write a TLA+ specification to verify Zab protocol](https://issues.apache.org/jira/browse/ZOOKEEPER-3615) has been raised early in 2019. 

Following the idea of TLA+'s ladder of abstractions and incremental specification, we develop two levels of specifiactions, namely *high-level sepecification* and *low-level specification*. 
* The ***high-level specification***, or ***protocol-level specification***, describes the high-level logic of the protocol design. It is the precise design of the system, and the implementation is expected to conform to this high-level design.
* The ***low-level specification***, or ***implementation-level specification***, describes the target logic of the code implementation. The ultimate goal of the low-level specification is to faithfully reflect the code implementation. Especially when the code implementation is buggy, the low-level specification should precisely reflect the buggy implementation. Thus, the bugs can be unearthed by the verification of the low-level specification. 

As for the ZooKeeper project, we first develop the high-level *protocol specification* that describes the Zab protocol without ambiguity. We discover several [ambiguities](high-level-spec/issues.md) of Zab's informal description and fix the bugs in the protocol specification.

Considering that the ZooKeeper implementation optimizes a lot based on the Zab protocol, we then develop the implementation-level specification,  named *system specification*, based on Zab's protocol specification and ZooKeeper's source code at a low cost. The system specification can serve as the super-doc of ZooKeeper (Zab-1.0) implementation.

To cope with the model-code gaps and alleviate state space explosion, we further develop ***multi-grained specifications*** based on the system specification and the source code, and compose the specifications with different granularities into ***mixed-grained specifications***. The mixed-grained specifications help find several deep bugs (see *[deep-bugs.md](low-level-spec/mixed-spec/deep-bugs.md)*) in ZooKeeper implementaion (including version 3.4.10, and 3.9.1, the latest version at the time of writing). 

Besides, to ensure the quality of these specifications, we also conduct model checking on them using the TLC model checkers, as well as conformance checking using our [REMIX](https://github.com/Lingzhi-Ouyang/Remix) framework. 

We submit a [pull request](https://github.com/apache/zookeeper/pull/1690) of providing formal specifications and verifications for Zab-pre1.0 and Zab-1.0 ( corresponding to protocol specification and system specification, respectively), and received positive feedbacks from community developers. The formal specifications have been merged to the [Apache ZooKeeper project](https://github.com/apache/zookeeper/tree/master/zookeeper-specifications). 



## Directories

This project is organized as follows.

#### *[high-level-spec](high-level-spec)*

* *[Zab.tla](protocol-spec/Zab.tla)* : TLA+ specification of Zab.
* *[doc.md](protocol-spec/doc.md)* : introduction of Zab's protocol specification, as well as practices of specification and verification. 
* *[verification-statistics.md](protocol-spec/verification-statistics.md)* : statistics of verification.
* [*issues.md*](protocol-spec/issues.md) : issues found from  the protocol specification and the Zab informal description. 
* *[pic](protocol-spec/pic)* : pictures of buggy trace examples.

#### *[low-level-spec](low-level-spec)*

* *[zk-3.7](low-level-spec/zk-3.7)*

  * *[ZkV3_7_0.tla](low-level-spec/zk-3.7/ZkV3_7_0.tla)* ： TLA+ specification of Zab implementation of ZooKeeper-3.7.0.
  * *[FastLeaderElection.tla](low-level-spec/zk-3.7/FastLeaderElection.tla)* :  TLA+ specification of the Fast Leader Election.
  * *[doc.md](low-level-spec/zk-3.7/doc.md)* : introduction of ZK's system specification, quality ensurance and feedbacks from community.
  * *[conformance-checking.md](low-level-spec/zk-3.7/conformance-checking.md)* : experience of conformance checking. 
  * *[verification-statistics.md](low-level-spec/zk-3.7/verification-statistics.md)* : statistics of verification.
* *[mixed-spec](low-level-spec/mixed-spec)*
    * *[mixed_v1](low-level-spec/mixed-spec/mixed_v1)*
        * *[mixed_v1.tla](low-level-spec/mixed-spec/mixed_v1/mixed_v1.tla)* : TLA+ specification v1 for model checking the implementation of ZooKeeper-3.4.10.
        * *[Zab-simulate.ini](low-level-spec/mixed-spec/mixed_v1/Zab-simulate.ini)* : TLC configuration file for *[mixed_v1.tla](low-level-spec/mixed-spec/mixed_v1/mixed_v1.tla)*.
        * *[trace ](low-level-spec/mixed-spec/mixed_v1/trace)*: reproduced traces of bugs like [ZK-3911](https://issues.apache.org/jira/browse/ZOOKEEPER-3911), [ZK-2845](https://issues.apache.org/jira/browse/ZOOKEEPER-2845), ...
    * *[doc.md](low-level-spec/mixed-spec/doc.md)* : introduction of ZK's mixed-grained specification. 

    * *[experiment.md](low-level-spec/mixed-spec/experiment.md)* : experiment design and results.

    * *[deep-bugs.md](low-level-spec/mixed-spec/deep-bugs.md)* : list of triggered deep bugs.

    * *[verification-statistics.md](low-level-spec/mixed-spec/verification-statistics.md)* : statistics of verification.
