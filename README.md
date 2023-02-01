# ZooKeeper's TLA+ Specification

This project is about the TLA+ specifications of ZooKeeper and its core consensus protocol called *Zab (Zookeeper Atomic Broadcast)*. 



## Overview

The ZooKeeper community show great interest in developing TLA+ specification for ZooKeeper and Zab. On Apache's issue tracking system, the request of [write a TLA+ specification to verify Zab protocol](https://issues.apache.org/jira/browse/ZOOKEEPER-3615) has been raised early in 2019. 

Following the idea of TLA+'s ladder of abstractions and incremental specification, we develop three levels of specifiactions, including *protocol sepecification*, *system specification* and *test specification*.

We first develop the ***protocol specification*** that describes the Zab protocol without ambiguity. We discover several ambiguities of Zab's informal description and  fix the bugs in the protocol specification.

Considering that the ZooKeeper implementation optimizes a lot based on the Zab protocol, we then develop the ***system specification*** based on Zab's protocol specification and ZooKeeper's source code at a low cost. The system specification can serve as the super-doc of ZooKeeper (Zab-1.0) implementation.

To guide the *Model checking-driven Explorative Testing (MET)*, we develop the ***test specification*** based on the system specification and the source code. The test specification help find several deep bugs in ZooKeeper implementaion (including the latest version ZK-3.8.0 at the time of writing). 

Besides, to ensure the quality of these specifications, we also conduct model checking on them using the TLC model checkers, as well as conformance checking using our MET framework. 

We submit a [pull request](https://github.com/apache/zookeeper/pull/1690) of providing formal specifications and verifications for Zab-pre1.0 and Zab-1.0 ( corresponding to protocol specification and system specification, respectively ), and received positive feedbacks from community developers.

Recently, we are told that our specification PR is expected to be reviewed and merged [soon](https://lists.apache.org/thread/x622jkntmj81tg44n5lo4lvpx0b000d7). 



## Directories

This project is organized as follows.

* *[protocol-spec](protocol-spec)*
  * *[Zab.tla](protocol-spec/Zab.tla)* : TLA+ specification of Zab.
  * *[doc.md](protocol-spec/doc.md)* : introduction of Zab's protocol specification, as well as experience of specification and verification. 
  * *[verification-statistics.md](protocol-spec/verification-statistics.md)* : statistics of verification.
  * [*issues.md*](protocol-spec/issues.md) : issues found from  the protocol specification and the Zab informal description. 
  * *[picture](protocol-spec/picture)* : pictures of buggy trace examples.
* *[system-spec](system-spec)*
  * *[zk-3.7](system-spec/zk-3.7)*
    * *[ZkV3_7_0.tla](system-spec/zk-3.7/ZkV3_7_0.tla)* ： TLA+ specification of Zab implementation of ZooKeeper-3.7.0.
    * *[FastLeaderElection.tla](system-spec/zk-3.7/FastLeaderElection.tla)* :  TLA+ specification of the Fast Leader Election.

  * *[doc.md](system-spec/doc.md)* : introduction of ZK's system specification, quality ensurance and feedbacks from community.
  * *[conformance-checking.md](system-spec/conformance-checking.md)* : experience of conformance checking. 

* *[test-spec](test-spec)*
  * *[zk_test_v1](test-spec/zk_test_v1)*
    * *[zk_test_v1.tla](test-spec/zk_test_v1/zk_test_v1.tla)* : TLA+ specification for testing Zab implementation of ZooKeeper-3.4.10.
    * *[trace ](test-spec/zk_test_v1/trace)*: reproduced traces of bugs like [ZK-3911](https://issues.apache.org/jira/browse/ZOOKEEPER-3911), [ZK-2845](https://issues.apache.org/jira/browse/ZOOKEEPER-2845), ...

  * *[doc.md](test-spec/doc.md)* : introduction of ZK's test specification and the [Model Checking-driven Explorative Testing (MET)](https://github.com/Lingzhi-Ouyang/MET) framework. 
  * *[experiment.md](test-spec/experiment.md)* : experiment design and results.


