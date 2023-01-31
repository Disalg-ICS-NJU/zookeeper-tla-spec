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

Recently, we are told that our specification PR is expected to be reviewed and merged soon (https://lists.apache.org/thread/x622jkntmj81tg44n5lo4lvpx0b000d7). 



## Directories

This project is organized as follows.

* *protocol-spec*
  * *Zab.tla & Zab.pdf* : TLA+ specification of Zab.
  * *results* : results of verification.
  * *doc-in-chinese* : document of the protocol specification and verification in Chinese. 

* system-spec
* test-spec

