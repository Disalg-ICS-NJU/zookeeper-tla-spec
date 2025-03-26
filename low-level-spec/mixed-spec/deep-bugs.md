# Triggering of Deep Bugs

With the mixed-grained specification we have exposed several deep bugs in ZooKeeper 3.4.10 efficiently. These subtle bugs will lead to critical property violations like data inconsistency or data loss. However, they are hard to be found, because the timing of the environment failures is quite subtle, and it requires more than ten steps to trigger them. 

Following is the overview of some triggered bugs. Detailed description and analysis of the bugs can be found on [ZooKeeper's issue tracking system](https://issues.apache.org/jira/projects/ZOOKEEPER/issues). 

We expose deep bugs like

* [ZK-3911](https://issues.apache.org/jira/browse/ZOOKEEPER-3911):  Data inconsistency caused by DIFF sync uncommitted log.
- It will cause committed logs to be lost.
  
- This bug violates *monotonicRead* and can be triggered with the spec [mixed_v1.tla](mixed_v1/mixed_v1.tla).

- [ZK-2845](https://issues.apache.org/jira/browse/ZOOKEEPER-2845): Data inconsistency issue due to retain database in leader election.
  - It will cause transaction logs to be inconsistent.
  - This bug violates *processConsistency* and can be triggered with the spec [mixed_v1.tla](mixed_v1/mixed_v1.tla).
- ...
