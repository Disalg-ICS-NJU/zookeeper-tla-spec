## Experiment

### Overview

Our experiments are conducted with the assistance of  the tool [tlc-cmd](https://github.com/tangruize/tlc-cmd). The configuration file can be processed by the script [tlcwrapper.py](https://github.com/tangruize/tlc-cmd/blob/master/tlcwrapper.py) in [tlc-cmd](https://github.com/tangruize/tlc-cmd), and the trace data can be generated with [tlcwrapper.py](https://github.com/tangruize/tlc-cmd/blob/master/tlcwrapper.py) and [trace_reader.py](https://github.com/tangruize/tlc-cmd/blob/master/trace_reader.py). 



### Invariants to Check

- Core correctness conditions: *Integrity*, *Agreement*, *TotalOrder*, *LocalPrimaryOrder*, *GlobalPrimaryOrder*, ...
- Invariant properties:
  - Checked inside the action: *StateConsistent*, *ProposalConsistent*,*CommitConsistent*, *AckConsistent*, *MessageLegal*, ...
  - Checked after the action: *SingleLeader*, *PrefixConsistency*, *CommittedLogMonotonicity (monotonicRead)* , *ProcessConsistency*, *LeaderLogCompleteness*, *CommittedLogDurability*, ...



### Results

#### Triggering of Deep Bugs

Exposed bugs can be found in [deep-bugs.md](deep-bugs.md).

Invariant violation results of the bugs can be found in *[verification-statistics.md](verification-statistics.md)*. 



###### Probabilities of Invariant Violations

With the following state space constraints for the spec  [zk_test_v1.tla](zk_test_v1/zk_test_v1.tla) :

- 3 servers
- TimeoutThresh: 6
- TxnNum: 2
- EpochThresh: 4
- CrashThresh: 5
- PartitionThresh: 5

we obtained the following statistics of invariant violations:

- 808 / 160,007 ≈ 0.5% traces violate *committedLogMonotonicity*
- 2087 / 160007 ≈ 1.3% traces violate *processConsistency*



