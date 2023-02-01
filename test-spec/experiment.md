## Experiment

### Configuration



### State Space Constraints

- 3 servers
- TimeoutThresh: 6
- TxnNum: 2
- EpochThresh: 4
- CrashThresh: 5
- PartitionThresh: 5



### Invariants to Check

- Core correctness conditions: *Integrity*, *Agreement*, *TotalOrder*, *LocalPrimaryOrder*, *GlobalPrimaryOrder*, ...
- Invariant properties:
  - Checked inside the action: *StateConsistent*, *ProposalConsistent*,*CommitConsistent*, *AckConsistent*, *MessageLegal*, ...
  - Checked after the action: *SingleLeader*, *PrefixConsistency*, *CommittedLogMonotonicity*, *ProcessConsistency*, ...



### Results

#### Invariant Violations

- 808 / 160,007 ≈ 0.5% traces violate *committedLogMonotonicity*
- 2087 / 160007 ≈ 1.3% traces violate *processConsistency*



#### Triggering of Deep Bugs

See the document of [deep-bugs.md](deep-bugs.md)
