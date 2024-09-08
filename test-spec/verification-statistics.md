# Verification Statistics 
## Experiment configuration

Our statistical results include: 

    -   diameter of the system states that have been traversed
    -   the number of states that have been traversed
    -   the time spent in the experiment

The machine configuration used in the experiment is 3.00 GHz, 6-core CPU, 16GB memory. The TLC version number is 1.7.0.

## State space constraints in model checking

Due to the state space explosion in model checking and the complex actions of Zab protocol, as well as unlimited number of rounds and unlimited length of history, it is impossible to traverse all states. We try to let models can tap into larger state space. See CONSTANT *Parameters* for details.  

In addition to this, we also use techniques of efficient exploration strategies for the model's state space. Which is:

-   Focusing on the key logic of the protocol
    -   Manual labeling of each modules empirically
-   Discover the equivalence between states
    -   When the event acts on multiple nodes, and there exists a subset that each node in the subset has the same status, we let these nodes ordered if the event is performed
-   Discover the independence between events
    -   When two events are independent of each other, and the execution order does not affect the behavior of subsequent events, we can only save one scenario
-   Limitations of key actions
    -   After investigation, we find that most of the bugs can be triggered after several epoches and several environmental error injections
-   Heuristic Exploration Strategies
    -   We distinguish some actions into "meaningful" actions and "meaningless" actions in specific scenarios, and cut off the execution of meaningless actions

## Verification statistics of model checking 
We use two mode for verifying Zab Protocol: model-checking mode and simulation mode. We terminate model checking when cost time exceeds 24 hours.

For invariant properties checked in model checking, besides invariants defined in protocol-spec, we define four invariants in test spec: 

    -   ProcessConsistency: Client will not read a stale value
    -   MonotonicRead: When Follower completes log recovery, the Follower log is the prefix substring of the Leader log
    -   LeaderLogCompleteness: Leader contains all committed log entries in old epoches
    -   CommittedLogDurability: Committed log entries will not be truncated or overwritten


Every TLC model contains four parameters, **N** for num of servers, **L** for maximum history length, **C** for maximum times of node crash, **P** for maximum times of network partition between two nodes.

In model checking below, we set **N** as 3, **L** as 2, **C** as 4, **P** as 4.

We use model-checking mode and simulation mode to explore every bugs mentioned. And each line of results contains:
**time spent in current mck** | **number of states** | **state depth that triggers violation** | **invariant violation**

### zk_test_v1
> Config: 3 servers, 2 txn num, 4 crashes, 4 partitions
- ZK-2845: 
    -   Model-checking mode
        -   00:00:12 ｜ 6,347  ｜ 10 ｜ aaInv.processConsistency = FALSE
        -   00:00:18 ｜ 17,146 ｜ 11 ｜ daInv.proposalConsistent = FALSE

    -   Simulation mode
        -   00:00:03 | 32,142 | 20 | daInv.proposalConsistent = FALSE
        -   00:00:02 | 29,560 | 23 | aaInv.processConsistency = FALSE

- ZK-3911:
    -   Model-checking mode
        -   00:00:42 ｜ 286,286   | 14 | aaInv.leaderLogCompleteness = FALSE
        -   00:13:13 ｜ 8,677,945 | 18 | aaInv.monotonicRead = FALSE

    -   Simulation mode
        -   00:01:29 ｜ 544,820 | 25 | aaInv.leaderLogCompleteness = FALSE
        -   00:01:35 ｜ 626,002 | 39 | aaInv.monotonicRead = FALSE
