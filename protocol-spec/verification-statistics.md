# Verification Statistics 
## Experiment configuration

Our statistical results include: 

    -   diameter of the system states that have been traversed
    -   the number of states that have been traversed
    -   the time spent in the experiment

The machine configuration used in the experiment is 3.00 GHz, 6-core CPU, 16GB memory. The TLC version number is 1.7.0.

## State space constraints in model checking

Due to the state space explosion in model checking and the complex actions of Zab protocol, as well as unlimited number of rounds and unlimited length of history, it is impossible to traverse all states. We try to let models tap into larger state space. See CONSTANT *Parameters* for details.  

In addition to this, we also use techniques of state space reduction to compress the model's state space. Which is:

-   Focusing on the key logic of the protocol
    -   Manual labeling of each modules empirically
-   Discover the equivalence between states
    -   When the event acts on multiple nodes, and there exists a subset that each node in the subset has the same status, we let these nodes ordered if the event is performed
-   Discover the independence between events
    -   When two events are independent of each other, and the execution order does not affect the behavior of subsequent events, we can only save one scenario

## Verification statistics of model checking 
We use two mode for verifying Zab Protocol: model-checking mode and simulation mode. We terminate model checking when cost time exceeds 24 hours.

For invariant properties checked in model checking, see invariants in *[doc.md](doc.md)*.

Every TLC model contains four parameters, **N** for num of servers, **L** for maximum history length, **T** for maximum times of timeout, **R** for maximum times of node restart.


|  Mode  |   TLC model(N, L, T, R)     |    Diameter   |   Num of states  | Time of checking(hh:mm:ss) |
| ----- | ---------------------- | ------------- | ------------------ | ------------------ |
| model-checking | (2,2,2,0)   |   38  |       19,980 | 00:00:03 |
| model-checking | (2,2,0,2)   |   38  |       25,959 | 00:00:04 |
| model-checking | (2,2,1,1)   |   38  |       26,865 | 00:00:04 |
| model-checking | (2,3,2,2)   |   60  |   10,370,967 | 00:06:58 |
| model-checking | (3,2,1,0)   |   43  |      610,035 | 00:00:28 |
| model-checking | (3,2,0,1)   |   50  |    1,902,139 | 00:02:36 |
| model-checking | (3,2,2,0)   |   54  |   26,126,204 | 00:17:07 |
| model-checking | (3,2,1,1)   |   61  |   84,543,312 | 01:00:18 |
| model-checking | (3,2,0,2)   |   68  |  245,606,642 | 03:41:23 |
| model-checking | (3,2,2,1)   |   50  |1,721,643,089 | > 24:00:00 |
| model-checking | (3,2,1,2)   |   46  |1,825,094,679 | > 24:00:00 |
| simulation     | (3,3,3,3)   |   -   |1,194,558,650 | > 24:00:00 |
| model-checking | (4,2,1,0)   |   64  |   21,393,294 | 00:23:29 |
| model-checking | (4,2,0,1)   |   71  |   79,475,010 | 01:37:31 |
| model-checking | (4,2,2,0)   |   57  |1,599,588,210 | > 24:00:00 |
| simulation     | (5,3,2,2)   |   -   |  817,181,422 | > 24:00:00 |
| simulation     | (5,2,3,3)   |   -   |1,044,870,264 | > 24:00:00 |

## Issues

Besides, we have found several issues related to the ambiguous description of the Zab protocol. Details can be found at [issues.md](issues.md).
