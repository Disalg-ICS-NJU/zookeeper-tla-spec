# Result of Verification
> Our verification of Zab using model checking is in progress, and we have obtained part of data set.  
> We show our result in this doc and the doc is currently not complete. 

## Experiment configuration

Our statistical results include: diameter of the system states that have been traversed, the number of states that have been traversed, the number of different states that have been discovered, and the time spent in the experiment.

The machine configuration used in the experiment is 2.40 GHz, 10-core CPU, 64GB memory. The TLC version number is 1.7.0.

## State space constraints in model checking

Due to the state space explosion in model checking and the complex actions of Zab protocol, as well as unlimited number of rounds and unlimited length of history, it is impossible to traverse all states.  
We try to let models can tap into larger state space. See CONSTANT *Parameters* for details.

## Verification results of model checking  
|  Mode  |     TLC model         |    Diameter   |     num of states  | time of checking(hh:mm:ss) |
| ----- | ---------------------- | ------------- | ------------------ | ------------------ |
| BFS   | (2 servers,3 rounds,2 transactions)    |     59   |  7758091583 |  17:28:17|
| Simulation | (2 servers,3 rounds,2 transactions)   |   -|  6412825222| 17:07:20  |
| BFS   | (3 servers,2 rounds,2 transactions)    |     19   |  4275801206 |  09:40:08|
| Simulation | (3 servers,2 rounds,2 transactions)   |   -|  10899460942| 20:15:11  |
| BFS   | (3 servers,2 rounds,3 transactions)   |    22    |  8740566213  | 17:49:09 |
| Simulation | (3 servers,2 rounds,3 transactions)  |  -    | 9639135842  |   20:10:00 |
| BFS    |  (3 servers,3 rounds,2 transactions)    |    21    | 7079744342    |14:17:45 |
| Simulation | (3 servers,3 rounds,2 transactions)    |  -  |  6254964039   | 15:08:42 |
| BFS    |  (4 servers,3 rounds,2 transactions)    |    16    | 5634112480  |15:42:09 |
| Simulation | (4 servers,3 rounds,2 transactions)    |  -  |  3883461291   | 15:52:03 |

## Verification results with parameters (count of servers, MaxTotalRestartNum, MaxElectionNum, MaxTransactionNum)
|  Mode  |     TLC model         |    Diameter   |     num of states  | time of checking(hh:mm:ss) |
| ----- | ---------------------- | ------------- | ------------------ | ------------------ |
| BFS   | (2,2,3,2,termination) |     55   |  10772649   |  00:02:21|
| BFS   | (3,1,1,2)             |     45   |  9602018536 |  31:01:57|

