# Verification Statistics 

## Experiment configuration

Our statistical results include: 

    -   diameter of the system states that have been traversed
    -   the number of states that have been traversed
    -   the time spent in the experiment

The machine configuration used in the experiment is 3.00 GHz, 6-core CPU, 16GB memory. The TLC version number is 1.7.0.


## Verification statistics of model checking 
We use two mode for verifying Zab Protocol: model-checking mode and simulation mode. We terminate model checking when cost time exceeds 24 hours.

Every TLC model contains four parameters, **N** for num of servers, **L** for maximum history length, **C** for maximum times of node crash, **P** for maximum times of network partition between two nodes.

|  Mode  |   TLC model(N, L, C, P)     |    Diameter   |   Num of states  | Time of checking(hh:mm:ss) |
| ----- | ---------------------- | ------------- | ------------------ | ------------------ |
| model-checking | (3,2,4,0)   |   27  |3,256,237,887 | > 24:00:00 |
| model-checking | (3,2,3,3)   |   24  |3,322,996,126 | > 24:00:00 |
| model-checking | (5,2,3,3)   |   16  |  693,381,547 | > 24:00:00 |
| simulation     | (3,2,4,4)   |   -   |1,472,147,440 | > 24:00:00 |
| simulation     | (3,5,5,5)   |   -   |1,139,420,778 | > 24:00:00 |
| simulation     | (5,5,5,5)   |   -   |1,358,120,544 | > 24:00:00 |
| simulation     | (3,5,0,10)  |   -   |1,463,314,104 | > 24:00:00 |
| simulation     | (3,5,10,0)  |   -   |1,211,089,513 | > 24:00:00 |

