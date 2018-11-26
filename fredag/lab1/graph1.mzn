int: graph_size = 3;
int: start = 1;

int: n_edges = 3;
array [1..n_edges] of int: from = [1,2,3];
array [1..n_edges] of int: to =   [2,3,1];
array [1..n_edges] of int: cost = [1,1,2];

int: n_dests = 1;
array [1..n_dests] of int: d = [3];

var set of 1..n_edges: solution;

array [1..graph_size] of var 0..1: reachable;

constraint forall (i in 1..graph_size) (reachable[i] = 0); %priority(2)

constraint reachable[start] = 1;
constraint forall (i in 1..n_edges) (if (reachable[from[i]]==1 /\ i in solution) then (reachable[to[i]] == 1) else (0=0) endif);

constraint forall (i in 1..n_dests) (reachable[i]==1);

solve minimize sum (i in solution) (cost[i]);

