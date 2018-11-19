%https://github.com/hakank/hakank/blob/master/minizinc/spp.mzn
%https://github.com/hakank/hakank/blob/master/minizinc/all_paths_graph.mzn
%include "global.mzn";
%include "jacop.mzn";

int: graph_size;
int: start;
int: n_dest;
array[1..n_dest] of int: dest;
int: n_edges;
array[1..n_edges] of int: from;
array[1..n_edges] of int: to;
array[1..n_edges] of int: cost;

var int: totCost;

set of int: nodes = 1..graph_size;

array[nodes, nodes] of var int: edges;

array[nodes, nodes] of var 0..1: shortestPath; %If edge is part of shortest path, akta dubbletter???

constraint forall(i in 1..n_edges)(edges[from[i],to[i]] = cost[i] /\ edges[to[i],from[i]] = cost[i]); 

%constraint totCost;

%var int: pathCost = sum(i in ) (c[i] * x[i]);


output [show(graph_size), "\n", show(n_dest), "\n", show(edges[1])];
