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

array[nodes] of var 0..1: shortestPath; %If edge is part of shortest path, akta dubbletter???

constraint forall(i in 1..n_edges)(edges[from[i],to[i]] = cost[i] /\ edges[to[i],from[i]] = cost[i]); 

%constraint totCost;

%var int: pathCost = sum(i in nodes) (cost[i] * x[i]);% x is shortestPath?

%forall(i in 1..n) ( sum(k in 1..num_edges where E[k,2] = i) (x[k]) + (if i = s then 1 else 0 endif) = sum(k in 1..num_edges where E[k,1] = i) (x[k]) + (if i = t then 1 else 0 endif) );

output [show(graph_size), "\n", show(n_dest), "\n", show(edges[1])];
