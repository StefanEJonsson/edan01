%https://github.com/hakank/hakank/blob/master/minizinc/spp.mzn
%https://github.com/hakank/hakank/blob/master/minizinc/all_paths_graph.mzn
%include "global.mzn";
%include "jacop.mzn";

int: graph_size;
int: start;
int: n_dest;
array[1..n_dest] of int: dest;
int: n_edges;

set of int: nbrEdges = 1..n_edges;
set of int: nbrPaths = 1..2*n_edges;

array[nbrEdges] of int: from;
array[nbrEdges] of int: to;
array[nbrEdges] of int: cost;

set of int: nodes = 1..graph_size;

var int: totCost;

%array[nodes, nodes] of var int: edges;

array[nbrPaths] of var 0..1: shortestPath; %If edge is part of shortest path, akta dubbletter???

%constraint forall(i in nbrEdges)(edges[from[i],to[i]] = cost[i] /\ edges[to[i],from[i]] = cost[i]);

array[nbrPaths, 1..2] of var int: edges;

constraint 
forall(i in nbrEdges)(
  edges[i,1] = from[i] /\ 
  edges[i+n_edges,1] = to[i] /\
  edges[i,2] = to[i] /\ 
  edges[i+n_edges,2] = from[i]);

constraint 
forall(i in nodes) (
  if i in dest then
    sum(k in nbrPaths where edges[k,2] = i) (shortestPath[k])
    >=
    1
  else if i = start then
    1
    <=
    sum(k in nbrPaths where edges[k,1] = i) (shortestPath[k]));
  else
    sum(k in nbrPaths where edges[k,2] = i) (shortestPath[k])
    <=
    sum(k in nbrPaths where edges[k,1] = i) (shortestPath[k]));

var int: pathCost = sum(i in nbrEdges) (cost[i] * shortestPath[i]+ cost[i]*shortestPath[i+n_edges]);% x is shortestPath?

solve minimize pathCost;

output [show(graph_size), "\n", show(n_dest), "\n", show(pathCost), "\n", show(edges)];
