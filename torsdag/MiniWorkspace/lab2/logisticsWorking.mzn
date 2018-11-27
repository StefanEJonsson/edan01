include "log3.dzn";
include "globals.mzn";
%include "jacop.mzn";

int: graph_size;
int: start;
int: n_dest;
array[1..n_dest] of int: dest;
int: n_edges;
array[nbrEdges] of int: from;
array[nbrEdges] of int: to;
array[nbrEdges] of int: cost;

set of int: nbrEdges = 1..n_edges;
set of int: nbrPaths = 1..2*n_edges;
set of int: nodes = 1..graph_size;
set of nodes: destSet = {dest[i] | i in 1..n_dest};

array[nbrPaths] of var 0..1: shortestPath; %If edge is part of shortest path
array[nbrPaths, 1..2] of var int: edges;

%gör om till array comprehension?
constraint forall(i in nbrEdges)(
  edges[i,1] = from[i] /\ 
  edges[i+n_edges,1] = to[i] /\
  edges[i,2] = to[i] /\ 
  edges[i+n_edges,2] = from[i]
  );

constraint forall(i in nodes)( %circuit and subcircuit???
  if i = start then
    1 <=
    sum(k in nbrPaths where edges[k,1] = i) (shortestPath[k])
  else if i in destSet then
  %else if i = dest[1] \/ i = dest[2] then   % Use n_dest instead
    sum(k in nbrPaths where edges[k,2] = i) (shortestPath[k])
    = 1
  else
    (if sum(k in nbrPaths where edges[k,2] = i) (shortestPath[k]) > 0 then 
    1 <=
    sum(k in nbrPaths where edges[k,1] = i) (shortestPath[k]) else
    0 =
    sum(k in nbrPaths where edges[k,1] = i) (shortestPath[k]) endif)
  endif endif
  );
  
constraint forall(i in nbrEdges)( %make sure double paths don't exist
  shortestPath[i]*shortestPath[i+n_edges] != 1
  );

var int: pathCost = sum(i in nbrEdges) (cost[i]*shortestPath[i]+ cost[i]*shortestPath[i+n_edges]);

solve minimize pathCost;

%%Print the path:
%var opt set of nbrPaths: pathIndices = {i | i in nbrPaths where shortestPath[i] = 1};

output ["pathCost: ", show(pathCost), "\nshortestPath: ", show(shortestPath), "\nedges:\n", show(edges[..,1]), "\n",show(edges[..,2]), "\ndestSet: ", show(destSet)];
