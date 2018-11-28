include "log2.dzn";
include "globals.mzn";

int: graph_size;
int: start;
int: n_dest;
array[1..n_dest] of int: dest;
int: n_edges;

set of int: nbrEdges = 1..n_edges;
set of int: nbrPaths = 1..2*n_edges;
set of int: nodes = 1..graph_size;

set of nodes: destSet = {dest[i] | i in 1..n_dest};

array[nbrEdges] of int: from;
array[nbrEdges] of int: to;
array[nbrEdges] of int: cost;

array[nodes, 1..n_dest] of var nodes: x;
constraint forall (i in nodes)(
  forall (k in 1..n_dest)(
    if i = dest[k] then
      x[i,k] = start
    else
      x[i,k] in {to[j] | j in nbrEdges where from[j] = i}
        union {from[j] | j in nbrEdges where to[j] = i}
        union if i != start then {i} else {} endif
    endif)
);

array[nbrEdges, 1..n_dest] var of 0..1: shortestPath;  
var of int: pathCost;

constraint forall (i in nodes)(
  forall (k in 1..n_dest)(
    if x[i,k] != i then
      forall (j in nbrEdges)(
        if from[j] = i /\ to[j] = x[i] then
          shortestPath[j,k] = 1;
        elseif to[j] = i /\ from[j] = x[i] then
          shortestPath[j,k] = 1;
        else 
          shortestPath[j,k] = 0;
        endif
    %element constraint
    )
  )
  );
  
constraint forall(k in 1..n_dest)(subcircuit(x[..,k]));

output ["x: ", show(x[..,1]), "\n   ", show(x[..,2]), "\n", show(destSet)];
