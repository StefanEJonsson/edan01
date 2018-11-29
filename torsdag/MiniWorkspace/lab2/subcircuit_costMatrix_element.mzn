include "globals.mzn";
include "log1.dzn";

int: graph_size;
int: start;
int: n_dest;
array[1..n_dest] of int: dest;
int: n_edges;

set of int: nbrEdges = 1..n_edges;
set of int: nbrDests = 1..n_dest;
set of int: nodes = 1..graph_size;

set of nodes: destSet = {dest[i] | i in 1..n_dest};

array[nbrEdges] of int: from;
array[nbrEdges] of int: to;
array[nbrEdges] of int: cost;

array[nodes, nbrDests] of var nodes: x;

%set domains
constraint forall (i in nodes)(
  forall (k in nbrDests)(
    if i = dest[k] then
      x[i,k] = start
    else
      x[i,k] in {to[j] | j in nbrEdges where from[j] = i}
        union {from[j] | j in nbrEdges where to[j] = i}
        union if i != start then {i} else {} endif
    endif)
);


%create cost matrix
array[nodes, nodes] of var 0..1000: edgeCosts;
constraint forall (i in nbrEdges)(
  edgeCosts[from[i], to[i]] = cost[i]
  /\
  edgeCosts[to[i], from[i]] = cost[i]
);

%connects the cost of each edge to choosing a node
array[nodes] of var int: nodeCost;
constraint forall(i in nodes)(
  forall(k in nbrDests)(
    element(x[i,k], edgeCosts[i,..], nodeCost[x[i,k]])
  )
);

  
constraint forall(k in nbrDests)(subcircuit(x[..,k]));

var int: pathCost;
constraint pathCost = sum(i in nodes)(nodeCost[i]);

solve minimize pathCost; 

%n_dest = 1:
output[show(destSet), "\n cost: ", show(pathCost), "\n", show(x[..,1])];
%n_dest = 2:
%output[show(destSet), "\n cost: ", show(pathCost), "\n", show(x[..,1]), "\n", show(x[..,2])];
%n_dest = 3:
%output[show(destSet), "\n cost: ", show(pathCost), "\n", show(x[..,1]), "\n", show(x[..,2]), "\n", show(x[..,3])];
