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

%set domains
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

%create cost matrix
array[nodes, nodes] of var 0..1000: edgeCosts;
constraint forall (i in nbrEdges)(
  edgeCosts[from[i], to[i]] = cost[i]
  /\
  edgeCosts[to[i], from[i]] = cost[i]
);

%create path matrix
array[nodes, nodes] of var 0..1: fullPath;
constraint forall (j in 1..n_dest)(
  forall (i in nodes)(
    fullPath[i, x[i,j]] = 1
  )  
);
  
constraint forall(k in 1..n_dest)(subcircuit(x[..,k]));

var int: pathCost;
constraint pathCost = sum(i in nodes)(sum(j in nodes)(fullPath[i,j] * edgeCosts[i,j]));

solve minimize pathCost; 

output[show(destSet), "\n cost: ", show(pathCost), "\n", show(x[..,1])];
