include "globals.mzn";

int: indirect_n_edges = 2*7;
array [1..indirect_n_edges, 1..2] of int: edges = [|1,2|1,3|2,3|2,4|3,5|4,5|4,6|2,1|3,1|3,2|4,2|5,3|5,4|6,4|];
%array [1..indirect_n_edges, 1..2] = [(from[i] | to[i]]
array [1..indirect_n_edges] of int: cost =  [ 4,  2,  5,  10, 3,  4, 11, 4,  2,  5,  10, 3,  4,  11];

var int: tot_cost;
array [1..indirect_n_edges] of var 0..1000000: out_flow;

constraint network_flow_cost (edges, [2, 0, 0, 0, -1, -1], cost, out_flow, tot_cost);

array [1..indirect_n_edges] of var 0..1: out_flow_binary;

constraint forall (i in 1..indirect_n_edges) (if out_flow[i] > 0 then out_flow_binary[i]=1 else out_flow_binary[i] = 0 endif);
%%constraint forall (i in 1..indirect_n_edges) (out_flow_binary[i] = ( 1 where out_flow[i] > 0 ))

var int: minimized_sum = sum (i in 1..indirect_n_edges) (out_flow_binary[i]*cost[i]);

solve minimize minimized_sum;

output [ show(minimized_sum) ];

