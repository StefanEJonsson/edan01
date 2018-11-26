int: n_vertices = 4;
int: n_edges = 4;
array [1..n_edges] of int: from = [1,2,3,10];
array [1..n_edges] of int: to   = [3,4,6,11];

%array [1..n_edges,1..2] of int: edges = [|1,3|2,4|3,6|];
%array [1..n_edges,1..2] of int: edges2 = array2d(1..n_edges, 1..2, [1,2,3,4]);

array [1..2] of int: edges4 = [from[(i*2)+1] | i in 0..1];
array [1..2] of int: edges5 = [to  [(i*2)+1] | i in 0..1];
array [1..2] of int: edges6 = [from[(i*2)+2] | i in 0..1];
array [1..2] of int: edges7 = [to  [(i*2)+2] | i in 0..1];

array [1..2*n_edges] of int: edges3 = edges4 ++ edges5 ++ edges6 ++ edges7;

output [ show(edges3) ]

