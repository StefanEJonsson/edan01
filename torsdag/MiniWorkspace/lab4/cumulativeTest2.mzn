include "ar_1_3.dzn";
include "globals.mzn";

%imported data
int: del_add;    % clock cycles per adder
int: del_mul;    % clock cycles per multiplier
int: number_add; % number of adders
int: number_mul; % number of multipliers
set of int: last;
set of int: add; % indices of adders
set of int: mul; % indices of multipliers
int: n;          % number of operations

set of int: ops = 1..n; %operations

array[ops] of set of int : dependencies;
array[ops] of var 0..1000: start;
array[ops] of 0..max(del_add,del_mul): duration = [if i in add then del_add else del_mul endif | i in ops];

var 0..1000: end;

array[ops] of 0..1: neededAdd = [if i in add then 1 else 0 endif | i in ops];
array[ops] of 0..1: neededMul = [if i in mul then 1 else 0 endif | i in ops];

constraint forall (i in ops)(
  forall (j in dependencies[i])(
    start[j] >= start[i] + duration[i]
  )
);


constraint cumulative(start, duration, neededAdd, number_add);
constraint cumulative(start, duration, neededMul, number_mul);

array[ops] of var 0..number_add: y_add;
array[ops] of var 0..number_mul: y_mul;
constraint forall(a in add)(y_add[a] in 1..number_add /\ y_mul[a] = 0);
constraint forall(m in mul)(y_mul[m] in 1..number_mul /\ y_add[m] = 0);
constraint diffn(start, y_add, duration, neededAdd);
constraint diffn(start, y_mul, duration, neededMul);

array[1..length(last)] of var 0..1000: ends = [start[i]+duration[i] | i in last];
constraint max(ends) = end;

solve::seq_search([
    int_search(start, first_fail, indomain_min, complete),
    int_search(y_mul++y_add, first_fail, indomain_min, complete)
])
 minimize end;

output ["start = ", show(start), 
"\nend = ", show(end), 
"\n\nends:", show(ends),
"\ny_add:", show(y_add),
"\ny_mul:", show(y_mul),
];
