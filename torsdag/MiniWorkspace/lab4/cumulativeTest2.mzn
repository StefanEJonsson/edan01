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

array[ops] of var 1..(number_add + number_mul): y;
constraint forall(a in add)(y[a] in 1..number_add);
constraint forall(m in mul)(y[m] in (number_add+1)..(number_add+number_mul));
constraint diffn(start, y, duration, neededAdd);
constraint diffn(start, y, duration, neededMul);

array[1..length(last)] of var 0..1000: ends = [start[i]+duration[i] | i in last];
constraint max(ends) = end;

solve minimize end;
%set of 0..10: slize = 2..3 union {5};
output ["start = ", show(start), 
"\nend = ", show(end), 
"\n\nends:", show(ends),
%"\nneeded:", show(needed),
%"\nstart[add] = ", show(start[add]),
%"\nslize = ", show(slize),
%"\nstart[{2..3} union {5}] = ", show(start[slize]),
%"\nduration[add] = ", show(duration[add]),
%"\nneeded[add] = ", show(needed[add]),
%"\nnumber_add = ", show(number_add),
];
