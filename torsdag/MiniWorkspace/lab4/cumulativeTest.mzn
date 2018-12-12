include "ar_2_4.dzn";
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
array[ops] of var 1..2: duration;

var 0..1000: end;

array[ops] of var 0..1: neededAdd;
array[ops] of var 0..1: neededMul;

constraint forall(i in ops)(
  if i in add then
    neededAdd[i] = 1 /\
    neededMul[i] = 0 /\
    duration[i] = del_add
  else
    neededAdd[i] = 0 /\
    neededMul[i] = 1 /\
    duration[i] = del_mul
  endif
);

constraint forall (i in ops)(
  forall (j in dependencies[i])(
    start[j] >= start[i] + duration[i]
  )
);

constraint cumulative(start, duration, neededAdd, number_add);
constraint cumulative(start, duration, neededMul, number_mul);

constraint forall(i in ops)(start[i]+duration[i] <= end);

solve minimize end;

output ["start = ", show(start), "\nend = ", show(end), "\n"];
