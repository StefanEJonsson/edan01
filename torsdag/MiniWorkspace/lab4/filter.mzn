include "ar_2_4.dzn";
include "globals.mzn";

%imported data
int : del_add; % clock cycles per adder
int : del_mul; % clock cycles per multiplier
int : number_add; % number of adders
int : number_mul; % number of multipliers
int : n; % number of operations
set of int : last;
set of int : add; % indices of adders
set of int : mul; % indices of multipliers
array[1..n] of set of int : dependencies;


% 
int: number_op = number_add + number_mul;
array[1..n] of var 1..number_op: r; % = y
%array[1..n] of var 0..(number_op-1): y;
%constraint forall(i in 1..n)(y[i] = r[i]-1); 
array[1..n] of var 1..1: dy;
array[1..n] of var 1..max(del_add,del_mul): dx;
array[1..n] of var 0..10000: x; % = s
array[1..n] of var 0..10005: xdx; % = x + dx

var int: endTime;

constraint forall(i in 1..n)(
if i in add then
dx[i] = del_add /\
r[i] in 1..number_add
else
dx[i] = del_mul /\
r[i] in (number_add + 1)..number_op
endif
);



%dx = [(del_add where i in add) \/ (del_mul |i in 1..n where i in mul)];

constraint forall (i in 1..n)(
  forall (j in dependencies[i])(
    x[j] >= x[i] + dx[i]
  )
);




constraint diffn(x, r, dx, dy);
%Constrains rectangles i , given by their origins ( x [ i ], y [ i ]) and sizes ( dx [ i ], dy [ i ]), to be non-overlapping. Zero-width rectangles can still not overlap with any other rectangle.


constraint cumulative(x, dx, r, number_op);

%Requires that a set of tasks given by start times s , durations d , and resource requirements r , never require more than a global resource bound b at any one time.

constraint forall (i in 1..n)(xdx[i] = x[i] + dx[i]);

endTime = max(xdx);
solve minimize endTime;
%output[show(1..number_op),"\n", show(max(del_add,del_mul))]
output[
"x: ", show(x),
"\ndx: ", show(dx),
"\ndy: ", show(dy),
%"\ny: ", show(y),
"\nr: ", show(r),
"\nnbr op: ", show(number_op),
"\n test. ", show(r[20]),
"\n endTime: ", show(endTime)]