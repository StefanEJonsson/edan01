include "ar_1_1.dzn";

int : del_add; % clock cycles per adder
int : del_mul; % clock cycles per multiplier
int : number_add; % number of adders
int : number_mul; % number of multipliers
int : n; % number of operations
set of int : last;
set of int : add; % indices of adders
set of int : mul; % indices of multipliers
array[1..n] of set of int : dependencies;