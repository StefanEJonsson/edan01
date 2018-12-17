include "globals.mzn";
include "3.dzn";

int: n;
int: n_commercial;
int: n_residential;

array [0..n] of int: point_distribution;

array[1..n,1..n] of var 0..1: plan;

array[1..n] of var int: rowPoints;
array[1..n] of var int: colPoints;

constraint forall (i in 1..n) (
  rowPoints[i] = point_distribution[sum (plan[i,1..n])]
);

constraint forall (j in 1..n) (
  colPoints[j] = point_distribution[sum (plan[1..n,j])]
);

constraint sum(i in 1..n, j in 1..n) (plan[i,j]) = n_residential;

constraint lex2(plan);

var int: totalPoints =
  sum (i in 1..n) (rowPoints[i]) + sum (j in 1..n) (colPoints[j]);

solve maximize totalPoints;

output [ show(plan) ];
output [ show(totalPoints)];
