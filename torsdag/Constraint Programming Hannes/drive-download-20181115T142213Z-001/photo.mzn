include "globals.mzn";

int: n; %no. of students
int: n_prefs; %no. of preferences
set of int: students = 1..n;
set of int: preferences = 1..n_prefs;

array[preferences, 1..2] of int: prefs; %preferences

array[students] of var students : order;
array[1..n-1, 1..n_prefs] of var 0..1: correctScore;

constraint all_different(order);
constraint forall (i in 1..n-1, m in 1..n_prefs)(
  if (order[i] = prefs[m,1] \/ order[i] =  prefs[m,2]) /\ 
    (order[i+1] = prefs[m,1] \/ order[i+1] = prefs[m,2])
    then correctScore[i,m] = 1 else correctScore[i,m] = 0 endif);

solve maximize sum(correctScore);

output [show(n)];


