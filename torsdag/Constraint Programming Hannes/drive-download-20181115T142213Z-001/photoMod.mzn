include "globals.mzn";

int: n; %no. of students
int: n_prefs; %no. of preferences
set of int: students = 1..n;
set of int: preferences = 1..n_prefs;

array[preferences, 1..2] of int: prefs; %preferences

array[students] of var students : order;
array[1..n_prefs] of var int: distances;

constraint all_different(order);
constraint 
forall (i in 1..n_prefs)(
  forall (k in 1..n)(
    if prefs[i,1] = order[k] 
    then forall (l in 1..n)(
      if prefs[i,2] = order[l]
      then distances[i] = abs(k-l)
      else true 
      endif)
    else true
    endif)
);

solve minimize max(distances);

output [show(prefs), "\n", show(order), "\n", show(distances), "\n", show(max(distances))];
