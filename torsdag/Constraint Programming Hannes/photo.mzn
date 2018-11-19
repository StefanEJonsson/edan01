include "globals.mzn";

int: n; %no. of students
int: n_prefs; %no. of preferences
set of int: students = 1..n;
set of int: preferences = 1..n_prefs;

output [show(n)];


