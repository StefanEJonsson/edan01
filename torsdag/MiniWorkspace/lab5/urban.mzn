include "3.dzn";
include "globals.mzn";

int: n; % side length of area
int: n_commercial;
int: n_residential;
array[0..n] of -n..n: point_distribution;

array[1..n,1..n] of var 0..1: area;
array[1..n] of var min(point_distribution)..max(point_distribution): row_points;
array[1..n] of var min(point_distribution)..max(point_distribution): col_points;
array[1..n] of var 0..5: nbr_res_per_row;

constraint
forall(i in 1..n)(
row_points[i] = point_distribution[sum(area[i,..])] /\
col_points[i] = point_distribution[sum(area[..,i])] /\
nbr_res_per_row[i] = sum(area[i,..])
);

% constraint
%   forall(i in 1..n-1)(
%     row_points[i] <= row_points[i+1] /\
%     col_points[i] <= col_points[i+1]
% );
constraint lex2(area);


%make sure the total of each type is satisfied
constraint sum(nbr_res_per_row) = n_residential;

var int: row_sum = sum(row_points);
var int: col_sum = sum(col_points);


solve maximize(row_sum+col_sum);

output[
"area:","\n", show(area[1,..]),"\n", show(area[2,..]),"\n", show(area[3,..]),"\n", show(area[4,..]),"\n", show(area[5,..]),
%"\n",show(area[6,..]),"\n", show(area[7,..]),
"\ncost: ", show(row_sum + col_sum)]