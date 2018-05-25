int: f;
int: g;
int: c;
int: k;
set of int: Cap = 0..k;
int: t;
set of int: Trips = 1..t;
int: pf;
int: pg;
int: pc;

%%% We will now declare the variables

array[Trips] of var 0..c: corn;
array[Trips] of var 0..g: geese;
array[Trips] of var 0..f: fox;

var int: obj;
var 1..t: trips;

%%% We are still declaring variables. Within the array, the value 1 will represent the left side of the river whereas the value 2 will represent the right side of the river. The following variables represent the numerical value of each after object after every trip.
array[1..2, 0..t] of var 0..t: cornCount;
array[1..2, 0..t] of var 0..t: geeseCount;
array[1..2, 0..t] of var 0..t: foxCount;

%%% We will now add some constraints

%% First Constraint must be that the number of trips should be odd. Assuming that we travel from the left side first, examples of combinations would be going right OR going right-left-right OR going right-left-right-left-right -- all odd number of trips.
constraint trips mod 2 == 1;

%% Second constraint is that there is only one existance of each object
constraint forall([ fox[i] + geese[i] + corn[i] <= k |i in Trips]);

% Third constraint is the fact that objects are moving from each side of the river when carried on the boat

% Moving objects from the right side of the river to the left side
constraint forall([foxCount[1,i] == foxCount[1, i-1] + fox[i] /\ foxCount[2, i] == foxCount[2, i-1] - fox[i] | i in 1..trips where i mod 2 == 0]);

constraint forall([geeseCount[1,i] == geeseCount[1, i-1] + geese[i] /\ geeseCount[2, i] == geeseCount[2, i-1] - geese[i] | i in 1..trips where i mod 2 == 0]);

constraint forall([cornCount[1,i] == cornCount[1, i-1] + corn[i] /\ cornCount[2, i] == cornCount[2, i-1] - corn[i] | i in 1..trips where i mod 2 == 0]);

% Moving objects from the left side of the river to the right side
constraint forall([foxCount[2,i] == foxCount[2, i-1] + fox[i] /\ foxCount[1, i] == foxCount[1, i-1] - fox[i] | i in 1..trips where i mod 2 == 1]);

constraint forall([geeseCount[2,i] == geeseCount[2, i-1] + geese[i] /\ geeseCount[1, i] == geeseCount[1, i-1] - geese[i] | i in 1..trips where i mod 2 == 1]);

constraint forall([cornCount[2,i] == cornCount[2, i-1] + corn[i] /\ cornCount[1, i] == cornCount[1, i-1] - corn[i] | i in 1..trips where i mod 2 == 1]);

%Fourth Constraint shows that the simulation starts with all objects and the boat being on the left side
constraint foxCount[1,0] = f;
constraint foxCount[2,0] = 0;
constraint geeseCount[1,0] = g;
constraint geeseCount[2,0] = 0;
constraint cornCount[1,0] = c;
constraint cornCount[2,0] = 0;

%Fifth Constraint shows the amount of points received from transporting each object to the other side successfully
constraint obj = foxCount[2,trips] * pf +
                 geeseCount[2,trips] * pg +
                 cornCount[2, trips] * pc;

%%% Solve
% Taken from handout.pdf
solve :: int_search([trips], input_order, indomain_min, complete)
maximize obj;

%%% Output
% This output should reflect the optimal solution presented in handout.pdf
output[
        "Fox:" ++ show(foxCount[2,trips]) ++ "\n" ++
        "Geese:" ++ show(geeseCount[2,trips]) ++ "\n" ++
        "Corn:" ++ show(cornCount[2,trips]) ++ "\n" ++
        "Trips:" ++ show(trips) ++ "\n" ++
        "Obj:" ++ show(obj)]