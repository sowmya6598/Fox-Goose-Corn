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

predicate deaths(var 0..f: lf, var 0..g: lg, var 0..c: lc, 
                 var 0..f: df, var 0..g: dg, var 0..c: dc) =             
     df = 0 /\ dg = 0 /\ dc = 0 
;




predicate arrived(Trips: tripNumber, 1..2: side) =
     let {
       var 0..f: fbefore = foxCount[side, tripNumber-1],
       var 0..g: gbefore = geeseCount[side, tripNumber-1],
       var 0..c: cbefore = cornCount[side, tripNumber-1,],
       var 0..f: fafter = foxCount[side,tripNumber], 
       var 0..g: gafter = geeseCount[side,tripNumber],
       var 0..c: cafter = cornCount[side,tripNumber],
     } in 
     fafter = fbefore + fox[tripNumber] /\
     gafter = gbefore + geese[tripNumber] /\
     cafter = cbefore + corn[tripNumber]
;

predicate departured(Trips: tripNumber, 1..2: side) =
    let {
       var 0..f: fbefore = foxCount[side, tripNumber-1],
       var 0..g: gbefore = geeseCount[side, tripNumber-1],
       var 0..c: cbefore = cornCount[side, tripNumber-1,],
       var 0..f: fafter = foxCount[side,tripNumber], 
       var 0..g: gafter = geeseCount[side,tripNumber],
       var 0..c: cafter = cornCount[side,tripNumber],
       var 0..f: fleft, var 0..g: gleft, var 0..c: cleft,
       var 0..f: fdeaths, var 0..g: gdeaths, var 0..c: cdeaths
     } in 
     
      fleft = fbefore - fox[tripNumber] /\
      gleft = gbefore - geese[tripNumber] /\
      cleft = cbefore - corn[tripNumber] /\
      deaths(fleft, gleft, cleft, fdeaths, gdeaths, cdeaths) /\
      fafter = fleft - fdeaths /\ 
      gafter = gleft - gdeaths /\
      cafter = cleft - cdeaths
;   

constraint forall(trip in Trips where trip mod 2 = 1)(
   arrived(trip, 2) /\ departured(trip, 1)
);

constraint forall(trip in Trips where trip mod 2 = 0)(
   arrived(trip, 1) /\ departured(trip, 2)
);

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
        "Fox    :" ++ show(fox) ++ "\n" ++
        "Geese:" ++ show(geese) ++ "\n" ++
        "Corn:  " ++ show(corn) ++ "\n" ++
        "Trips:" ++ show(trips) ++ "\n" ++
        "obj = " ++ show(obj) ++ ";"]
