sets
I        orders          / A, B, C /
J        units           /J1 * J4/
K        stages          /K1 * K2/
;

table  Jk(j,k)  if unit j in stage k
         K1      K2
J1       1       0
J2       1       0
J3       0       1
J4       0       1
;

table  JF(i,j)  if order i is forbidden in unit j
         J1      J2      J3      J4
A        0       0       0       0
B        0       0       0       0
C        0       0       0       0
;

parameters
q(i)  'demand(kf) of order i'
/ A  30,
  B  40,
  C  40 /
r(i)  'release time(hr) of order i'
/ A  0,
  B  0,
  C  0 /

d(i)  'due time(hr) of order i'
/ A  30,
  B  30,
  C  30 /

b_min(j)  'min batch size(kg) in unit j'
/ J1  10,
  J2  20,
  J3  20,
  J4  25 /
b_max(j)  'max batch size(kg) in unit j'
/ J1  30,
  J2  40,
  J3  35,
  J4  50 /
;

table  tau_F(i,j)  'fixed term(hr) of order i in j'
         J1      J2      J3                      J4
A        2.5     2.0     0.88888888888889        2.0
B        2.5     2.0     0.88888888888889        2.0
C        2.5     2.0     0.88888888888889        2.0
;

table  tau_P(i,j)  proportional term(hr) of order i in j
         J1                 J2      J3                    J4
A        0.08333333333333   0.1     0.08888888888888889   0.08
B        0.08333333333333   0.1     0.08888888888888889   0.08
C        0.08333333333333   0.1     0.08888888888888889   0.08
;


parameters
H          'horizon time(hr)'
JA(i,j,k)  'if unit j is allowable of order i in stage k'
bi_min(i)  'min  feasible batch size for order i'
bi_max(i)  'max  feasible batch size for order i'
li_min(i)  'min  num of batch'
li_max(i)  'max  num of batch'
;

H = 30;
JA(i,j,k) = 0;
JA(i,j,k)$(Jk(j,k) and JF(i,j)<>1) = 1;
bi_min(i) = smax(k, smin( j$(JA(i,j,k) = 1), b_min(j) ));
bi_max(i) = smin(k, smax( j$(JA(i,j,k) = 1), b_max(j) ));
li_max(i) = ceil(q(i) / bi_min(i));
li_min(i) = ceil(q(i) / bi_max(i));

sets
l                Dummy placeholder       /1*3/
Li(i,l);
Li(i,l)$(ord(l) <= li_max(i)) = yes;

alias(i, i_), (l, l_), (k, k_), (j, j_);
sets
IL(i,l,i_,l_);
IL(i,l,i_,l_)$(Li(i,l) and Li(i_, l_)
               and (ord(i) <> ord(i_)
                    or (ord(i) = ord(i_) and ord(l) <> ord(l_)) ) ) = yes;
$onempty
sets
FP(j,j_)         forbidden path between units j j_       / /;
$offempty

positive variables
B(i,l)           batch size
B_(i,l,j)        batch size (i l) in unit j
T(i,l,k)         finish time of batch(i l) in stage k
;

VARIABLE
MS               makespan
;

binary variables
X(i,l,j)  batch (i l) assigned to j
Z(i,l)  selection of batch
Y(i,l,i_,l_,k)  batch (i l) processed before (i_ l_) in stage k
;


* Batching and assignment constraints
equations eq3, eq4a, eq4b, eq5, eq6, eq7a, eq7b, eq8;
eq3(i).. sum(l$(Li(i,l)), B(i,l)) =g= q(i);

eq4a(i,l)$(Li(i,l)).. B(i,l) =g= bi_min(i) * Z(i,l);
eq4b(i,l)$(Li(i,l)).. B(i,l) =l= bi_max(i) * Z(i,l);

eq5(i,l,k)$(Li(i,l)).. Z(i,l) =e= sum(j$(JA(i,j,k)), X(i,l,j) );
eq6(i,l,k)$(Li(i,l)).. B(i,l) =e= sum(j$(JA(i,j,k)), B_(i,l,j));

eq7a(i,l,j)$(Li(i,l)).. B_(i,l,j) =g= b_min(j) * X(i,l,j);
eq7b(i,l,j)$(Li(i,l)).. B_(i,l,j) =l= b_max(j) * X(i,l,j);

eq8(i,l)$(Li(i,l) and ord(l) < card(l)).. Z(i, l+1) =l= Z(i,l);


* Sequencing and timing constraints
equations eq9, eq10, eq11;
eq9(i,l,i_,l_,k,j)$((IL(i,l,i_,l_)) and (ord(i) <= ord(i_)) and JA(i,j,k) and JA(i_,j,k))..
X(i,l,j) + X(i_,l_,j) - 1 =l= Y(i,l,i_,l_,k) + Y(i_,l_,i,l,k);

eq10(i,l,i_,l_,k)$(IL(i,l,i_,l_)).. T(i_,l_,k) =g= T(i,l,k)
+ sum(j$JA(i,j,k), tau_F(i_,j) * X(i_,l_,j) + tau_P(i_,j) * B_(i_,l_,j) )
- H * (1 - Y(i,l,i_,l_,k));

eq11(i,l,k)$(Li(i,l) and ord(k) < card(k)).. T(i,l,k+1) =g= T(i,l,k)
+ sum(j$JA(i,j,k+1), tau_F(i,j) * X(i,l,j) + tau_P(i,j) * B_(i,l,j));


* Additional constraints
equations eq12, eq13, eq14, eq15, eq16, eq17;
eq12(i,l,k)$(Li(i,l)).. T(i,l,k) =g= r(i) * Z(i,l)
+ sum(k_$(ord(k_) <= ord(k)), sum(j$(JA(i,j,k_)), tau_F(i,j) * X(i,l,j) + tau_P(i,j) * B_(i,l,j) ));

eq13(i,l,k)$(Li(i,l)).. T(i,l,k) =l= d(i) * Z(i,l)
- sum(k_$(ord(k_) > ord(k)), sum(j$(JA(i,j,k_)), tau_F(i,j) * X(i,l,j) + tau_P(i,j) * B_(i,l,j) ));

eq14(i,l,j,j_)$(Li(i,l) and FP(j,j_)).. X(i,l,j) + X(i,l,j_) =l= Z(i,l);
eq15(i,l,j)$(Li(i,l) and JF(i,j)).. X(i,l,j) =e= 0;
eq16(i,l)$(Li(i,l) and ord(l) < card(l)).. B(i,l+1) =l= B(i,l);
eq17(i,l)$(ord(l) <= li_min(i)).. Z(i,l) =e= 1;


* Objective minimizing makespan
equations eq23;
eq23(i,l)$(Li(i,l)).. MS =g= T(i,l,'K2');


* Fix batch size
B.fx('A', '1') = 30;
B.fx('B', '1') = 40;
B.fx('C', '1') = 40;

* find solver time
scalar tcomp, texec, telapsed;
tcomp = TimeComp;
texec = TimeExec;
telapsed = TimeElapsed;

options
limrow = 100000,
optcr = 0,
mip = CPLEX;


model ex1 / all /;

solve ex1 using mip minimizing MS;

display tcomp, texec, telapsed;








