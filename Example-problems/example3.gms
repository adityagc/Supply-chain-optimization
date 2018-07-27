sets
I        orders          / A, B, C, D, E, F, G, H, I, J, K, L /
J        units           /J1 * J6/
K        stages          /K1 * K2/
;

table  Jk(j,k)  if unit j in stage k
         K1      K2
J1       1       0
J2       1       0
J3       1       0
J4       0       1
J5       0       1
J6       0       1
;

table  JF(i,j)  if order i is forbidden in unit j
         J1      J2      J3      J4      J5      J6
A        1       0       0       0       0       0
B*L      0       0       0       0       0       0
;

parameters
q(i)  'demand(kf) of order i'
/ A   80, B   50, C   30, D  105, E   70, F   40,
  G  105, H   20, I   20, J   20, K   20, L   20 /

r(i)  'release time(hr) of order i'
/ A   20, B    5, C    0, D   25, E    0, F    0,
  G   30, H    0, I   20, J   40, K   40, L   30 /

d(i)  'due time(hr) of order i'
/ A   50, B   30, C   20, D   60, E   40, F   30,
  G   60, H   20, I   80, J   80, K   70, L   70 /

b_min(j)  'min batch size(kg) in unit j'
/ J1  10,
  J2  10,
  J3  15,
  J4  10,
  J5  15,
  J6  10 /

b_max(j)  'max batch size(kg) in unit j'
/ J1  25,
  J2  25,
  J3  30,
  J4  25,
  J5  30,
  J6  25 /
;

table  tau_F(i,j)  fixed term(hr) of order i in j
         J1                  J2                  J3                  J4                  J5                  J6
A*C      3.24444444444444    2.88888888888889    3.13333333333333    2.31111111111111    2.23333333333333    2.22222222222222
D*F      2.88888888888889    3.33333333333333    2.83333333333333    2.0                 2.33333333333333    2.13333333333333
G*J      3.02222222222222    3.33333333333333    3.0                 2.13333333333333    2.16666666666667    2.13333333333333
K*L      3.46666666666667    2.84444444444444    2.33333333333333    2.22222222222222    2.0                 2.0
;

table  tau_P(i,j)  proportional term(hr) of order i in j
         J1                  J2                  J3                  J4                  J5                  J6
A*C      0.16222222222222    0.14444444444444    0.209               0.11666666666666    0.149               0.11111111111111
D*F      0.14444444444444    0.16666666666667    0.18888888888889    0.1                 0.15555555555556    0.10666666666667
G*J      0.15111111111111    0.16666666666667    0.2                 0.10666666666667    0.14444444444444    0.11111111111111
K*L      0.17333333333333    0.14222222222222    0.15555555555556    0.11111111111111    0.13333333333333    0.1

table  c_F(i,j)  fixed processing cost for order i in j
         J1      J2      J3      J4      J5      J6
A        0       85      90      100     100     110
B        50      52      41      91      91      91
C        100     110     90      50      50      55
D        20      10      10      61      61      61
E        80      80      90      110     120     130
F        70      70      70      40      40      30
G        100     100     100     90      90      100
H        10      30      40      45      45      45
I        15      20      20      35      40      35
J        30      40      30      35      45      25
K        15      20      40      15      25      40
L        25      30      30      40      35      45
;
parameters
c_P(i,j)   'proportional processing cost of order i in unit j';
c_P(i,j) = 0;


parameters
H          'horizon time(hr)'
JA(i,j,k)  'if unit j is allowable of order i in stage k'
bi_min(i)  'min  feasible batch size for order i'
bi_max(i)  'max  feasible batch size for order i'
li_min(i)  'min  num of batch'
li_max(i)  'max  num of batch'
;

H = 80;
JA(i,j,k) = 0;
JA(i,j,k)$(Jk(j,k) and JF(i,j)<>1) = 1;
bi_min(i) = smax(k, smin( j$(JA(i,j,k) = 1), b_min(j) ));
bi_max(i) = smin(k, smax( j$(JA(i,j,k) = 1), b_max(j) ));
li_max(i) = ceil(q(i) / bi_min(i));
li_min(i) = ceil(q(i) / bi_max(i));

sets
l                Dummy placeholder       /1*12/
Li(i,l);
Li(i,l)$(ord(l) <= li_max(i)) = yes;

alias(i, i_), (l, l_), (k, k_), (j, j_);
sets
IL(i,l,i_,l_);
IL(i,l,i_,l_)$(Li(i,l) and Li(i_, l_)
               and (ord(i) <> ord(i_)
                    or (ord(i) = ord(i_) and ord(l) <> ord(l_)) ) ) = yes;

sets
FP(j,j_);
FP('J1','J6') = yes;
FP('J2','J5') = yes;


display Jk, JF, bi_min, bi_max, li_max, li_min, Li, IL, FP, JA, tau_F, tau_P, c_F, c_P;


positive variables
B(i,l)           batch size
B_(i,l,j)        batch size (i l) in unit j
T(i,l,k)         finish time of batch(i l) in stage k
;


VARIABLE
*MS               makespan
*earl             earliness
cp               processing cost
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


* Objective minimizing earliness
equations eq22;
eq22.. cp =e= sum((i,l,j,k)$(Li(i,l) and JA(i,j,k)), c_F(i,j) * X(i,l,j) + c_P(i,j) * B_(i,l,j));

*eq22.. earl =e= sum((i,l)$(Li(i,l)),d(i)*Z(i,l) - T(i,l,'K2'));
*eq23(i,l)$(Li(i,l)).. MS =g= T(i,l,'K2');


* find solver time
scalar tcomp, texec, telapsed;
tcomp = TimeComp;
texec = TimeExec;
telapsed = TimeElapsed;

options
limrow = 100000,
optcr = 0,
mip = CPLEX;


model ex3 / all /;

solve ex3 using mip minimizing cp;

display tcomp, texec, telapsed;









