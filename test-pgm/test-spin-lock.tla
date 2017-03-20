------------------------------ MODULE Spinlock ------------------------------

EXTENDS Naturals
\* Replace this default variable with your own variables (it keeps the models editable in the meantime)
VARIABLE pc, x, x0, out, lock, pcq
CONSTANT X

\* Insert any custom definitions that you want to appear in all modules here (e.g. ABS0)

\* Always fill out the definitions below
ABS == x=x0
INV == (pc \in {10, 27} => x=1)
STATUS == (pc \in {28,29} => out=1) /\ (pc \in {31,32} => out=0)
AOP == (pc=21 => x0'=1) /\ (pc=10 => x0' = 0) /\ (pc \in {26.F, 27} => (IF x0=1 THEN x0'=0 /\ out'=1 ELSE x0'=x0 /\ out'=0))


\* Fill out D if you are checking for non-interference
D == /\ \lnot (pc \in {9, 10, 11, 14, 26, 27, 28, 31} /\ pcq \in {9, 10, 11, 14, 26, 27, 28, 31})
     /\ (pc \in {9, 10, 11, 14, 26, 27, 28, 31} => lock /= FALSE)
     /\ (pcq \in {9, 10, 11, 14, 26, 27, 28, 31} => lock /= FALSE)

\* Fill out the status transitions to automatically invoke potential-linearisation-point mode
IN_OUT == FALSE
IN_INOUT == FALSE
INOUT_OUT == FALSE
INOUT_IN == FALSE
STATUSHELPER == TRUE


=============================================================================