------------------------------ MODULE Seqlock ------------------------------

EXTENDS Naturals
\* Replace this default variable with your own variables (it keeps the models editable in the meantime)
VARIABLE pc, c, c0, x1, x2, xa1, xa2, d1, d2, lock, in, out, pcq, c0q
CONSTANT X, C

\* Insert any custom definitions that you want to appear in all modules here (e.g. ABS0)

\* Always fill out the definitions below
ABS == c%2=0 => x1=xa1 /\ x2=xa2
INV == (pc\in {0,26} \union 21..24 => (lock=FALSE => c%2=0))
        /\ (pc=24 => ((lock=FALSE => c%2=0) /\ (c=c0 => x1=d1)))
        /\ (pc=25 /\ c=c0 => (lock=FALSE => c%2=0) /\ x1=d1 /\ x2=d2)
        /\ (pc=25 /\ (c /= c0 => (lock=FALSE => c%2=0)))
        /\ (pc=0 => (lock=FALSE => c%2=0))
        /\ (pc=10 => (lock=FALSE => c%2=0))
        /\ (pc\in {11,15} => c%2=0)
        /\ (pc \in 12..14 => c%2 /= 0)
        /\ (pc \in 13..14 => x1=d1)
        /\ (pc=14 => x2=d2)
        
STATUS == (pc=26 => out[1]=x1 /\ out[2]=x2) /\ (pc \in 10..14 => in[1]=d1 /\ in[2]=d2)
AOP == (pc = 14 => xa1'=in[1] /\ xa2'=in[2]) /\ (pc=25.F => out' \in X \X X /\ out'[1]=x1 /\ out'[2]=x2)


\* Fill out D if you are checking for non-interference
D ==  (pc \in 11..15 => \lnot pcq \in 11..15 /\ lock=TRUE) /\ (pcq \in 11..15 => \lnot pc \in 11..15 /\ lock=TRUE) 
     /\ (pcq \in 21..25 => c0q <= c)


\* Fill out the status transitions to automatically invoke potential-linearisation-point mode
IN_OUT == FALSE
IN_INOUT == FALSE
INOUT_OUT == FALSE
INOUT_IN == FALSE
STATUSHELPER == TRUE


=============================================================================