---------------------------- MODULE Init----------------------------
EXTENDS Naturals
VARIABLES c, pc, pcq, xa2, x1, xa1, lock, x2, d1, d1q, c0, c0q, d2, d2q

CONSTANTS C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV == TRUE

D == TRUE

INVq == TRUE

Init == /\ c = 0 /\ pc = 0 /\ xa2 = 0 /\ x1 = 0 /\ xa1 = 0 /\ lock \in {TRUE, FALSE} /\ x2 = 0 /\ d1 = 0 /\ c0 = 0 /\ d2 = 0 /\ ( pcq = 0 /\ d1q = 0 /\ c0q = 0 /\ d2q = 0 ) 

Stop == FALSE

Spec ==  Init /\ [][Stop]_<<c, pc, pcq, xa2, x1, xa1, lock, x2, d1, d1q, c0, c0q, d2, d2q>> 

=============================================================================