---------------------------- MODULE read22T----------------------------
EXTENDS Naturals
VARIABLES c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 22 => ((lock=FALSE => c%2=0)))
	 /\ (pc = 21 => ((lock=FALSE => c%2=0))) 

STATUS ==  (pc = 22 => (TRUE))
	 /\ (pc = 21 => (TRUE)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 22 /\ c0 \in C /\ d1 \in X /\ d2 \in X /\ INV /\ out \in X \X X /\ out[1] = 0 /\ out[2] = 0 /\ STATUS
 

read22T ==  pc = 22 /\ pc' = 21 /\ c % 2 /= 0 /\ UNCHANGED<<c,xa2,x1,xa1,lock,x2,c0,d1,d2,out>> 

Spec ==  Init /\ [][read22T]_<<c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out>> 

=============================================================================