---------------------------- MODULE read0----------------------------
EXTENDS Naturals
VARIABLES c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 0 => ((lock=FALSE => c%2=0) /\  (lock=FALSE => c%2=0)))
	 /\ (pc = 21 => ((lock=FALSE => c%2=0))) 

STATUS ==  (pc = 0 => (TRUE))
	 /\ (pc = 21 => (TRUE)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 0 /\ c0 = 0 /\ d1 = 0 /\ d2 = 0 /\ INV /\ out \in X \X X /\ out[1] = 0 /\ out[2] = 0 /\ STATUS
 

read0 ==  pc = 0 /\ pc' = 21 /\ UNCHANGED<<c,xa2,x1,xa1,lock,x2,c0,d1,d2,out>> 

Spec ==  Init /\ [][read0]_<<c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out>> 

=============================================================================