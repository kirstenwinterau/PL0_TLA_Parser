---------------------------- MODULE write15----------------------------
EXTENDS Naturals
VARIABLES c, pc, in, xa2, x1, xa1, lock, x2, d1, d2

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 15 => (c%2=0))
	 /\ (pc = 0 => ((lock=FALSE => c%2=0) /\  (lock=FALSE => c%2=0))) 

STATUS ==  (pc = 15 => (TRUE))
	 /\ (pc = 0 => (TRUE)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 15 /\ d1 \in X /\ d2 \in X /\ INV /\ in \in X \X X /\ STATUS
 

write15 ==  pc = 15 /\ pc' = 0 /\ lock = TRUE /\ lock' = FALSE /\ UNCHANGED<<c,in,xa2,x1,xa1,x2,d1,d2>> 

Spec ==  Init /\ [][write15]_<<c, pc, in, xa2, x1, xa1, lock, x2, d1, d2>> 

=============================================================================