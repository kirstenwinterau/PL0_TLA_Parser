---------------------------- MODULE read24----------------------------
EXTENDS Naturals
VARIABLES c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 24 => ((lock=FALSE => c%2=0) /\  ((lock=FALSE => c%2=0) /\ (c=c0 => x1=d1)) /\  (lock=FALSE => c%2=0)))
	 /\ (pc = 25 => ( c=c0 => (lock=FALSE => c%2=0) /\ x1=d1 /\ x2=d2 /\  (c /= c0 => (lock=FALSE => c%2=0)))) 

STATUS ==  (pc = 24 => (TRUE))
	 /\ (pc = 25 => (TRUE)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 24 /\ c0 \in C /\ d1 \in X /\ d2 \in X /\ INV /\ out \in X \X X /\ out[1] = 0 /\ out[2] = 0 /\ STATUS
 

read24 ==  pc = 24 /\ pc' = 25 /\ d2' = x2 /\ UNCHANGED<<c,xa2,x1,xa1,lock,x2,c0,d1,out>> 

Spec ==  Init /\ [][read24]_<<c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out>> 

=============================================================================