---------------------------- MODULE read25F----------------------------
EXTENDS Naturals
VARIABLES c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 25 => ( c=c0 => (lock=FALSE => c%2=0) /\ x1=d1 /\ x2=d2 /\  (c /= c0 => (lock=FALSE => c%2=0))))
	 /\ (pc = 26 => ((lock=FALSE => c%2=0))) 

STATUS ==  (pc = 25 => (TRUE))
	 /\ (pc = 26 => ( out[1]=x1 /\ out[2]=x2)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 25 /\ c0 \in C /\ d1 \in X /\ d2 \in X /\ INV /\ out \in X \X X /\ out[1] = 0 /\ out[2] = 0 /\ STATUS
 

read25F ==  pc = 25 /\ pc' = 26 /\ c = c0 /\  out' \in X \X X /\ out'[1]=x1 /\ out'[2]=x2 /\ UNCHANGED<<c,xa2,x1,xa1,lock,x2,c0,d1,d2>> 

Spec ==  Init /\ [][read25F]_<<c, pc, xa2, x1, xa1, lock, x2, c0, d1, d2, out>> 

=============================================================================