---------------------------- MODULE write13----------------------------
EXTENDS Naturals
VARIABLES c, pc, in, xa2, x1, xa1, lock, x2, d1, d2

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 13 => ((c%2 /= 0) /\ (x1=d1)))
	 /\ (pc = 14 => ((c%2 /= 0) /\ (x1=d1) /\  x2=d2)) 

STATUS ==  (pc = 13 => (in[1]=d1 /\ in[2]=d2))
	 /\ (pc = 14 => (in[1]=d1 /\ in[2]=d2)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 13 /\ d1 \in X /\ d2 \in X /\ INV /\ in \in X \X X /\ STATUS
 

write13 ==  pc = 13 /\ pc' = 14 /\ x2' = d2 /\ UNCHANGED<<c,in,xa2,x1,xa1,lock,d1,d2>> 

Spec ==  Init /\ [][write13]_<<c, pc, in, xa2, x1, xa1, lock, x2, d1, d2>> 

=============================================================================