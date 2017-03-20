---------------------------- MODULE write14----------------------------
EXTENDS Naturals
VARIABLES c, pc, in, xa2, x1, xa1, lock, x2, d1, d2

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 14 => ((c%2 /= 0) /\ (x1=d1) /\  x2=d2))
	 /\ (pc = 15 => (c%2=0)) 

STATUS ==  (pc = 14 => (in[1]=d1 /\ in[2]=d2))
	 /\ (pc = 15 => (TRUE)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 14 /\ d1 \in X /\ d2 \in X /\ INV /\ in \in X \X X /\ STATUS
 

write14 ==  pc = 14 /\ pc' = 15 /\ c' = c + 1 /\  xa1'=in[1] /\ xa2'=in[2] /\ UNCHANGED<<in,x1,lock,x2,d1,d2>> 

Spec ==  Init /\ [][write14]_<<c, pc, in, xa2, x1, xa1, lock, x2, d1, d2>> 

=============================================================================