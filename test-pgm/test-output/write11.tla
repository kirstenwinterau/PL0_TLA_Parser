---------------------------- MODULE write11----------------------------
EXTENDS Naturals
VARIABLES c, pc, in, xa2, x1, xa1, lock, x2, d1, d2

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 11 => (c%2=0))
	 /\ (pc = 12 => (c%2 /= 0)) 

STATUS ==  (pc = 11 => (in[1]=d1 /\ in[2]=d2))
	 /\ (pc = 12 => (in[1]=d1 /\ in[2]=d2)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 11 /\ d1 \in X /\ d2 \in X /\ INV /\ in \in X \X X /\ STATUS
 

write11 ==  pc = 11 /\ pc' = 12 /\ c' = c + 1 /\ UNCHANGED<<in,xa2,x1,xa1,lock,x2,d1,d2>> 

Spec ==  Init /\ [][write11]_<<c, pc, in, xa2, x1, xa1, lock, x2, d1, d2>> 

=============================================================================