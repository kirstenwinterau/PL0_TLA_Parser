---------------------------- MODULE write0----------------------------
EXTENDS Naturals
VARIABLES c, pc, in, xa2, x1, xa1, lock, x2, d1, d2

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 0 => ((lock=FALSE => c%2=0) /\  (lock=FALSE => c%2=0)))
	 /\ (pc = 10 => (TRUE)) 

STATUS ==  (pc = 0 => (TRUE))
	 /\ (pc = 10 => (in[1]=d1 /\ in[2]=d2)) 

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 0 /\ d1 = 0 /\ d2 = 0 /\ INV /\ in \in X \X X /\ in[1] = 0 /\ in[2] = 0 /\ STATUS
 

write0 ==  pc = 0 /\ pc' = 10 /\ in'[1] = d1' /\ in'[2] = d2' /\ in' \in X \X X /\ UNCHANGED<<c,xa2,x1,xa1,lock,x2>> 

Spec ==  Init /\ [][write0]_<<c, pc, in, xa2, x1, xa1, lock, x2, d1, d2>> 

=============================================================================