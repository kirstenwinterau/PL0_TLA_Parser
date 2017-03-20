---------------------------- MODULE write0_D----------------------------
EXTENDS Naturals
VARIABLES d2q, c, in, c0q, d1q, xa2, xa1, d1, inq, c0, d2, out, pc, outq, x1, lock, x2, pcq

CONSTANT C, X

ABS == c%2=0 => x1=xa1 /\ x2=xa2

INV ==  (pc = 0 => ((lock=FALSE => c%2=0) /\  (lock=FALSE => c%2=0)))
	 /\ (pc = 10 => (TRUE)) 

STATUS ==  (pc = 0 => (TRUE))
	 /\ (pc = 10 => (in[1]=d1 /\ in[2]=d2)) 

D ==  TRUE

INVq ==  (pcq\in {0,26} \union 21..24 => (lock=FALSE => c%2=0))
/\ (pcq=24 => ((lock=FALSE => c%2=0) /\ (c=c0q => x1=d1q)))
/\ (pcq=25 /\ c=c0q => (lock=FALSE => c%2=0) /\ x1=d1q /\ x2=d2q)
/\ (pcq=25 /\ (c /= c0q => (lock=FALSE => c%2=0)))
/\ (pcq=0 => (lock=FALSE => c%2=0))
/\ (pcq=24 => (lock=FALSE => c%2=0))
/\ (pcq\in {11,15} => c%2=0)
/\ (pcq \in 12..14 => c%2 /= 0)
/\ (pcq \in 13..14 => x1=d1q)
/\ (pcq=14 => x2=d2q)

STATUSq ==  (pcq=26 => outq[1]=x1 /\ outq[2]=x2) /\ (pcq \in 10..14 => inq[1]=d1q /\ inq[2]=d2q)

Init == /\ x1 \in X /\ x2 \in X /\ c \in C /\ xa1 \in X /\ xa2 \in X /\ lock \in {TRUE, FALSE} /\ ABS /\ pc = 0 /\ d1 = 0 /\ d2 = 0 /\ INV /\ in \in X \X X /\ in[1] = 0 /\ in[2] = 0 /\ c0 = 0  /\ out = 0  /\ STATUS
 /\ (( pcq = 0 /\ d1q = 0 /\ d2q = 0 /\ INVq /\ D /\ inq \in X \X X /\ inq[0] = 0 /\ inq[1] = 0 /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 10 /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ inq \in X \X X /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 11 /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ inq \in X \X X /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 12 /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ inq \in X \X X /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 13 /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ inq \in X \X X /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 14 /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ inq \in X \X X /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 15 /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ inq \in X \X X /\ STATUSq /\ c0q = 0 /\ outq = 0 )
\/( pcq = 0 /\ c0q = 0 /\ d1q = 0 /\ d2q = 0 /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )
\/( pcq = 21 /\ c0q \in C /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )
\/( pcq = 22 /\ c0q \in C /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )
\/( pcq = 23 /\ c0q \in C /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )
\/( pcq = 24 /\ c0q \in C /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )
\/( pcq = 25 /\ c0q \in C /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )
\/( pcq = 26 /\ c0q \in C /\ d1q \in X /\ d2q \in X /\ INVq /\ D /\ outq \in X \X X /\ outq[0] = 0 /\ outq[1] = 0 /\ STATUSq /\ inq = 0 )) 

write0 ==  pc = 0 /\ pc' = 10 /\ in'[1] = d1' /\ in'[2] = d2' /\ in' \in X \X X /\ UNCHANGED<<d2q,c,c0q,d1q,xa2,xa1,inq,c0,out,outq,x1,lock,x2,pcq>> 

Spec ==  Init /\ [][write0]_<<d2q, c, in, c0q, d1q, xa2, xa1, d1, inq, c0, d2, out, pc, outq, x1, lock, x2, pcq>> 

=============================================================================