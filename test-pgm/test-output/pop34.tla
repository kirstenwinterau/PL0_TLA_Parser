---------------------------- MODULE pop34----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, lv, out, ssn

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 34 => (TRUE))
	 /\ (pc = 35 => ( ss /= null /\ mem[ss] /= undef /\ (ss=head => lv=mem[ss][1] /\ ssn=mem[ss][2]))) 

STATUS ==  (pc = 34 => (TRUE))
	 /\ (pc = 35 => (TRUE)) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 34 /\ lv \in T /\ ssn \in Ref \union {null} /\ INV /\ out = 0 /\ STATUS
 

pop34 ==  pc = 34 /\ pc' = 35 /\ ssn' = mem[ss][2] /\ UNCHANGED<<head,ss,stack,mem,lv,out>> 

Spec ==  Init /\ [][pop34]_<<head, ss, stack, pc, mem, lv, out, ssn>> 

=============================================================================