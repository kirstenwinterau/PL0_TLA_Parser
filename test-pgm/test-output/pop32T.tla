---------------------------- MODULE pop32T----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, lv, out, ssn

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 32 => ( ss /= null /\ mem[ss] /= undef))
	 /\ (pc = 33 => ( ss /= null /\ mem[ss] /= undef /\ (ss=head => ssn=mem[ss][2]))) 

STATUS ==  (pc = 32 => (TRUE))
	 /\ (pc = 33 => (TRUE)) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 32 /\ lv \in T /\ ssn \in Ref \union {null} /\ INV /\ out = 0 /\ STATUS
 

pop32T ==  pc = 32 /\ pc' = 33 /\ ss = null /\ UNCHANGED<<head,ss,stack,mem,lv,out,ssn>> 

Spec ==  Init /\ [][pop32T]_<<head, ss, stack, pc, mem, lv, out, ssn>> 

=============================================================================