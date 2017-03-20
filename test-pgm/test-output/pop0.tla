---------------------------- MODULE pop0----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, lv, out, ssn

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 0 => (TRUE))
	 /\ (pc = 31 => ( ss /= null /\ mem[ss] /= undef)) 

STATUS ==  (pc = 0 => (TRUE))
	 /\ (pc = 31 => ( (out = empty))) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss = null /\ pc = 0 /\ lv = 0 /\ ssn = null /\ INV /\ out = 0 /\ STATUS
 

pop0 ==  pc = 0 /\ pc' = 31 /\ UNCHANGED<<head,ss,stack,mem,lv,out,ssn>> 

Spec ==  Init /\ [][pop0]_<<head, ss, stack, pc, mem, lv, out, ssn>> 

=============================================================================