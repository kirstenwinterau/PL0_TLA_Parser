---------------------------- MODULE pop37T----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, lv, out, ssn

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 37 => (TRUE))
	 /\ (pc = 38 => (TRUE)) 

STATUS ==  (pc = 37 => (TRUE))
	 /\ (pc = 38 => (TRUE)) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 37 /\ lv \in T /\ ssn \in Ref \union {null} /\ INV /\ out = 0 /\ STATUS
 

pop37T ==  pc = 37 /\ pc' = 38 /\ head = ss /\ head' = ssn /\ UNCHANGED<<ss,stack,mem,lv,out,ssn>> 

Spec ==  Init /\ [][pop37T]_<<head, ss, stack, pc, mem, lv, out, ssn>> 

=============================================================================