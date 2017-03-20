---------------------------- MODULE push22T----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 22 => (TRUE))
	 /\ (pc = 23 => (TRUE)) 

STATUS ==  (pc = 22 => (TRUE))
	 /\ (pc = 23 => (TRUE)) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 22 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push22T ==  pc = 22 /\ pc' = 23 /\ head = ss /\ head' = n /\ UNCHANGED<<ss,stack,mem,in,v,n>> 

Spec ==  Init /\ [][push22T]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================