---------------------------- MODULE push23----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 23 => (TRUE))
	 /\ (pc = 0 => (TRUE)) 

STATUS ==  (pc = 23 => (TRUE))
	 /\ (pc = 0 => (TRUE)) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 23 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push23 ==  pc = 23 /\ pc' = 0 /\ UNCHANGED<<head,ss,stack,mem,in,v,n>> 

Spec ==  Init /\ [][push23]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================