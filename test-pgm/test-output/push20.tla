---------------------------- MODULE push20----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 20 => (TRUE))
	 /\ (pc = 22 => (TRUE)) 

STATUS ==  (pc = 20 => (in=v ))
	 /\ (pc = 22 => (TRUE)) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 20 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push20 ==  pc = 20 /\ pc' = 22 /\ mem' = [mem EXCEPT ![n] = <<@[1],ss>>] /\ UNCHANGED<<head,ss,stack,in,v,n>> 

Spec ==  Init /\ [][push20]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================