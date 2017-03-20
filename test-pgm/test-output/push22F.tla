---------------------------- MODULE push22F----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 22 => (TRUE))
	 /\ (pc = 19 => ( mem[n] /= undef /\ mem[n][1]=v /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= n) /\ head /=n /\ ss /= n)) 

STATUS ==  (pc = 22 => (TRUE))
	 /\ (pc = 19 => (in=v )) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 22 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push22F ==  pc = 22 /\ pc' = 19 /\ head /= ss /\ UNCHANGED<<head,ss,stack,mem,in,v,n>> 

Spec ==  Init /\ [][push22F]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================