---------------------------- MODULE push19----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 19 => ( mem[n] /= undef /\ mem[n][1]=v /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= n) /\ head /=n /\ ss /= n))
	 /\ (pc = 20 => (TRUE)) 

STATUS ==  (pc = 19 => (in=v ))
	 /\ (pc = 20 => (in=v )) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 19 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push19 ==  pc = 19 /\ pc' = 20 /\ ss' = head /\ UNCHANGED<<head,stack,mem,in,v,n>> 

Spec ==  Init /\ [][push19]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================