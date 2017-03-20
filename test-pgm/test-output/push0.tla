---------------------------- MODULE push0----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 0 => (TRUE))
	 /\ (pc = 15 => ( mem[n] /= undef /\ (\A r\in Ref : mem[r]/= undef => mem[r][2] /= n  /\ head/=n))) 

STATUS ==  (pc = 0 => (TRUE))
	 /\ (pc = 15 => (in=v )) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss = null /\ pc = 0 /\ v = 0 /\ n = null /\ INV /\ in = 0 /\ STATUS
 

push0 ==  pc = 0 /\ pc' = 15 /\ v' \in T /\ in' = v' /\ UNCHANGED<<head,ss,stack,mem,n>> 

Spec ==  Init /\ [][push0]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================