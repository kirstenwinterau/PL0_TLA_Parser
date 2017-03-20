---------------------------- MODULE push16----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 16 => (TRUE))
	 /\ (pc = 19 => ( mem[n] /= undef /\ mem[n][1]=v /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= n) /\ head /=n /\ ss /= n)) 

STATUS ==  (pc = 16 => (in=v ))
	 /\ (pc = 19 => (in=v )) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss = null /\ pc = 16 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push16 ==  pc = 16 /\ pc' = 19 /\ mem' = [mem EXCEPT ![n] = <<v,@[2]>>] /\ UNCHANGED<<head,ss,stack,in,v,n>> 

Spec ==  Init /\ [][push16]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================