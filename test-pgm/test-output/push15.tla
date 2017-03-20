---------------------------- MODULE push15----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES head, ss, stack, pc, mem, in, v, n

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 15 => ( mem[n] /= undef /\ (\A r\in Ref : mem[r]/= undef => mem[r][2] /= n  /\ head/=n)))
	 /\ (pc = 16 => (TRUE)) 

STATUS ==  (pc = 15 => (in=v ))
	 /\ (pc = 16 => (in=v )) 

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss = null /\ pc = 15 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ STATUS
 

push15 ==  pc = 15 /\ pc' = 16 /\ n' \in Ref /\ (\A r\in Ref : mem[r][2] /= n' /\ (mem[r] /= undef => r /= n')) /\ mem'= [mem EXCEPT ![n'] = <<0,null>>] /\ UNCHANGED<<head,ss,stack,in,v>> 

Spec ==  Init /\ [][push15]_<<head, ss, stack, pc, mem, in, v, n>> 

=============================================================================