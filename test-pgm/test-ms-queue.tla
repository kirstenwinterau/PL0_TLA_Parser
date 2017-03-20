---------------------------- MODULE MichaelScott ----------------------------
EXTENDS FiniteSequences, Naturals, Status

VARIABLE retVal, qHead, in, out, tail, queue, nextNode, newNode, value, head, pc, pcq, qTail, mem, retValq, nextNodeq, newNodeq, headq
CONSTANT Ref, undef, T, N, null, empty

ABS0[q \in FiniteSeq(T, N), h \in Ref \union {null}] == (h = null => Len(q)=0) /\
                   (h /= null => Len(q) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(q) /\ ABS0[Tail(q), mem[h][2]])
         
ABS == (qHead /= null /\ qTail/= null /\ mem[qHead] /= undef /\ mem[qTail] /= undef) 
        /\ (mem[qTail][2] = null => (qTail = qHead \/ (Len(queue) /= 0 /\ mem[qTail][1] = queue[Len(queue)])))
        /\ (mem[qTail][2] /= null => (Len(queue) > 1 /\ mem[qTail][1] = queue[Len(queue)-1]) 
             \/ (Len(queue) = 1 /\ qTail = qHead)) /\ ABS0[queue, mem[qHead][2]]

INV == (pc=21 => (head /= null /\ (head=qHead => (head /= tail => mem[head][2] /= null)) /\ tail = qTail))
    /\ (pc \in 20..28 =>  head /= null)
    /\ (pc \in 22..28 =>  mem[head][2] = nextNode)
    /\ (pc=28 => (nextNode /= null))
    /\ (pc \in 22..23 => (head=qHead => (head /= tail => mem[head][2] = nextNode /\  nextNode /= null) /\ (tail=head => (nextNode /= null => (qTail=tail => mem[tail][2]=nextNode)))))
    /\ (pc=24 => (head /= tail => (qHead=head => mem[head][2] = nextNode /\  nextNode /= null)) /\ (tail=head => (nextNode /= null => (qTail=tail => mem[tail][2]=nextNode))))
    /\ (pc=26 => (nextNode /= null => (qTail=tail => mem[tail][2]=nextNode)))
    /\ (pc=28 => (qTail=tail => mem[tail][2]=nextNode))
    /\ (pc \in 20..32 => head /= null)
    /\ (pc=32 => (head /= tail /\ qHead=head => mem[head][2] =  nextNode /\  nextNode /= null))
    /\ (pc=33 => (head /= tail /\ qHead=head => mem[head][2] = nextNode /\ nextNode /= null /\ (head=qHead => retVal = mem[head][1])))
    /\ (pc=42 => qHead /= newNode /\ qTail /= newNode)
    /\ (pc \in 42..52 => mem[newNode] /= undef /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= newNode) /\ newNode /= qHead /\ newNode /= qTail)
    /\ (pc=56 => mem[newNode] /= undef /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= newNode) /\ newNode /= qHead /\ newNode /= qTail)
    /\ (pc=43 => qHead /= newNode /\ qTail /= newNode /\ mem[newNode][1]=value)
    /\ (pc \in 47..56 => tail /= null)
    /\ (pc \in 46..56 => mem[newNode][1]=value /\ mem[newNode][2]=null)
    /\ (pc \in 48..49 => (qTail=tail => mem[qTail][2]=nextNode))
    /\ (pc \in {50, 56} => (mem[tail][2]=nextNode => tail=qTail) /\ (qTail=tail => mem[qTail][2]=nextNode))
    /\ (pc \in 52..53 => nextNode = null /\ mem[newNode][1]=value /\ mem[newNode][2]=null /\ (mem[tail][2]=nextNode => tail=qTail /\ nextNode=null))
    /\ (pc = 53 => (qTail=tail => mem[qTail][2]=newNode))
    /\ (pc = 56 => nextNode /= null)
    /\ (pc=58 => (qTail = tail => mem[tail][2] = newNode))

STATUS == (pc \in 22..26 => (nextNode = null => out = empty)) /\ (pc=27 => out = empty)
                 /\ (pc=34 => (out = retVal)) /\ (pc \in 41..56 => (in = value))

AOP == (pc \in 19..34 => ((Len(queue)=0 => out'=empty /\ queue'=queue) 
                        /\ (Len(queue) /= 0 => out'=Head(queue) /\ queue' = Tail(queue))))
      /\ (pc \in 41..58 => (queue' = queue \o <<in>>))
             
D ==  (pc \in 22..33 /\ pcq \in 22..33 => nextNode /= nextNodeq) 
        /\ (pc \in 22..33 /\ pcq \in 48..56 => nextNode /= nextNodeq)
        /\ (pc \in 48..56 /\ pcq \in 22..33 => nextNode /= nextNodeq)
        /\ ( pc \in 48..56 /\ pcq \in 48..56 => nextNode /= nextNodeq)
        /\ (pc \in 42..58 /\ pcq \in 42..58 => newNode /= newNodeq) 
        /\ (pc \in 22..33 /\ pcq \in 42..58 => nextNode /= newNodeq)
        /\ (pc \in 48..46 /\ pcq \in 48..56 => nextNode /= newNodeq)
        /\ (pc \in 42..58 /\ pcq \in 48..56 => newNode /= nextNodeq)
        /\ (pc \in 42..58 /\ pcq \in 48..56 => newNode /= nextNodeq)
        /\ (pc = 33 => retVal = mem[head][1])
        /\ (pcq = 33 => retValq = mem[headq][1])
        /\ (pc \in {32,33} => mem[head] /= undef /\ nextNode = mem[head][2])
        /\ (pcq \in {32,33} => mem[headq] /= undef /\ nextNodeq = mem[headq][2])
        /\ (pc = 52 => mem[nextNode] /= undef /\ mem[nextNode][2] = null)
        /\ (pcq = 52 => mem[nextNodeq] /= undef /\ mem[nextNodeq][2] = null)

             
STATUSHELPER == (pc \in 19..21 => In) /\ (pc \in 22 => (In \/ InOut)) /\ (pc= 23 => In) 
             /\ (pc \in 24..26 => (In \/ Out)) /\ (pc = 27 => Out)
             /\ (pc \in 28..33 => In) /\ (pc = 34 => Out) /\ (pc \in 41..52 => In) 
             /\ (pc = 53 => Out) /\ (pc=56 => In) /\ (pc = 58 => Out)
             
IN_OUT == (pc = 33 /\ pc' = 34) \/ (pc = 52 /\ pc'= 53)

IN_INOUT == (pc = 21 /\ pc' = 22 /\ Len(queue) = 0) 

INOUT_OUT == (pc = 22 /\ pc' = 24 /\ Len(queue) = 0) 

INOUT_IN == (pc = 22) \/ (pc = 26 /\ pc' /=  27) 
=============================================================================
