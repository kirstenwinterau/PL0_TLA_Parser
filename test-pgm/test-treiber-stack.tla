---------------------------- MODULE TreiberStack ----------------------------
EXTENDS FiniteSequences, Naturals, Status

VARIABLE stack, head, mem, ss, ssn, lv, v, in, out, pc, n, nq, pcq, lvq, ssq, ssnq

CONSTANT Ref, T, null, N, undef, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
            
ABS == ABS0[stack, head]

INV == (pc = 15 => mem[n] /= undef /\ (\A r\in Ref : mem[r]/= undef => mem[r][2] /= n  /\ head/=n)) 
    /\ (pc = 18 => mem[n] /= undef /\ mem[n][1]=v /\ (\A r\in Ref : mem[n] /= undef => mem[r][2] /= n) /\ head /= n)
    /\ (pc=19 => mem[n] /= undef /\ mem[n][1]=v /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= n) /\ head /=n /\ ss /= n)
    /\ (pc=21 => mem[n] /= undef /\ mem[n][1]=v /\ (head=ss => mem[n][2]=ss) /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= n) /\ head /= n /\ ss /= n)
    /\ (pc=30 => ss=head /\ (ss /= null => mem[ss] /= undef))
    /\ (pc=32 => ss /= null /\ mem[ss] /= undef)
    /\ (pc=33 => ss /= null /\ mem[ss] /= undef /\ (ss=head => ssn=mem[ss][2]))
    /\ (pc=35 => ss /= null /\ mem[ss] /= undef /\ (ss=head => lv=mem[ss][1] /\ ssn=mem[ss][2]))
    
       
STATUS == (pc \in 14..21 => in=v ) 
    /\ (pc = 30 => (Len(stack) = 0 => out=empty)) 
    /\ (pc = 31 => (out = empty))
    /\ (pc=36 => out=lv)        
            
AOP == (pc = 21.T => (stack'= <<in>> \o stack))
    /\ (pc = 29 =>  (ss'=null => (Len(stack)=0 => out'=empty /\ stack'=stack) /\ (Len(stack) /= 0 => out'=Head(stack) /\ stack'=Tail(stack)))
        /\ (ss' /= null => stack'=stack /\ out'=out))
    /\ (pc = 35.T => (Len(stack)=0 => out'=empty /\ stack'=stack) /\ (Len(stack) /= 0 => out'=Head(stack) /\ stack'=Tail(stack)))
            
D == (pc \in 29..35 /\ pcq \in 15..21 => ss /=nq /\ ssn /= nq)
        /\ (pc \in {33,35} => mem[ss] /= undef /\ ssn=mem[ss][2])
        /\ (pcq \in {33,35} => mem[ssq] /= undef /\ ssnq=mem[ssq][2])
        /\ (pc=35 => lv=mem[ss][1]) /\ (pcq=35 => lvq=mem[ssq][1])
        /\ (pcq\in 15..21 /\ pc\in 15..21 => n /= nq) /\ (pcq\in 19..21 /\ pc\in 15..21 => n /= ssq) 
        /\ (pc\in 19..21 /\ pcq\in 15..21 => nq /= ss)
        /\ (pcq=21 => mem[nq] /= undef /\ mem[nq][2]=ssq) /\ (pc=21 => mem[n] /= undef /\ mem[n][2]=ss) 
        /\ (pcq\in 29..35 /\ pc\in 15..21 => ssq /=n /\ ssnq /= n)
=============================================================================