---------------------------- MODULE push22T_D----------------------------
EXTENDS Status, FiniteSequences, Naturals
VARIABLES ss, stack, nq, in, lvq, lv, inq, n, out, ssn, head, ssq, pc, mem, ssnq, v, outq, vq, pcq

CONSTANT Ref, T, null, undef, N, empty

ABS0[s\in FiniteSeq(T,N), h\in Ref\union {null}] ==
            (h=null => Len(s)=0) 
            /\ (h /= null => Len(s) /= 0 /\ mem[h] /= undef /\ mem[h][1]=Head(s) /\ ABS0[Tail(s), mem[h][2]])
ABS == ABS0[stack, head]

INV ==  (pc = 22 => (TRUE))
	 /\ (pc = 23 => (TRUE)) 

STATUS ==  (pc = 22 => (TRUE))
	 /\ (pc = 23 => (TRUE)) 

D ==  (pc \in 29..35 /\ pcq \in 15..21 => ss /=nq /\ ssn /= nq)
/\ (pc \in {33,35} => mem[ss] /= undef /\ ssn=mem[ss][2])
/\ (pcq \in {33,35} => mem[ssq] /= undef /\ ssnq=mem[ssq][2])
/\ (pc=35 => lv=mem[ss][1]) /\ (pcq=35 => lvq=mem[ssq][1])
/\ (pcq\in 15..21 /\ pc\in 15..21 => n /= nq) /\ (pcq\in 19..21 /\ pc\in 15..21 => n /= ssq)
/\ (pc\in 19..21 /\ pcq\in 15..21 => nq /= ss)
/\ (pcq=21 => mem[nq] /= undef /\ mem[nq][2]=ssq) /\ (pc=21 => mem[n] /= undef /\ mem[n][2]=ss)
/\ (pcq\in 29..35 /\ pc\in 15..21 => ssq /=n /\ ssnq /= n)

INVq ==  (pcq = 15 => mem[nq] /= undef /\ (\A r\in Ref : mem[r]/= undef => mem[r][2] /= nq  /\ head/=nq))
/\ (pcq = 18 => mem[nq] /= undef /\ mem[nq][1]=vq /\ (\A r\in Ref : mem[nq] /= undef => mem[r][2] /= nq) /\ head /= nq)
/\ (pcq=19 => mem[nq] /= undef /\ mem[nq][1]=vq /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= nq) /\ head /=nq /\ ssq /= nq)
/\ (pcq=21 => mem[nq] /= undef /\ mem[nq][1]=vq /\ (head=ssq => mem[nq][2]=ssq) /\ (\A r\in Ref : mem[r] /= undef => mem[r][2] /= nq) /\ head /= nq /\ ssq /= nq)
/\ (pcq=30 => ssq=head)
/\ (pcq=31 => ssq /= null /\ mem[ssq] /= undef)
/\ (pcq=32 => ssq /= null /\ mem[ssq] /= undef)
/\ (pcq=33 => ssq /= null /\ mem[ssq] /= undef /\ (ssq=head => ssnq=mem[ssq][2]))
/\ (pcq=35 => ssq /= null /\ mem[ssq] /= undef /\ (ssq=head => lvq=mem[ssq][1] /\ ssnq=mem[ssq][2]))

STATUSq ==  (pcq \in 14..21 => inq=vq )
/\ (pcq = 30 => (Len(stack) = 0 => outq=empty))
/\ (pcq = 31 => (outq = empty))
/\ (pcq=36 => outq=lvq)

Init == /\ stack \in FiniteSeq(T, N) /\ head \in Ref \union {null} /\ mem \in [Ref ->(T \X (Ref \union {null})) \union {undef}] /\ ABS /\ ss \in Ref \union {null} /\ pc = 22 /\ v \in T /\ n \in Ref /\ INV /\ in \in T /\ lv = 0  /\ out = 0  /\ ssn = 0  /\ STATUS
 /\ (( pcq = 0 /\ ssq = null /\ vq = 0 /\ nq = null /\ INVq /\ D /\ inq = 0 /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 15 /\ ssq = null /\ vq \in T /\ nq \in Ref /\ INVq /\ D /\ inq \in T /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 16 /\ ssq = null /\ vq \in T /\ nq \in Ref /\ INVq /\ D /\ inq \in T /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 19 /\ ssq \in Ref \union {null} /\ vq \in T /\ nq \in Ref /\ INVq /\ D /\ inq \in T /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 20 /\ ssq \in Ref \union {null} /\ vq \in T /\ nq \in Ref /\ INVq /\ D /\ inq \in T /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 22 /\ ssq \in Ref \union {null} /\ vq \in T /\ nq \in Ref /\ INVq /\ D /\ inq \in T /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 23 /\ ssq \in Ref \union {null} /\ vq \in T /\ nq \in Ref /\ INVq /\ D /\ inq \in T /\ STATUSq /\ lvq = 0 /\ outq = 0 /\ ssnq = null )
\/( pcq = 0 /\ ssq = null /\ lvq = 0 /\ ssnq = null /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 31 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 32 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 33 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 34 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 35 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 37 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )
\/( pcq = 38 /\ ssq \in Ref \union {null} /\ lvq \in T /\ ssnq \in Ref \union {null} /\ INVq /\ D /\ outq = 0 /\ STATUSq /\ inq = 0 /\ vq = 0 /\ nq = null )) 

push22T ==  pc = 22 /\ pc' = 23 /\ head = ss /\ head' = n /\ UNCHANGED<<ss,stack,nq,in,lvq,lv,inq,n,out,ssn,ssq,mem,ssnq,v,outq,vq,pcq>> 

Spec ==  Init /\ [][push22T]_<<ss, stack, nq, in, lvq, lv, inq, n, out, ssn, head, ssq, pc, mem, ssnq, v, outq, vq, pcq>> 

=============================================================================