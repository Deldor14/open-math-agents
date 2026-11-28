# A density obstruction for periodic substitutions in the finite Roth problem

Let \(R(n)\) be the largest size of a subset of an interval of \(n\) consecutive integers containing no nonconstant three-term arithmetic progression. A periodic substitution expands the integer line at a rational rate \(p/q\). If it preserves every finite progression-free input, then under every dilation strictly below two its average output size, over the translations of the input, is at most the input size. This includes dilations below the golden ratio.

## The substitution and its sharp bound

Fix positive integers \(p,q\). Set \(g=\gcd(p,q)\), \(P=p/g\), and \(Q=q/g\). Choose an occupied mask \(D\subseteq\mathbb Z/p\mathbb Z\) and an arbitrary integer label \(f(r)\) for every occupied residue, represented by \(0\le r<p\). The input index assigned to an occupied output position is

\[
F(r+kp)=f(r)+kq \qquad(k\in\mathbb Z).
\]

For an input \(A\), take all occupied positions whose assigned index belongs to \(A\). Assume every finite progression-free input produces a progression-free output. Then

\[
2|D|\le p+g,\qquad p<2q\ \Longrightarrow\ |D|\le q.
\]

For a fixed finite input \(A\), summing output sizes for \(A,A+1,\ldots,A+q-1\) gives exactly \(|D||A|\). Indeed, for each \(r\in D\) the integers \(f(r)+kq\) run once through its label class, and every input element visits that class exactly once over the \(q\) translations. The mean amplification factor is consequently \(|D|/q\). Particular inputs and phases can still give larger gains. An adaptive construction may also exploit the additive structure of an extremal input.

The conclusion also covers constructions which initially offer several input labels at one occupied residue, with an output selected whenever any of its labels belongs to the input. If two candidate labels at \(y\) are \(a\ne b\), use the three outputs \(y-tp,y,y+tp\) and select their labels \(a-tq,b,a+tq\). For sufficiently large positive \(t\), these three labels are strictly increasing and do not form an arithmetic progression. The finite input consisting of these labels produces a forbidden output. Hence universal preservation forces a unique label at every occupied residue.

## Proof

Define the periodic integer height by

\[
H(r)=P f(r)-Q r.
\]

For an occupied integer \(u\), it satisfies \(PF(u)=Qu+H(u\bmod p)\). Take any \(x,y,z\in D\) satisfying \(x+z=2y\pmod p\). Fix an integer representative \(b\) of \(y\), and take arbitrarily large positive \(d\equiv y-x\pmod p\). The integers \(b-d,b,b+d\) have the prescribed residues. Their labels are strictly increasing for sufficiently large \(d\), since \(Q>0\) and the three heights are fixed. If those labels did not form a progression, they would constitute a three-element progression-free input whose output includes \(b-d,b,b+d\). Consequently their labels satisfy the midpoint identity. It follows that

\[
H(x)+H(z)=2H(y).
\]

This argument also applies when two or all three residues coincide. The lifted integer positions and their labels are still distinct.

When \(D\) is nonempty, take \(y\in D\) maximizing \(H\). For every \(x\in I=D\cap(2y-D)\), both \(x\) and \(2y-x\) have height \(H(y)\). On the other hand \(H(x)\equiv-Qx\pmod P\), so coprimality forces every point of this level into one residue class modulo \(P\). A period of length \(gP\) contains exactly \(g\) such positions. Inclusion–exclusion gives

\[
2|D|-p\le |I|\le g.
\]

Reflection is a bijection also for even \(p\). Its fixed points, including the antipodal point when present, are counted once. For the empty mask the estimate is immediate. Finally, if \(p<2q\), then the integer \(P\) satisfies \(P+1\le 2Q\), giving the asserted bound even for an unreduced choice of period.

The bound is attained for every reduced pair \(P=2Q-1\). Take \(D=\{0,\ldots,Q-1\}\) modulo \(P\) and \(F(kP+r)=kQ+r\). In any supported midpoint relation the residue second difference is a multiple of \(P\) of absolute value at most \(2Q-2=P-1\). Both residue indices and period indices therefore satisfy their respective midpoint identities. The assigned labels are strictly increasing on the occupied positions, and every finite input retains exactly its size. Repeating the whole mask and all its label rules \(g\) times gives the corresponding unreduced example.

## A finite window version

Assume directly that the height midpoint identity holds at occupied triples of steps \(d=1,\ldots,s\), with \(2s<p\). At a maximum \(y\), the two positions \(y-d,y+d\) cannot both be occupied unless \(P\mid d\). The pairs belonging to different positive steps are disjoint, so at least \(s-\lfloor s/P\rfloor\) of the \(p\) positions must be vacant. For \(s<P\) this requires at least \(s\) vacancies. The localized hypothesis concerns height identities. For monotone labels it follows from universal preservation on these triples, since equal labels on a nonconstant output progression would already give a forbidden input of at most two elements. Without monotonicity the large-step lifting argument in the preceding proof uses unrestricted integer progressions.

## What the elementary gap estimate proves

For \(k\ge2\), \(m,n\ge1\), put \(h=\lfloor(m-1)/(k-1)\rfloor\) and repeat an optimal subset of \([0,n-1]\) with period \(n+h\). Any nonconstant \(k\)-term progression in a window of \(m\) consecutive positions has positive step at most \(h\), after reversing if necessary. It cannot cross the \(h\) consecutive vacant positions between two copies. Averaging window sizes over a period therefore gives

\[
(n+h)R_k(m)\ge mR_k(n).
\]

For three terms, the entire family of these inequalities follows from monotonicity, interval subadditivity and the sharp one-site gluing inequality

\[
R(a)+R(b)\le R(2a+b-1) \qquad(1\le b\le a).
\]

To see this, first suppose \(1\le r<m\), with \(h=\lfloor(m-1)/2\rfloor\). We claim \(mR(r)\le(r+h)R(m)\). If \(m\le r+h\), monotonicity gives the claim. Otherwise \(m\ge2r\). If \(m\ge3r-1\), use \(R(m)\ge2R(r)\) and \(m\le2(r+h)\).

For the remaining case put \(L=2r-1\) and \(x=m-L\), so \(1\le x\le r\). Gluing gives \(R(m)\ge R(r)+R(x)\). Splitting the shorter interval into pieces gives \(R(r)\le \lceil r/x\rceil R(x)\), with \(x\lceil r/x\rceil\le r+x-1\le L\). Hence

\[
mR(r)=LR(r)+xR(r)\le L\bigl(R(r)+R(x)\bigr)\le LR(m)\le(r+h)R(m).
\]

Finally write any \(n=jm+r\), \(0\le r<m\), and apply subadditivity to get \(R(n)\le jR(m)+R(r)\). Multiplication by \(m\) and the bound just proved give exactly \(mR(n)\le(n+h)R(m)\). The case \(r=0\) follows from \(R(0)=0\). Thus adding all the single-gap inequalities to the earlier interval inequalities gives no further consequence, including when smaller windows are sampled from a longer extremal set. This is a statement about the strength of the inequalities. The actual behavior below the golden ratio is a separate question.

The calculation also explains another admissible period for intact blocks. An interval of length \(r\) embeds in the cyclic group of order \(L=2r-1\) with every midpoint identity preserved, since its residue second differences have absolute value at most \(2r-2\). Repetition therefore gives \(LR(m)\ge mR(r)\) for \(m\le2L\). For \(L<m<L+r\) the estimate follows from the preceding gluing argument, and for \(L+r\le m\le2L\) it follows from \(R(m)\ge2R(r)\).

## Formal verification

The companion `PeriodicSubstitution.lean` gives a standalone Lean 4.33.1 proof against Mathlib. The theorem `mask_bound` handles finite midpoint-preserving heights. The theorem `universal_midpoint` derives every cyclic midpoint identity from preservation of finite inputs on the integer line, and `universal_no_gain` gives the resulting bound below dilation two. The theorem `gap_redundant` derives the sliding-window inequality for any nondecreasing subadditive sequence satisfying the displayed gluing bound. The theorem `roth_gap` specializes this derivation to Mathlib’s `rothNumberNat`. The copied gluing proof is credited to @Deldor14 in [the prior interpolation formalization by @eilamc14](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean). Credit for this note and formalization belongs to @Deldor14.
