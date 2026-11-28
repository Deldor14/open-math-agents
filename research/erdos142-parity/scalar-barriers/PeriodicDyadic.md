# Exact density of universal periodic substitutions through dilation four

For Erdős problem 142, write $R_3(n)$ for the maximum size of a subset of $n$ consecutive integers with no nonconstant three-term arithmetic progression. Consider a periodic rule that converts every finite progression-free input into a progression-free output. In the class defined below, the exact maximum mean output size per input element, at any reduced rational dilation $0<P/Q\le4$, is

$$
\frac{\lceil P/2\rceil}{Q}.
$$

In particular, every rule at dilation $P/Q\le2$ has mean at most one. Gains occur at $2+1/Q$ for every positive $Q$, with mean $1+1/Q$. Below $13/8$, all reduced ratios other than $1$ and $3/2$ have mean at most $6/7$. This constant is attained at $11/7$, below the golden ratio. These conclusions concern the average over input translations. A choice of phase or rule tailored to an extremal input can behave differently.

## Periodic rules and mean size

Fix positive integers $g,P,Q$, with $P,Q$ coprime. Take an occupied mask $D\subseteq\mathbb Z/(gP)\mathbb Z$ and an integer label $f(r)$ for every $r\in D$, using representatives $0\le r<gP$. Position $r+kgP$ receives the input index $F(r+kgP)=f(r)+kgQ$. The output on input $A$ consists of the occupied positions with $F(x)\in A$. A rule is universal if every finite three-term-progression-free input gives a three-term-progression-free output.

For fixed finite $A$, each $r\in D$ supplies exactly $|A|$ positions in total over the $gQ$ translated inputs $A+t$ with $0\le t<gQ$. Thus the mean is $|A||D|/(gQ)$, even when several positions share an input label.

The companion proof for periodic substitutions introduces the integer height $H(r)=P f(r)-Qr$. It shows that on occupied cyclic midpoints $x+z=2y$ one has $H(x)+H(z)=2H(y)$. Indeed the residues lift to arbitrarily widely spaced integer progressions. Their labels are then strictly increasing. If those labels failed the midpoint identity, those three labels alone would give a finite progression-free input containing an output progression.

At a maximum of $H$ over $D$, the reflected intersection $D\cap(2y-D)$ has size at least $2|D|-gP$ and consists entirely of points of maximal height. Equal heights imply equal residues modulo $P$, so this intersection has at most $g$ elements. For odd $P$ this gives $|D|\le g(P+1)/2$.

## The even numerator

A midpoint-preserving integer height on a strict majority of a cyclic group of order $2^a$ is constant on that majority. For $a=0$ the group is a singleton. For the induction step, at least one parity class contains a strict majority of its $2^{a-1}$ sites. On that class, rescaling its positions by a factor of two gives the induction hypothesis. All its occupied points have one height, say $c$. For each occupied $y$ in the whole group, reflection about $y$ preserves the chosen parity class. Its occupied subset and its reflection must meet there because both have more than half of its sites. There are therefore occupied $x,z$ in that class with $x+z=2y$. The midpoint identity gives $2H(y)=2c$. This argument includes $x=z$ and the antipodal fixed point of a reflection.

Now suppose $P$ is even. Write $gP=s2^a$, where $s$ is odd and $a\ge1$. If more than half the sites in the period were occupied, at least one class $r\bmod s$ would contain a strict majority of its $2^a$ sites. Writing its positions as $r+si$, we can apply the dyadic lemma to their indices $i$. The height on all its occupied points would then be constant. Since $s$ is odd, the class contains equally many even and odd representatives, and a strict majority contains both. But equal heights imply equal residues modulo the even integer $P$. This contradiction gives $2|D|\le gP$. Combining both parities proves

$$
|D|\le g\lceil P/2\rceil
$$

for every positive $P,Q$, including periods displayed with an arbitrary common multiple $g$.

## Attainment

Take $L=\lceil P/2\rceil$. In each primitive period use the $L$ consecutive residues $0\le r<L$, with labels $F(iP+r)=iQ+r$ for every integer $i$. Repeating this rule $g$ times gives exactly $gL$ occupied sites.

Write an occupied output progression as $iP+r,jP+s,kP+t$ in increasing order. The congruence $r+t=2s\pmod P$ has $|r+t-2s|\le2(L-1)<P$. It follows that $r+t=2s$ as integers and $i+k=2j$. The labels form an arithmetic progression. If its common difference were zero, we would have $Q(j-i)=r-s$. A nonzero $j-i$ would imply $|t-r|=2|s-r|\ge2Q$, whereas $P\le4Q$ gives $L-1<2Q$. If $j=i$, zero label difference also gives $s=r$, contrary to the distinct output positions. The labels therefore form a nonconstant progression, which a progression-free input excludes. This proves universality and attains the upper bound.

For the loss below $13/8$, the arithmetic is finite. If $8P<13Q$ and $7\lceil P/2\rceil>6Q$, then $Q\le11$, using $2\lceil P/2\rceil\le P+1$. Checking $1\le Q\le11$ leaves only $(P,Q)=(1,1),(3,2)$. At $(11,7)$, the six occupied residues attain mean $6/7$. The next boundary $13/8$ has mean $7/8$, which exceeds $6/7$.

## Lean verification

The standalone source `PeriodicDyadic.lean` imports Mathlib. Its theorem `optimal_universal_mask` gives the exact maximum and constructs a universal mask of that size for every $P\le4Q$. The theorem `universal_no_gain_closed` includes dilation exactly two. The theorem `below_thirteen_eighths` gives the uniform loss and both exceptional pairs. The intermediate theorem `dyadic_majority_height` applies to any integer height satisfying all occupied cyclic midpoint identities. Eight kernel audits report only `propext`, `Classical.choice`, and `Quot.sound`. Credit for this note and formalization belongs to @Deldor14.
