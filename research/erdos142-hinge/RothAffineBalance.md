# Simultaneous balance in residue classes and intervals for progression-free sets

For a positive integer $n$, let $M=R(n)$ be the maximum size of a three-term-progression-free subset of $[0,n)$. Take a prime $p\ge 2n-1$ with $p\ge n$, write $\mu=nM/p$, and assume $\mu>2$. Take a nonempty finite list of partitions of $[0,n)$ into nonempty cells, of total cell count $K$ with repetitions counted. There exists a progression-free set $B\subset[0,n)$ such that
$$\big||B|-\mu\big|\le\sqrt{2\mu},\qquad
\sum_{\mathcal P}\chi^2(P_{B,\mathcal P},P_{U,\mathcal P})
\le \frac{2\mu K}{(\mu-\sqrt{2\mu})^2}.\tag{1}$$
Here $P_{B,\mathcal P}$ and $P_{U,\mathcal P}$ are the cell probabilities of a uniform point of $B$ and $[0,n)$, respectively. For distributions $P,Q$, $\chi^2(P,Q)=\sum_C(P_C-Q_C)^2/Q_C$. The estimate also works with $M$ equal to the size of any supplied progression-free seed in $[0,n)$.

## Proof

Embed a seed of size $M$ in $\mathbb F_p$. An integer second difference in $[0,n)$ has absolute value at most $2n-2<p$, so the seed is free in the field. Take its image under a uniformly chosen map $x\mapsto ax+b$ with $a\ne0$, and let $B$ consist of the representatives in $[0,n)$. The resulting set is free. Put $X_C=|B\cap C|$ and $u_C=|C|/n$. Every image point is uniform and every pair of distinct image points is uniform on ordered distinct field points. Expanding the second moment therefore gives
$$\mathbf E X_C=\mu u_C,\qquad
\operatorname{Var}(X_C)=\frac{M(p-M)}{p-1}\frac{|C|}{p}
\left(1-\frac{|C|}{p}\right)\le\mu u_C.$$
Applying this to $C=[0,n)$ gives $\operatorname{Var}(|B|)\le\mu$. Choose a map for which
$$\frac{(|B|-\mu)^2}{\mu}
+\frac{1}{K\mu}\sum_{\mathcal P}\sum_{C\in\mathcal P}
\frac{(X_C-\mu u_C)^2}{u_C}\le2.$$
Such a map exists by the two expectation bounds. For each partition the weighted sum of squares in the display is minimized, as a function of the center replacing $\mu$, at $|B|=\sum_C X_C$. Substituting this center, dividing by $|B|^2$, and using $|B|\ge\mu-\sqrt{2\mu}>0$ gives (1).

## Consequence for binary digits

Take $n=2^d$ and the least prime $p\ge2n-1$. By the prime number theorem $p=(2+o(1))n$, so one keeps $(1/2+o(1))M$ points. At each cut $j$, the low and high digit partitions consist of the residue classes modulo $2^j$ and the aligned intervals of length $2^j$. Include both partitions at every $L\le j\le d-L$. Their total number of cells is less than $4n/2^L$. With
$$L=\lceil\log_2(n/M)\rceil+g(d),$$
where $g(d)$ is any positive integer function tending to infinity with $L\le d/2$, one has $K=o(M)$. Equation (1) makes the sum of the chi-square divergences $o(1)$, uniformly over these cuts. Relative entropy is bounded by chi-square divergence by $\log x\le x-1$. For the uniform point $X$ of this single set $B$ one has exactly
$$I(X\bmod 2^j;\lfloor X/2^j\rfloor)
=\log(n/|B|)-D_{\rm KL}(P_{\rm low}\|U_{\rm low})
-D_{\rm KL}(P_{\rm high}\|U_{\rm high}).$$
Thus at every central cut the information differs from its upper bound $\log(n/|B|)$ by $o(1)$, and $\log(n/|B|)=\log(n/M)+\log2+o(1)$. In particular the real rank of the zero-one occupancy matrix is at least $(1-o(1))n/|B|$ throughout these cuts by the normalized-matrix bound. At least a $(1-o(1))$ fraction of the low residues are occupied, since the uniform mass of empty cells is bounded by chi-square divergence. Covering the occupied low residues with actual columns therefore takes at least $(1-o(1))2^j/R(2^j)$ columns.

For a marginal with $q$ equiprobable cells, any set of $m$ points has entropy at most $\log m$, so its divergence from uniform is at least $\log(q/m)$. In particular the smaller side of the cut must have size at least $(1-o(1))n/m$ for both divergences to tend to zero. The construction above attains balance with the smaller side exceeding $n/M$ by an arbitrarily slowly diverging factor. Its conclusion is existential. The characterization of the exponent in the companion article concerns the minimum over sets. [Digit information and its exponent](RothDigitInformation.md)

## Verification

Lean verifies the exact covariance identity for every centered real test over a finite field, simultaneous selection for a finite list of weighted centered tests, the centered-indicator moment, and preservation of progression-freeness under the affine image and crop. Formula (1) and its entropy consequences are deduced in writing above. The exact-arithmetic verifier checks 8,014 affine maps and 50 second-moment identities. [Variance](RothAffineVariance.lean) · [Selection](RothAffineSelection.lean) · [Crop](RothAffineCrop.lean) · [Finite verifier](check_roth_digit_scales.py)
