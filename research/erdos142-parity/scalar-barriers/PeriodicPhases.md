# Adaptive phases of a periodic substitution on extremal Roth sets

Write $R(N)$ for the largest size of a three-term-progression-free subset of $[0,N)$. Consider a periodic coding with output period $p$, input period $q$, mask $D\subseteq\mathbb Z/p\mathbb Z$, and integer labels $f(r)$. Its occupied output position $r+kp$ uses input index $f(r)+kq$. An input translation by $s$ replaces the finite input $A$ with $A+s$.

Fix any positive period budget $q_{\max}(N)$ satisfying $\log q_{\max}(N)=o(\sqrt{\log N})$. There is a set of observation lengths $N$ of logarithmic density one on which, uniformly over every free input $A\subseteq[0,N)$, every coding with $q\le q_{\max}(N)$, and every integer translation $s$,

$$
|\mathrm{output}(A+s)|\le(1+o(1))\,\frac{|D|}{q}R(N).
$$

Summing output sizes over all $q$ phases gives exactly $|A||D|$. For an extremal input, the best phase therefore retains between $|D|R(N)/q$ and $(1+o(1))|D|R(N)/q$ output points. This makes the constant $6/7$ below sharp on these lengths, since the coding at dilation $11/7$ has six occupied residues.

The estimate also holds for independent periodic rules on a partition of the input, using the sum of their input periods as the budget. This extension is proved below. The supremum in the single-rule case permits choosing the mask, labels, and translation after seeing $A$. The estimate counts the entire output on the integer line. In particular it applies to every maximizing input on these lengths. It also bounds the output relative to $|A|$ when $|A|=(1-o(1))R(N)$.

For a universal coding, write $p=gP,\ q=gQ$ in lowest terms. The companion theorem on periodic substitutions gives $|D|\le g\lceil P/2\rceil$. Consequently, even an adaptive choice of universal codings with dilation at most two has output size at most $(1+o(1))R(N)$ at these lengths. For dilation below $13/8$, excluding $1$ and $3/2$, the bound becomes $(6/7+o(1))R(N)$. For example, the period budget may be $\exp((\log N)^{1/3})$. The conclusion puts a limit on this proof method for Erdős 142. The true value of $R(\lfloor (p/q)N\rfloor)$ can be larger.

## Finite bounds

For $j,M\ge0$ let $L=2^j$, $K=2^M$, and $T=KL$. Suppose

$$
R(T)\ge e^{-\delta}K R(L).
$$

For $N=T$, any output $O$ of the coding satisfies

$$
q|O|\le |D|(1+q/K)e^\delta R(T).
$$

For every $N\le T$ there is a finer bound

$$
[N-L-(1-e^{-\delta})T]\,q|O|
\ \le\ |D|(N+qL)R(N).
$$

To see the counting estimate, fix an output residue $r\in D$. Its input coordinates lie in a single class modulo $q$, even after translation. Dividing that class into consecutive segments of $L$ positions gives at most $\lceil N/(qL)\rceil R(L)$ input elements. Inside each segment, division by $q$ after subtracting the residue converts the elements into a free subset of an interval of length $L$. Every contributing input coordinate lifts to a unique output in the residue $r$. Therefore

$$
Lq|O|\le |D|(N+qL)R(L).
$$

Interval subadditivity and the same rounding bound give

$$
L R(T)\le L R(N)+(T-N+L)R(L).
$$

The regularity hypothesis yields $[N-L-(1-e^{-\delta})T]R(L)\le L R(N)$. Combining the two inequalities gives the claimed intermediate estimate, including when the coefficient in square brackets is nonpositive.

## Independent choices on many input intervals

Let the input intervals have lengths $N_i$ with $\sum_iN_i\le N$. The intervals may come from a partition of the observed input chosen after inspection. In each interval choose a separate rule, phase and output placement, with input period $q_i$ and $|D_i|/q_i\le\rho$. Local inputs need only be progression-free. If $O$ is the union of their output sets, with any output collisions, the rounded counting estimate gives

$$
L|O|\le \rho\left(N+L\sum_iq_i\right)R(L).
$$

Indeed $|O|\le\sum_i|O_i|$ and $L|O_i|\le \rho(N_i+q_iL)R(L)$. Moving an individual output set leaves its size unchanged. In particular the estimate applies if the choices between blocks also ensure that their assembled output stays progression-free.

Writing $H=\sum_iq_i$, combination with the finite regularity estimate gives

$$
[N-L-(1-e^{-\delta})T]\,|O|\le \rho(N+HL)R(N).
$$

Thus the same logarithmic-density-one set works for all partitions and rules for which $H\le q_{\max}(N)$. The estimates $(1+o(1))R(N)$ at dilation at most two and $(6/7+o(1))R(N)$ below $13/8$ apply to the assembled output whenever every component obeys the respective dilation condition, including the two exclusions for the second bound. This allows the number, length, rule and phase of the blocks to grow or vary with the observation length and input, subject to the two displayed total budgets.

## Counting exceptional dyadic windows

Set $d_j=j\log 2-\log R(2^j)$. Subadditivity gives $d_{j+1}\ge d_j\ge0$, and Behrend's lower bound, in the explicit version in Mathlib, gives $d_j\le4\sqrt{j\log2}$. For any positive $\delta$ the number of $j<J$ satisfying $d_{j+M}-d_j>\delta$ is at most

$$
\frac{4M\sqrt{(J+M)\log 2}}{\delta}.
$$

Indeed the total of the window increments is the sum of the last $M$ terms $d_{J+i}$ minus the sum of the first $M$ terms $d_i$, for $0\le i<M$. All increments are nonnegative. Every other $j$ satisfies the finite regularity hypothesis. [Behrend’s lower bound in the verified Mathlib revision](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Combinatorics/Additive/AP/Three/Behrend.lean#L481)

## From regular windows to lengths of logarithmic density one

Group the dyadic exponents $t$ into blocks $J\le t<2J$, with $J$ successively a power of two. For each block let $h_J$ be the largest value of $\log_2 q_{\max}(N)$ over $2^{J-1}\le N<2^{2J}$. The budget assumption gives $h_J=o(\sqrt J)$. Choose an integer $M\ge\max(2h_J,J^{1/4})$ with $M=o(\sqrt J)$, and put $\delta=(M/\sqrt J)^{1/2}$. The number of exceptional $t$ in the block, using $j=t-M$ in the finite estimate, is $O(M\sqrt{J}/\delta)=o(J)$. The unexceptional exponents together have natural density one.

For such an exponent take $T=2^t$, $L=T/K$ and any integer $T/2\le N<T$. Here $q/K\le2^{-M/2}$, and the relative factor in the intermediate estimate is bounded by

$$
\frac{N+qL}{N-L-(1-e^{-\delta})T}
\ \le\ \frac{1+2q/K}{1-2/K-2(1-e^{-\delta})}
\ =1+o(1).
$$

The denominator is positive for all sufficiently large $J$. Each dyadic shell has bounded logarithmic weight $\sum_{T/2\le N<T}1/N$, tending to $\log 2$. Removing the shells with exceptional exponents therefore removes zero logarithmic density. The resulting statement is uniform over all the allowed codings and phases.

## Verification and attribution

The standalone Lean source is `PeriodicPhases.lean`. The theorem `blockwise_output` proves the bound with the sum of the periods. Its theorems `regular_window_output` and `regular_interval_output` give the two finite bounds on arbitrary actual output positions. The theorem `window_count` gives the explicit exceptional-window count. The theorems `phase_sum` and `realize_phase` give the mean identity and its realization by actual integer outputs. The passage from these finite bounds to logarithmic density one is proved above. The exceptional-window proof extends the single-step telescoping estimate in the companion `RegularScales.lean`. Credit for the note and formalization belongs to @Deldor14.
