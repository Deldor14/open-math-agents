# Matching any finite initial segment of the true Roth numbers

For every prescribed integer p≥1 the integer countermodel of
[the recurrent profile theorem](RecurrentProfiles.md) can be chosen to satisfy

    H(n)=R(n) for 0≤n≤p,              H(n)≥R(n) for every n≥0.

It still has increments zero or one, is subadditive, satisfies the sharp
one-site gluing and all genuine interval digit-product inequalities, has
log(n/H(n)) of order (log n)^(1/6)/log log n, and satisfies
liminf H(floor((987/610)n))/H(n)=1. Even finitely many prescribed exact
Roth values and a global majorant condition do not remove this obstruction
to a proof by scalar inequalities. Here p is fixed before H is constructed.

## An initial extension with a linear tail

Put J(n)=ceil(n/p) and B(n)=max(R(n),J(n)). It agrees with R up to p, and
with J from some finite index onwards by Roth's theorem R(n)=o(n).
The maximum of two nondecreasing, subadditive sequences with increments
zero or one has all three properties. It also vanishes at zero.

For 1≤a≤b consider the sharp gluing bound B(a)+B(b)≤B(a+2b−1).
If B takes the R value on both inputs, use the true R inequality. In the
following cases say the line wins only when J is strictly greater than R.
If the line wins at b alone then R(a)≤R(b)≤J(b)−1, giving an upper
bound 2J(b)−1≤J(2b). If it wins at a alone then pR(a)<a.
Partitioning into intervals of length a gives
pR(b)≤p ceil(b/a)R(a)<a ceil(b/a)≤b+a−1≤2b−1.
Thus J(a)+R(b)≤J(a+2b−1). If it wins at both then b>p and
J(a)+J(b)≤J(a+b+p−1)≤J(a+2b−1).

Let r=R(m), L=2m−1. For the true-R branch at n use the ordinary digit
inequality. On the other branch n>p and j=J(n)≥2. When m≥2,
L(j−1)≥mj−1 because (m−1)(j−2)≥0. Now n/p>j−1 implies
J(Ln)≥mj≥rj. The m=1 case is the identity.

## Switching to a sequence with recurrent near-plateaus

Fix S≥4p so that B(n)=J(n) for n>S. In the integer construction of the
recurrent profile theorem keep θᵢ=2⁻ⁱ and increase the separation parameter
K, with p and S fixed, before defining the transition points Nᵢ.
Replace the model by

    H(n)=B(n)       for n<N₁,
    H(n)=ceil(f(n)/p) for n≥N₁.

For S<n<N₁ the definitions agree. Choose N₁>3S+3. This gives the
original monotonicity and unit-increment bound across the join. Subadditivity
below N₁ follows from B. Above N₁ it follows from ceil(f/p), since the
modified input values can only have increased before the join.

In the sharp gluing argument put z=a+2b with a≤b. If z<N₁ use B.
Otherwise b≥Nᵢ/3, where i is the last transition starting no later than z,
and z−1>S. For a>S the proof of the recurrent profile theorem applies
unchanged after dividing its gluing surpluses by p: their uniform lower
bounds still exceed 3 by increasing K. For a≤S we have H(a)≤S,
while f(2b)≥(1+δ)f(b), since b and 2b use the same extended profile.
Choose K so δf(b)/p≥S+3 uniformly in i. Then the loss of one site and
both rounding errors are absorbed. The conditions follow from
f(b)≥βⁱNᵢ/3 with β=128/987.

If Ln<N₁ use the digit inequality for B. When Ln≥N₁ and n>S, apply
the recurrent-profile digit proof to f/p. In a single transition the
rounding condition is θᵢαᵢ₋₁ n≥2p. For i≥2 this follows from
n≥TNᵢ₋₁ by choosing K large, and for i=1 use n>S≥4p, θ₁=1/2.
With no transition the linear gain L/r≥3/2 suffices once the input exceeds
two. In this range f(n)/p≥2, since n>S and the function is increasing.
Multiple transitions give the same factor two as before.

It remains to check bounded inputs n≤S going all the way to a large
output. With i the last transition starting by Ln we have
L≥Nᵢ/S and m≥Nᵢ/(2S). Raghavan's bound and the choice
log Nᵢ≈K(i log(e+i))⁶ permit R(m)/L≤βⁱ/p uniformly for these m and i.
Indeed the exponent divided by i tends uniformly to infinity as K grows,
by the estimate in the recurrent-profile proof with 2S in place of 4T.
Since H(n)≤n and f(Ln)≥βⁱLn, the required inequality follows.

Finally the same bound, now at n≥Nᵢ, gives R(n)/n≤βⁱ/p for every
Nᵢ≤n<Nᵢ₊₁. Thus H majorizes R on the entire tail as well as on the
initial segment. Multiplying f by 1/p changes log(n/H(n)) by only a
bounded term. Since αᵢ₋₁Nᵢ/p tends to infinity, rounding retains the
limiting ratio one at the lengths 610Nᵢ exactly as before. Constants
and the finite joining length can depend on the prescribed prefix p.

## Verification

`FinitePrefix.lean` checks the initial extension, including its sharp gluing and digit inequalities, and derives the eventual ceiling formula from the Roth theorem in mathlib. The splice to infinitely many near-plateaus and the global comparison use the written estimates above.
