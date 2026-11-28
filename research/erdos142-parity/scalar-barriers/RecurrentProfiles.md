# Recurring Fibonacci plateaus with the known density decay and every digit bound

Let R(m) be the true largest size of a three-term-progression-free subset of
[1,m], and λ=987/610. There is a nondecreasing **integer sequence** H,
starting at zero with successive increments in {0,1}, such that for all
nonnegative integers a,b and all positive m,n,

    H(a+b) ≤ H(a)+H(b),
    H(a)+H(b) ≤ H(a+b+max(a,b)−1)     if a,b≥1,
    R(m) H(n) ≤ H((2m−1)n).

Nevertheless liminf H(floor(λn))/H(n)=1. In fact we can impose

    log(n/H(n)) = Θ((log n)^(1/6) / log log n).

There is also a continuous version with exact plateaus [610Nᵢ,987Nᵢ] at
infinitely many integer scales Nᵢ, satisfying the same subadditivity and
digit inequalities and continuous gluing at a+b+max(a,b).
These countermodels address the scalar approach to Erdős #142.
They do not describe the growth of R itself. The constants in the density
estimate are existential. The upper-bound input is [Raghavan, 2026,
Theorem 1.1](https://arxiv.org/abs/2603.27045). With the exponent 1/9 of
[Bloom and Sisask](https://arxiv.org/abs/2309.02353), the simpler choice
Nᵢ=B^(i⁹) gives log(n/H(n))=Θ((log n)^(1/9)).

## A profile which agrees with straight lines at both ends

Use the unnormalized continuous G of [the Fibonacci barrier](FibonacciBarrier.md)
at s=7. Put M=128, W=987, β=M/W and T=620W. Its successive linear pieces
have slopes zero or one, G(x+W)=G(x)+M, and βx≤G(x)≤min(x,βx+M).
The last upper bound follows by reducing to a single period.
Define P(x)=G(x) for x≤T and P(x)=βx for x≥T. The definitions agree.
P(x)=x on [0,1], P=128 on [610,987], and βx≤P(x)≤x.

Subadditivity persists when the sum crosses T because each input is at
least β times its argument. For 0≤x≤y, if z=x+2y≥T then y≥2W, hence
P(x)+P(y)≤β(x+y)+2M≤βz. Below T the old gluing applies.

For L=2m−1, r=R(m), consider Lx≥T. The finite barrier proves
Wr≤ML for every m≥155. For 2≤m<155, L≤307 gives x>2W and
P(x)≤(3/2)βx, while r≤m implies L/r≥3/2. Thus rP(x)≤βLx.
For Lx<T use G, and m=1 is equality.

There exists δ in (0,1] with P(2x)≥(1+δ)P(x) for all x≥0.
Indeed, any positive-level plateau of G has endpoints A(j)+1 and A(j+1),
with A the binary capacity. The carry inequality with i=0 shows
A(j+1)≤2A(j)+1<2(A(j)+1). No such interval contains both x and 2x.
The truncation adds no plateau. On a compact middle range use continuity
and positivity; near zero and beyond T the ratio is two.
The functions Pθ=(1−θ)P+θx, 0≤θ≤1, share this doubling gain, the digit
bounds, gluing, and subadditivity. Their slopes at the right are
κθ=β+(1−β)θ. Each is nondecreasing and 1-Lipschitz.

## Choosing the scales

Write h(t)=(t log(e+t))⁶. Let Nᵢ=ceil(exp(K h(i))) for i≥1, with one
large constant K to be chosen. The intervals [Nᵢ,TNᵢ] are disjoint.
We use the following consequences of increasing K.

* The consecutive ratios Nᵢ/Nᵢ₋₁ (i≥2) can be made uniformly larger
  than any prescribed constant. They tend to infinity.
* If [x,Lx] meets h₀≥2 of these intervals, L/R(m)≥2β^(−h₀)
  whenever L=2m−1. To verify this, let j be the first interval met,
  so L≥Nⱼ₊ₕ₀₋₁/(TNⱼ). The function h is superadditive because h(t)/t
  is increasing. Thus log m≥K h(h₀−1)−log(4T). From Raghavan's bound
  one has L/R(m)≥C⁻¹ exp(c v^(1/6)/log(e+v)) for v=log m sufficiently
  large. At v≥K h(l)−log(4T), l=h₀−1≥1, the quantity in that exponent
  is bounded below by a constant times K^(1/6)l/(1+log K), uniformly in l.
  Indeed v^(1/6) is at least a constant times K^(1/6)l log(e+l) at the
  lower endpoint, log(e+v) there is at most a constant times
  (1+log K) log(e+l), and their ratio is eventually increasing.
  Choosing K large proves the claim for every h₀ simultaneously.

## Joining the profiles at widely separated sizes

Take θᵢ=0 for the continuous example and θᵢ=2^(−i) for the integer example.
Write α₀=1 and αᵢ=αᵢ₋₁κθᵢ. The ratio αᵢ/βⁱ lies between 1 and a fixed
finite constant, since the θᵢ are summable in both cases.
On [Nᵢ,TNᵢ] define

    f(x)=αᵢ₋₁ Nᵢ Pθᵢ(x/Nᵢ).

Between intervals put f(x)=αᵢx after the i-th interval and f(x)=x before
the first. This agrees at every boundary. The resulting f is nondecreasing
and 1-Lipschitz. On the i-th interval its density f(x)/x is between αᵢ
and αᵢ₋₁. Thus for Nᵢ≤x<Nᵢ₊₁, log(x/f(x))=i log(1/β)+O(1).
Since log x is between K h(i)+O(1) and K h(i+1)+O(1), the density
decay asserted above follows. More precisely f(x) is within constant factors
of x β^(h⁻¹(log(x)/K)), a smoothly varying reference function.

Here are the checks across different intervals. For 0<x≤y and
z=x+y or z=x+2y, choose the last i with Nᵢ≤z. If none exists, all
values are in the initial linear region. Otherwise y≥Nᵢ/3 and [y,z]
agrees with the i-th copy extended linearly on both sides, since
Nᵢ/3>TNᵢ₋₁ for i≥2. The value at x agrees too unless x<TNᵢ₋₁.
In that earlier region the actual f(x) is at least αᵢ₋₁x, its value
in the extended i-th copy. Thus subadditivity always transfers.

For gluing in the earlier region,
f(x)≤αᵢ₋₁TNᵢ₋₁, while f(y)≥βαᵢ₋₁Nᵢ/3.
Choose K so this gives f(x)≤δ f(y)/2. Both y and 2y use the extended
i-th copy. Hence f(z)≥f(2y)≥f(x)+f(y)+δ f(y)/2.
In the single-copy case there is at least the extra gluing slack
αᵢ₋₁θᵢy, contributed by the linear summand.

For the digit bound, an interval [x,Lx] crossing no transition uses a
single linear function. If it meets just the i-th transition, the full
interval agrees with its linearly extended copy. If it meets h₀≥2,
both endpoint densities give f(Lx)/f(x)≥β^h₀ L≥2R(m).
With θᵢ=0 the promised exact plateaus now follow.

## Integer rounding and the one-site saving

For θᵢ=2^(−i), set H(n)=ceil(f(n)). Since f is 1-Lipschitz and nondecreasing,
H has increments zero or one. Subadditivity passes to ceilings. In the
gluing inequality the ceiling on each input costs less than one, and moving
the output from z to z−1 costs at most one. It therefore suffices to have
three units of slack in the continuous inequality. When Nᵢ≤z, in the
single-copy case the slack is at least αᵢ₋₁θᵢNᵢ/3. In the earlier-region
case it is at least δβαᵢ₋₁Nᵢ/6. Both exceed three after increasing K,
uniformly in i since αᵢ₋₁≥β^(i−1). Before N₁, H(n)=n and
a+b≤a+b+max(a,b)−1 whenever a,b≥1.

For integer n≥1 and m≥2 write r=R(m) and L=2m−1. If [n,Ln] meets
one transition, the residual surplus from the linear summand is at least
αᵢ₋₁θᵢ(L−r)n. Since L−r≥r/2, this pays for r units of rounding when
αᵢ₋₁θᵢn≥2. For i≥2 one has n≥TNᵢ₋₁, so a single large K suffices.
For i=1 either n≥N₁ or f(n)=n exactly and there is no input rounding.
When no transitions are met, L/r≥3/2 absorbs the ceiling if f(n)≥2;
all smaller integer values are in the initial linear region. For multiple
transitions the factor two suffices since f(n)≥1. Thus rH(n)≤H(Ln)
exactly, including the separate identity for m=1.

At nᵢ=610Nᵢ the dilated argument is exactly 987Nᵢ. The ratio of the
unrounded values is

    ((1−θᵢ)128+987θᵢ)/((1−θᵢ)128+610θᵢ) → 1.

The denominator before normalization by αᵢ₋₁Nᵢ is bounded below by 128,
and αᵢ₋₁Nᵢ tends to infinity. The ceilings preserve the limiting ratio.
Monotonicity supplies the reverse bound one on the liminf. Rounding also
preserves the density estimate. The argument gives a written counterexample
to the sufficiency of these scalar conditions, leaving the true extremal
asymptotic and the prize question open.

ProfileTruncation.lean checks the truncation argument and transfers the digital
inequality to the actual mathlib Roth numbers under the stated tail bound.
For ManyBlockLimit.lean put the module LongGluing from the adjacent long-growth
directory on LEAN_PATH.
