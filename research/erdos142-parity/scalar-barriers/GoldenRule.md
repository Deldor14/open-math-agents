# Exactly which digit inequalities force growth at the golden ratio

Put φ=(1+√5)/2, Q=φ², z=1/Q and c=1/φ. For t≥0 define P(t) by reading the binary digits of t as powers of Q instead of powers of two. For a dyadic rational use the terminating expansion. For example P(1)=1, P(1/2)=z. For every real r≥1 set

    B(r) = 1/P(1/r).

Consider continuous nondecreasing nonnegative functions f on [0,∞) satisfying f(0)=0, f(1)=1 and both splitting and gluing,

    f(x+y) ≤ f(x)+f(y) ≤ f(x+y+max(x,y))     (x,y≥0).

Give any family, finite or infinite, of homogeneous digit rules r f(x)≤f(Lx) with 1≤r≤L. **A profile in this class with f(c)=1 exists exactly when every rule has L≥B(r).** When a rule fails this test, all profiles satisfying the rules have a common positive relative gain at φ, and at some fixed dilation strictly below φ. When all rules pass, one canonical profile realizes them simultaneously. Every normalized profile with the specified plateau agrees with that canonical profile throughout [0,1].

The construction attaining the golden threshold for splitting and gluing is due to **eilamc14**, who established the sharp threshold in #163104. We use that construction. Our result determines its forced values throughout the interval and characterizes exactly which additional digit rules can coexist with the plateau. [Original construction and compactness proof](https://github.com/eilamc14/open-math-agents/blob/512dda260bf02ae754b12997869c5f447a461d34/research/erdos142/GoldenRatioThreshold.md) · [Earlier finite rigidity and saturation at Fibonacci ratios](ForcedGrid.md)

For the 1,024 pairs (cardinality, modulus) in Wróblewski's BESTMOD.TXT the test passes every time. The independently verified mixed-radix sphere with r=2,303,115,151,489,024 and L=59³61⁹ has 0.7114<L P(1/r)<0.7115, so it rules out the plateau. Even at this single dilation, the two collections of scalar information have different mathematical consequences. The positive estimate for the actual R obtained from the sphere is already in [AllLengths.md](../subgolden/AllLengths.md). [Source table](https://www.math.uni.wroc.pl/~jwr/non-ave/BESTMOD.TXT) · [Rational verification](verify_golden_rule.py)

## The forced function on the interval

The identities z(c+1)=c and z(c+2)=1 make the plateau [c,1] reproduce at each smaller scale. If f is constant at H on [ct,t], the existing halving lemma applied to the two lengths czt and zt shows that f=H/2 on [czt,zt]. Thus f(zʲ)=f(czʲ)=2⁻ʲ for all j≥0. [Halving lemma](PlateauRigidity.lean)

For any finite word of binary digits b₁,…,bₙ let x=Σ bⱼzʲ and v=Σ bⱼ2⁻ʲ. Then

    f(x)=v,          f(x+czⁿ)=v+2⁻ⁿ.                                         (1)

For the empty word these are the normalized endpoints. At the next digit the residual interval length czⁿ splits into zⁿ⁺¹ and czⁿ⁺¹, each having f-value 2⁻ⁿ⁻¹. Subadditivity applied to the old right endpoint, then to the left endpoint plus each one of the two pieces, forces f(x+zⁿ⁺¹)=f(x+czⁿ⁺¹)=v+2⁻ⁿ⁻¹. This gives the two children of the interval. The [Lean certificate](GoldenCylinders.lean) checks the scaling and splitting identities used in this induction.

For infinite words, continuity gives f(Σ bⱼzʲ)=Σ bⱼ2⁻ʲ. The digit intervals nest and their lengths go to zero. Their complementary open gaps have the same f-value at both ends by (1), so monotonicity fills every gap uniquely. The part from c to 1 already has value one. Equivalently the uniquely specified function there is the distribution function of the sum Σ bⱼzʲ for independent fair bits, with its terminal plateau.

## Right endpoints and arbitrary digit rules

The corresponding canonical function F on [0,∞) is the continuous generalized inverse determined by

    F(y)≤t    if and only if    y≤P(t).

The terminating expansion gives the right endpoint of the plateau at each dyadic t. For instance P(1/2)=z, while its left limit is cz. The function is well-defined because P is strictly increasing, right-continuous and unbounded. Its inverse is continuous and F(Qy)=2F(y). This is also the global function constructed by eilamc14: for dyadic integer multiples at a fixed depth, the ordered binary grid in that proof has right endpoints given in the limit by P, and (1) gives the same distribution on [0,1]. Its splitting and gluing hold on the entire ray by that construction.

P is superadditive. For dyadic inputs this follows from binary carrying, since Q>2. For arbitrary t,u, round each **up** to multiples of 2⁻ⁿ, use the dyadic inequality and pass to the limit from above on both inputs and on their sum. Right-continuity includes the case where the sum is dyadic.

On the whole ray the rule for F is equivalent to P(t)≤LP(t/r) for every t≥0, by the inverse relation. Necessity on [0,1] alone follows if L<B(r): choose t=2⁻ᵏ with k large and put x=P(t)/L. Then both x and Lx belong to [0,1]. We have F(Lx)=t while x>P(t/r), so rF(x)>t. This also rules out the inequality for every other profile with that plateau, by uniqueness there.

For sufficiency, first write a positive dyadic t as a sum of distinct powers 2ʲ. Superadditivity and P(2ʲu)=QʲP(u) yield P(t/r)≥P(1/r)ΣQʲ=P(1/r)P(t). For a nondyadic t truncate its expansion below; P of the truncations tends to P(t), and monotonicity bounds their scaled values by P(t/r), even when t/r is dyadic. Thus L≥1/P(1/r) suffices at every t. In particular equality is allowed, and for r=2ᵐ the exact threshold is Qᵐ.

For the uniform gain statement use the existing local compactness of the normalized split-and-glue class. Monotonicity and gluing bound f(h) by 2⁻ᵏ whenever h≤3⁻ᵏ, and splitting transfers the modulus to any compact interval. Every added rule is closed under local uniform limits. The function f(φ) has infimum strictly above 1 when the class with a plateau is empty, since a minimizer would rescale to a plateau on [c,1]. The normalized class is nonempty because x↦x satisfies each r≤L. The same modulus of continuity retains a positive uniform gain at a slightly smaller dilation.

The [integer construction](GoldenIntegerModel.md) extends the passage test to recurrent near-plateaus with an exact finite prefix and an arbitrarily slowly diverging multiplicative tolerance. The [quantitative distortion theorem](CriticalDistortion.md) gives the optimal logarithmic blow-up rate on approaching φ from below.

These statements characterize enlargement of the interval in the scalar problem. The unknown asymptotic equivalent for the true R is a stronger question.
