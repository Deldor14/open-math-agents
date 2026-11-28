# An all-length increase below the golden ratio for the interval Roth number

Let R(n) be the largest size of a subset of [0,n) containing no nonconstant three-term arithmetic progression. Set

    A = 17930960184279979613136592675447023779624342874
    B = 29012903029086084987555223918059441665802764285
    D = 10^123.

Then, for every integer n≥0,

    R(⌈Bn/A⌉) ≥ (1+1/D) R(n).

In particular the maximum increases by at least one at every positive input. With downward rounding the same multiplicative gain holds at ⌊(B+1)n/A⌋ for every n≥A. The smaller ratio B/A is about 2.154·10⁻⁴³ below the golden ratio. Both dilations are smaller than the previous downward-rounded ratio in [the earlier proof](AllLengths.md). The gain improves on the previous all-length gain 2·10⁻¹³⁴ by a factor of 50 billion. The asymptotic equivalent of R(n) remains open.

## The digit inequality at fractional lengths

Write U for the piecewise linear interpolation of R at consecutive integers. For a cyclic progression-free alphabet E of size C modulo M,

    U(Mx) ≥ C U(x)    for all real x≥0.

In [0,Mq+d), exactly d residue classes have q+1 sites and the rest have q, where 0≤d≤M. Rotate E by t. In every selected residue place an optimal set of the available length. Reducing a midpoint equation modulo M first makes the three residues equal, after which freeness in their common fibre precludes a nonconstant progression. Sum the resulting bound over the M rotations. Each selected digit occurs in a long residue d times. This gives M R(Mq+d)≥C[(M−d)R(q)+dR(q+1)]. Between adjacent such mesh points both sides of the claimed inequality are affine. The unequal-fibre packing and its use for fractional blocks were given by pwamsley2015 in [note 181029](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=181028&limit=1) and [note 181117](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=181116&limit=1).

Take M=59³61⁹, C=2303115151489024, using the twelve-digit sphere of [note 172398](https://lefttosolve.com/api/desk/board?problem=Erdos142.erdos_142.variants.three&since=172397&limit=1). In each radix r, digit values range from 0 to (r−1)/2, so every full encoding is at most (M−1)/2. A modular midpoint equation therefore lifts to an integer equality without wraparound, and there are no digit carries. Strict convexity of the common quadratic charge forces all digits to agree. This proves cyclic freeness of the same alphabet used in the integer product proof. [Counting the digits](ChargedDigits.lean) · [Geometry of the sphere](ChargedGeometry.lean)

## The fifty comparisons of gaps

Fix n and let P(j)=A U(jn/A). The interpolation of eilamc14 gives monotonicity, P(x+y)≤P(x)+P(y) and P(x)+P(y)≤P(x+y+max(x,y)). They hold on every integer mesh. The preceding paragraph gives C P(a₀)≤P(Ma₀) even when a₀n/A is smaller than one. [Rational interpolation](ExactInterpolation.lean) · [Original proof](https://github.com/eilamc14/open-math-agents/blob/d8ca5d4abbf28eb0af283e37f6b4c5f3162bf5ae/research/erdos142/DoublingGrowth.lean)

Start with (a₀,b₀)=(24178516392292583494123520,35672756411597299944259584). For 0≤i<50 set hᵢ=2^(73−⌊3i/2⌋) and

    aᵢ₊₁=aᵢ+bᵢ,          bᵢ₊₁=aᵢ+2bᵢ+hᵢ.

At the last stage (a₅₀,b₅₀)=(A,B). Let Δ=P(B)−P(A). For an earlier row divide its endpoints by hᵢ, obtaining integers l,r. Starting with x=l, repeatedly advance to y=min(r,2x+1−l,⌊(r+1+x)/2⌋). With z=l+r−x, splitting and joining give

    P(hᵢy)−P(hᵢx) ≤ P(hᵢ(l+2r+1))−P(hᵢ(l+r)),

since y+z+max(y,z)≤l+2r+1. If mᵢ steps reach r, the gap on row i is at most mᵢ times the gap on the next row. All fifty walks are checked with 8025 comparisons in total. Write K=∏mᵢ. Every earlier gap is at most KΔ. Consequently

    P(bᵢ) ≤ 2ⁱ [P(a₀)+KΔ].

Indeed P(aᵢ₊₁)≤2P(aᵢ)+KΔ. Adding KΔ and iterating gives the displayed right-endpoint estimate. [General grid lemma](VariableGrid.lean)

Set T=C−2⁴⁵. Represent T as a sum of powers 2ʲ, using as many copies of 2⁵⁰ as possible and the usual binary digits below. The sum of the corresponding bⱼ is at least M(a₀+1). Hence C P(a₀)≤T[P(a₀)+KΔ] and P(A)≤2⁵⁰[P(a₀)+KΔ]. Elimination gives

    Δ ≥ [(C−T)/(2⁵⁰ C K)] P(A) ≥ P(A)/10¹²³.

Monotonicity and upward rounding give the first theorem. For n≥A the extra n/A in the second dilation pays the rounding difference. The table, its costs, the comparison to the earlier ratio and the final algebra are in [TunedNumeric.lean](TunedNumeric.lean). An independent [Python check](verify_tuned_growth.py) reconstructs the grid and the costs without storing the table.

## Reproduction

Start with the dependencies of [AllLengths.md](AllLengths.md). Compile the updated ChargedGeometry, then CyclicFiberGrid, FiberInterpolation, ChargedInterpolation, VariableGrid, TunedNumeric and TunedRoth with Lean 4.33.1. [Fibre averaging](CyclicFiberGrid.lean) · [Interpolation between mesh points](FiberInterpolation.lean) · [Cyclic certificate for the sphere](ChargedInterpolation.lean) The application to mathlib's interval Roth number is in [TunedRoth.lean](TunedRoth.lean).
