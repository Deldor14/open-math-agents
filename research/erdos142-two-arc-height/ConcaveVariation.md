# First variation for concave perturbations of the lower boundary

Deldor14, 28 November 2026. Start at any optimizing intercept from [AffineBases.md](AffineBases.md). Keep its terminal height and its two terminal lower endpoints fixed. For every admissible concave first-order deformation of either lower boundary, the right derivative of the optimized terminal-support area is nonpositive. The upper rows may change their angular mode and may have arbitrary holes. The conclusion is a first-order obstruction. Finite deformations and competitors whose upper support ceases before the terminal height are outside this derivative statement.

## Perturbation and exact caps

Use α,β,S,Z₀ from the affine optimizer, write R₀=Z₀/S, and let 0≤d≤(1/2−Z₀)/S. The chosen intercept is e=1/2−Z₀−Sd, and its terminal height is R=R₀+d. For 0≤u≤R replace the lower right magnitude 2αu and lower left magnitude e+2βu by
$$
 r_\lambda(u)=2\alpha u+\lambda f(u),\qquad
 l_\lambda(u)=e+2\beta u+\lambda h(u).
$$
Here f,h are bounded continuous concave functions with f(R)=h(R)=0. Take λ≥0 small for which the lower magnitudes are nonnegative, increasing, and their sum is less than 1/2 below R. Beyond R keep lower rows of length 1/2, with right magnitude extended affinely in such a way that the right magnitude and the actual left magnitude are concave on the full lower layer. For example admissible piecewise affine perturbations with sufficiently small λ allow such an extension. The derivative analysis below requires only these hypotheses. Upper support reaches R and the primary upward carry is forbidden pointwise. The row condition is the bounded angular midpoint-height condition used in the preceding paper.

At each u<R the full upper envelope consists of two arcs of common length z=1/2−rλ(u)−lλ(u). When x=2R−1/2−u>0, the following additional upper lengths, intersected with [0,z], are exact outer caps:
$$
 A_u=2r_\lambda(R)-r_\lambda(x)-r_\lambda(u),\qquad
 B_u=2l_\lambda(R)-l_\lambda(x)-l_\lambda(u).
$$
The two magnitudes then start at rλ(u) and lλ(u), as before. When x≤0 there is no mixed cap.

For necessity, the doubled values of any occupied upper rows approaching R converge to 2rλ(R) modulo one, because the full envelope collapses and rλ(R)+lλ(R)=1/2. An upper endpoint at offset u plus the open lower interval at x cannot contain that limit in its interior: membership would persist along the terminal sequence by continuity of the lower endpoints. On the positive lobe the lower end of this sum interval is below 1/2<2rλ(R). On the negative lobe its upper end exceeds 2rλ(R)−1, since rλ(u)+rλ(x)>2rλ(R)−1/2. At λ=0 the latter margin is 1/2−α, uniformly in u, and bounded perturbations preserve it for small λ. These inequalities give the two displayed caps on the corresponding physical magnitudes. The same-height lower pair gives the full envelope.

For sufficiency, two lower endpoints have their sum between the constraints from the equal-height pair by concavity of the actual lower endpoints. For a mixed endpoint pair, keep its upper offset u fixed and vary the lower height y, with upper target v=(1/2+y+u)/2<R. We have y<v and 0<y<x. For any concave right or left magnitude p on [0,R], the function 2p((1/2+y+u)/2)−p(y) is nonincreasing in y. This follows by integrating its almost-everywhere derivative on compact interior subintervals and taking endpoint limits. Its minimum at x is 2p(R)−p(x), precisely the absolute cap used above. The other side of the angular sum lies in the permitted gap by monotonicity, p≥0 and y<v. Both upper endpoints cannot generate an upward carry. Hence the whole angular-capacity optimum in the envelope is available, row by row, by the interval trims of the reflection theorem. The trims are measurable, and the upper tail has two full nonempty arcs for small λ. General concave rows can have infinitely many crossings; only geometric measure and row heights are asserted in that generality.

## Differentiation

Write v=u−d and T=2R₀−1/2. The baseline z equals Z₀−Sv. For v<0 the semicircle strictly dominates the oriented trim in the surplus expression away from its switching point; the paired upper and lower surplus is identically zero to first order. For 0<v<R₀ the branches of C−z in the affine proof are the following, with X and Y the retained positive and negative envelope lengths.
$$
\begin{array}{c|c|c}
 v & C-z & \text{active lengths}\\ \hline
(0,J) & 1/4+X+Y/2-3z/2 & X=A_u,\ Y=B_u\\
(J,V) & 1/2-z & \\
(V,G) & Y & X=z,\ Y=B_u\\
(G,R_0) & z & X=Y=z .
\end{array}
$$
For almost every row these formulas are stable for sufficiently small λ. In particular, on the semicircle branch X+Y>z at baseline, since α+β>1/2. On the last band the full lengths remain active away from the switching points. At u,x with an active mixed cap its derivatives are −f(u)−f(x) for Aᵤ and −h(u)−h(x) for Bᵤ, while z' =−f(u)−h(u). The finite min/max capacity formula is Lipschitz in these variables, and the functions are bounded. Dominated convergence differentiates the integral away from the finitely many baseline switch heights, which are null.

Writing 1ᵢ for the indicator of an interval I, the right derivative of the total area is
$$
 \int_0^{R_0}\! K_r(v) f(d+v)+K_l(v) h(d+v)\,dv ,
$$
where
$$
\begin{aligned}
K_r={}&\tfrac12 1_{(0,J)}+1_{(J,V)}-1_{(G,R_0)}-1_{(T-J,T)},\\
K_l={}&1_{(0,V)}-1_{(V,R_0)}-\tfrac12 1_{(T-J,T)}-1_{(T-G,T-V)} .
\end{aligned}
$$
The reflected arguments occur because x=d+T−v. The unchanged primary tail beyond R contributes no derivative.

## Sign for every concave variation

Both kernels are nonnegative before V and nonpositive after V. Both obey
$$
 \int_0^{R_0}(R_0-v)K_i(v)\,dv=0 .
$$
These are finite identities in ℚ(√2). The accompanying exact verifier checks the sign on every constant piece and evaluates each interval contribution as its signed length times R₀ minus its midpoint, that is, c(b−a)(R₀−(a+b)/2).

If H(v)=f(d+v) or h(d+v), let L be the line through (V,H(V)) and (R₀,0). Concavity puts H below the extension of L for v<V and above it for v>V. Therefore ∫KᵢH≤∫KᵢL=0 for each side separately. Perturbations affine on the active band give zero derivative, which explains why an approximate quadrature of narrow early tents can give small apparent positive numbers. The sign certificate applies to the continuum of kink locations.

## Reproduction

    python3 variation.py /path/to/erdos142-deterministic-shell

The first-variation proof is written. The kernel moments use exact arithmetic and the parameter definitions from the original polygon. The scalar Lean lemmas in the preceding affine paper concern its row and area identities. This result changes neither the established lower-bound exponent for the interval extremal function nor its unresolved asymptotic equivalent.
