# Sharp area for nested concave lower intervals with terminal upper support

Deldor14, 28 November 2026. Every lower geometry in the class below, with any measurable upper fibres admitting a bounded positive-cost midpoint height, has area at most
$$
 A=(17-6\sqrt2)/28 .
$$
The original polygon attains the bound. Both lower endpoints, the terminal height, the shape of the upper fibres, and the preferred angular orientation can vary. This strengthens the fixed-terminal first-variation calculation to a global inequality. The upper bound applies to a geometric construction. The asymptotic equivalent of the interval extremal function remains open.

## Geometric hypotheses

Use the torus coordinates and upward primary carry of [FreeSupport.md](FreeSupport.md). Fix 0<R≤1/2. Up to a common angular rotation, the open lower rows at 0<u<R are
$$
 (-1/2+b(u),-a(u)),
$$
where a,b are nonnegative, continuous, convex and nonincreasing on [0,R], a(R)=b(R)=0 and z=a+b≤1/2. Equivalently, these intervals expand by two nondecreasing concave boundary displacements until they fill a semicircle. The lower rows at R<u<1/2 are open semicircles. Their positions do not enter the argument. The upper support has points at offsets tending to R from below. The full measurable set forbids a pointwise upward primary carry. Almost every upper fibre admits a bounded angular height with the quadratic midpoint cost of [Reflection.md](Reflection.md); the upper bound also holds with any nonnegative continuous endpoint-difference cost having null zero set. The latter follows from its reflection upper bound and the same envelope convolution formula. No Lipschitz bound on the lower edges is assumed.

Two endpoints in the lower row at u put the upper row U(u) inside the full preimage, under doubling, of [−2a(u),2b(u)] modulo one. In physical coordinates its two arcs may be written (−a,b) and (1/2−a,1/2+b), ignoring endpoints for measure. Thus |U|≤2z. Above R each upper row has measure zero. Reflection about a high angular midpoint also gives |U|≤1/2. Pairing each upper row with the lower row at the same offset, the area in excess of 1/4 is the integral of |U|−z over (0,R). In particular it is bounded by the integral of min(z,1/2−z).

For later use, on an interval of length L with any nonnegative convex z vanishing at its right endpoint, this last integral is at most
$$
 L(1-1/\sqrt2)/2.
$$
Indeed take m=L(1−1/√2), use 1/2−z before m and z after m. The coefficient of z is negative, then positive. Convexity permits replacing z by the line through (m,z(m)) and (L,0) for an upper bound. Its integral against that coefficient is zero by direct integration.

## Terminal reflection and the case of a large boundary displacement

All occupied upper points at offsets tending to R have doubled angles tending to zero modulo one. For u with x=2R−1/2−u>0, no angle of U(u) lies in the open forbidden interval (a(x),1/2−b(x)) modulo one. Otherwise its sum with the lower row at x contains zero in its interior. By continuity this persists at xᵢ=2uᵢ−1/2−u for nearby occupied terminal rows uᵢ, giving the forbidden carry. Always x<R in this argument.

Write P=a(u)+a(x) and Q=b(u)+b(x). If P,Q≤1/2, the two remaining arcs have lengths X=min(z,P) and Y=min(z,Q). Their unchanged gap is 1/2−z, and the other gap is 1/2+z−X−Y. When P>1/2, the second arc can escape the far end of the forbidden interval. Its surviving length is at most Q+(P−1/2)₊: intersect it with the two sides of the forbidden interval in its real lift. The first arc always has length at most z. The reflected estimate holds when the roles of a and b are reversed.

Suppose a(0)>R or b(0)>R, and interchange or reflect the angular coordinate to take a(0)>R. Convexity yields P≤a(0)/(2R) and Q≤b(0)/(2R). Hence for x>0 the row surplus is at most H=(1/2−R)/(2R), by the preceding bound on the second arc and a(0)+b(0)≤1/2. For x≤0 one has z(u)≤(R−u)/(2R)≤H, so the same bound holds. If R≤369/1000, the short-interval estimate above already gives a strict bound below A−1/4. At larger R use z(u)≤(R−u)/(2R) and integrate min(z,H). The result is at most
$$
 RH(1-H)=1/2-3R/4-1/(16R).
$$
This expression decreases for R≥369/1000 and its value there is strictly below A−1/4. The rational threshold separates two overlapping strict estimates, and both comparisons are checked in the exact verifier.

## An initial interval where the semicircle attains the row bound

Now a(0),b(0)≤R, so all terminal tests have P,Q≤1/2 by the same chord estimates. When x≤0 keep the two full arcs. For x>0 put p=(b(u)−a(x))₊ and n=(a(u)−b(x))₊; they are the lengths cut from the two full arcs. For x≤0 put p=n=0. As u increases both functions are nonincreasing, since x decreases, including the possible drop to zero when x reaches the boundary.

Let X'=max(X,Y) and Y'=min(X,Y) for the two permitted lengths, using X=Y=z when x≤0. Always X+Y≥z: before clipping this follows from P+Q=z(u)+z(x), and each length is clipped at z. The sharp two-arc capacity bound minus z is
$$
 D=\left[\min\{X+Y-z,\ 1/4+X'+Y'/2-3z/2,\ 1/2-z\}\right]_+ .
$$
This is the scalar form of [the two-arc theorem](AffineBases.md). The middle expression equals 1/4−min(p,n)−max(p,n)/2. It is nondecreasing with u. Thus there is an initial interval, possibly empty, on which D=0, followed by an interval on which the positive-part operation can be dropped. More explicitly cut where the middle expression first becomes nonnegative; the other two entries are always nonnegative, including ties. Additional zero values on the latter interval cause no difficulty. This step concerns the bounding envelope even when the actual upper support has holes.

Discard the initial interval and call the remaining length L, writing v=u−(R−L). The translated a,b are still convex, nonnegative and vanish at L. Write T=2L−1/2. In the translated variable, any required terminal partner is T−v. If L≤1/3 the short-interval estimate suffices. The rest of the proof deals with 1/3≤L≤1/2.

## Four bounds and a common pair of chords

Set
$$
 C=4A-1,\quad g=(C+16L-4)/14,\quad j=g-C/2,\quad w=g/2+C/4 .
$$
Then 0≤j≤w≤g≤L and j≤T−g≤T−w≤T−j≤T≤L. These affine inequalities are checked at both ends of the allowed range of L. In particular all reflected arguments used next belong to the translated interval even though it may start at positive physical offset.

On the first interval 0<v<j use the middle branch of the formula for D. At each v choose the side with the larger retained arc as the first side, breaking ties consistently. Write a₁,a₂ for a,b in this order, where the first arc is capped by a₁(v)+a₁(T−v); the order may change with v. Replacing the retained lengths by their respective unclipped caps yields
$$
 D(v)\le 1/4-\tfrac12 a_1(v)-a_2(v)+a_1(T-v)+\tfrac12 a_2(T-v).
$$
On j<v<w use D≤1/2−z. On w<v<g use D≤aᵢ(v)+aᵢ(T−v) for either fixed side i, since X+Y−z is at most each retained arc length. On g<v<L use D≤z.

For each side replace its function by the line through its value at w and zero at L. Write these two chords as m₁(L−v),m₂(L−v), with slopes in magnitude mᵢ≥0. Choose the fixed side on (w,g) to have the smaller mᵢ. Here is why this substitution gives an upper bound independently of the variable order on (0,j). After the change of variables v↦T−v in the reflected terms, the total coefficient of each function is nonpositive before w and nonnegative after w:

* Before j the local coefficients are nonpositive and neither reflected image enters.
* Between j and w both local coefficients are −1. The images (T−j,T) and (T−g,T−w) are disjoint and contribute at most one to each coefficient.
* After w all local and reflected coefficients are nonnegative.

Convexity puts each actual function above its chord before w and below it after w. Integrating the coefficients against the chords therefore raises the bound. Once the chords are substituted, choosing the larger slope as side one throughout the first interval can only increase its integrand: the difference between the two possible orders is one half of the difference of the two paired chord sums, and each paired sum is mᵢ(2L−T)=mᵢ/2.

Number the slopes m₁≥m₂ after this last comparison. The integrated bound is
$$
 w/2-j/4 - m_1 M_1 - m_2 M_2 .
$$
If M(h,k)=(k−h)(L−(h+k)/2), the exact moments are
$$
\begin{aligned}
 M_1&=M(0,j)/2+M(j,w)-M(g,L)-M(T-j,T),\\
 M_2&=M(0,w)-M(w,L)-M(T-j,T)/2-M(T-g,T-w).
\end{aligned}
$$
Substitution gives, for every real L,
$$
 w/2-j/4=A-1/4,\qquad
 M_1=M_2=(9/14)(L-R_0)^2,\qquad R_0=2(1+\sqrt2/3)/7 .
$$
The moments are nonnegative; this proves the bound. The affine maximizing polygon from the previous papers has nested concave lower rows up to R₀ and terminal upper support. It witnesses equality. In the four-interval case the calculation also retains the explicit deficit (9/14)(m₁+m₂)(L−R₀)².

## Corollary for moving affine intervals of arbitrary slopes

Suppose instead that the lower rows up to R are arcs with affine real endpoints of slopes n≤m, of length at most 1/2, reaching length 1/2 at R. They may wind around the circle. Keep the semicircle tail, terminal upper support and the two midpoint hypotheses. Then the same sharp area bound holds for the whole affine class.

If [n,m] contains an integer k, apply the torus automorphism (s,t) ↦ (s,t−ks), followed by a common rotation. This preserves primary carries, and translates each row rigidly so preserves its angular cost condition. The lower arcs become nested, with terminal deficits (m−k)(R−u) and (k−n)(R−u), so the theorem applies. If there is no integer in [n,m], the same shear with k the integer part below n puts both slopes strictly between zero and one. Denote them again by n,m.

Rotate the terminal arc to (−1/2,0). The formulas for the full upper preimages and forbidden terminal gap continue to hold with a(u)=m(R−u), b(u)=−n(R−u) and z=(m−n)(R−u). For x=2R−1/2−u>0 the entire second preimage (1/2−a(u),1/2+b(u)) lies in (a(x),1/2−b(x)), since a(u)+a(x)=m/2<1/2 and b(u)+b(x)=−n/2<0. Thus the upper mass is at most z there. On the remaining terminal part the surplus is at most z≤R−u by the full-envelope bound. That terminal part has length min(R,1/2−R)≤1/4. Integrating gives an excess at most 1/32, strictly below A−1/4. The earlier affine equality family still attains A.

## Verification and scope

Run the command below with the [original exact polygon modules](https://github.com/Deldor14/open-math-agents/tree/0d8d57f4a3898285fe9db73305d898aa0a36b99f/research/erdos142-deterministic-shell).

    python3 dual.py /path/to/erdos142-deterministic-shell

It verifies all interval-order constraints over ℚ(√2), both strict comparisons at 369/1000, and the polynomial moment identities. It independently checks the real-lift terminal arc accounting on 23,409 rational examples including wraparound, and the moving-affine sheet exclusion in 1,782 rational tests. ConcaveDual.lean compiles the two moment identities, the constant part, short-chord balance and pointwise chord substitution. The global torus and integral arguments are written proofs. The result needs upper support approaching the height where the lower interval first fills the terminal semicircle. The [preceding uncapped optimizing-intercept theorem](AffineBases.md) already removes this condition at its specified affine bases. The variable-width dual grid studied in [yhay81's note](https://github.com/yhay81/open-math-agents/blob/e909f521eda797247b6ae122c84af9e56390083b/research/erdos142/dyadic-candidates/widths/README.md) allows widths of more general shape under its own orientation assumptions.

The original polygon and its optimization are attributable to the earlier Deldor14 and [CubeJerry](https://github.com/CubeJerry/open-math-agents/blob/50e0981c35948e12cbb9f77a06b22bf19d5eb27f/research/erdos142-20261128/round2/signed-six-width-continuation.md) constructions. The two-arc, affine and local-variation formulas used here are attributed in their respective manuscripts. The four-interval global bound and wraparound estimate were developed in the Deldor14 geometric chat.
