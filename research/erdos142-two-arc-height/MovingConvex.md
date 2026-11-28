# Sharp terminal-support area for an arbitrary convex lower lift

Deldor14, 28 November 2026. In the [nested concave theorem](GlobalConcave.md), allow the lower arcs at 0<u<R to be given modulo one by any continuous real endpoints l(u)≤r(u), with l convex, r concave, width at most 1/2 and terminal width exactly 1/2. In particular the lower domain in its real lift is convex, and the intervals may move and wind on the circle without being nested. Keep 0<R≤1/2, the lower semicircle tail at R<u<1/2, upper support reaching R from below, the pointwise upward-primary-carry exclusion and the bounded angular midpoint-height assumption on almost every upper row. Then the largest area is still **(17−6√2)/28**. The attainer is the previously published polygon. This theorem applies to the area underlying a lower-bound construction for the interval problem.

## Shear and terminal caps

For u<R let nᵤ=(l(R)−l(u))/(R−u) and mᵤ=(r(R)−r(u))/(R−u). The intervals [nᵤ,mᵤ] are nested as u increases: nᵤ is nondecreasing, mᵤ is nonincreasing, and nᵤ≤mᵤ by the width hypothesis. An integer shear (s,t) ↦ (s,t−ks) subtracts k from both secants and preserves all the hypotheses.

If [n₀,m₀] contains no integer, shear it into (0,1). All secants now lie in (0,1). Rotate the terminal interval to (−1/2,0) and put a(u)=mᵤ(R−u), b(u)=−nᵤ(R−u), both zero at R, and z=a+b. For x=2R−1/2−u>0 the whole second upper preimage (1/2−a(u),1/2+b(u)) lies in the forbidden terminal gap (a(x),1/2−b(x)), because a(u)+a(x)<1/2 and b(u)+b(x)<0. The proof of that forbidden gap in GlobalConcave.md needs only continuity and the collapsing terminal envelope. Elsewhere z≤R−u. The surplus above 1/4 is at most 1/32 by the same integration as for a moving affine base.

Otherwise choose an integer in [n₀,m₀] as the shear. Then a(0),b(0)≥0. Both a and b are convex with zero terminal value; either may be negative inside. The full upper envelope has arcs (−a,b) and (1/2−a,1/2+b), each of length z, and |U|≤1/2. The baseline pairing gives total surplus ∫(|U|−z). If a(0)>R or b(0)>R use the large-displacement bound of GlobalConcave.md unchanged. Indeed the surviving second-arc length is always at most (B)₊+(P−1/2)₊, where P=a(u)+a(x) and B=b(u)+b(x), by intersecting the two sides of the real terminal gap. For a(0)>R, the nonnegative initial b(0) gives (B)₊≤b(0)/(2R); the rest of that proof uses only convexity of z, its terminal zero and z(0)≤1/2. Interchange the roles by angular reflection for b(0)>R.

We are left with 0≤a(0),b(0)≤R. Convexity gives P,B≤1/2 whenever x>0. There may be negative caps. Intersect the second arc with the complement of (a(x),1/2−b(x)): its left surviving piece has length at most (P−1/2)₊=0. Thus its right piece has length at most (B)₊, and similarly the surviving first arc has length at most (P)₊ and starts at −a(u), up to null endpoints. These are containments in permitted arc envelopes, sufficient even if other translates of the gap delete more. In particular, with a negative cap the entire upper row has measure at most z.

## The active height range

For x>0 use the signed lengths X=min(z,P) and Y=min(z,B); for x≤0 set X=Y=z. Set p=z−X and n=z−Y. Both cuts are nonincreasing in u. For x>0 these are (b(u)−a(x))₊ and (a(u)−b(x))₊. To see the monotonicity before clipping, the derivatives of the expressions are of the form l'(u)−r'(x) and l'(x)−r'(u) in the sheared coordinates. Every interior derivative of l is bounded above by every interior derivative of r: the former increase, the latter decrease, and the terminal one-sided order follows from l(t)−r(t)≥l(R)−r(R). Equivalently take differences using secants and then limits. Convex and concave functions are locally absolutely continuous away from the endpoints. The cuts may only drop at x=0, where they are set to zero.

Let M=1/4−min(p,n)−max(p,n)/2. On rows with both caps nonnegative this is the middle branch of the two-arc capacity surplus in GlobalConcave.md. If M<0, the actual surplus |U|−z is at most zero, including rows with a negative cap. Discard this initial range. On the remaining translated interval [0,L] we have M≥0, so |U|−z≤M also when a cap is negative. The bounds |U|−z≤1/2−z and |U|−z≤z always hold. Where the terminal partner exists we have, for either side i,
$$
 |U(v)|-z(v)\le \big(a_i(v)+a_i(T-v)\big)_+ ,\qquad T=2L-1/2,
$$
where a₁,a₂ denote the translated functions a,b. This follows by bounding the opposite arc by z, with the other arc clipped to its positive cap.

For L≤1/3 the short-interval chord bound of GlobalConcave.md suffices. For larger L take its same j,w,g,T,C. On (0,j) use M, bounded using the two signed raw caps in the order of the signed lengths X,Y. The linear majorant in that paper remains valid: M is exactly 1/4+max(X,Y)+min(X,Y)/2−3z/2, and replacing each X,Y by its own raw cap increases the expression in the selected order. On (j,w) and (g,L) keep the previous bounds. On (w,g) select the side with the smaller chord slope mᵢ=aᵢ(w)/(L−w), and use its positive cap. This amounts to taking the original linear bound on the measurable subset where that raw cap is positive, and zero on the rest. The coefficient is reduced only in a region with a nonnegative local or reflected coefficient. Before w the reflected term could only offset a coefficient of −1, and after w all coefficients remain nonnegative. Thus the sign needed to substitute both chords is preserved.

If both chord slopes are nonnegative, the optional subset on (w,g) can be enlarged to the whole band after chord substitution, as the paired chord sum is mᵢ/2≥0. The already verified two equal moments prove the desired bound. It remains to handle a negative smaller chord.

## A strict bound if a chord slope is negative

Normalize the translated coordinate to s=v/L in [0,1]. Write
$$
 W=w/L=4/7+(2C-1)/(7L),\qquad H=2-1/(2L),\qquad
 y=z(w)/(1-W)\in[0,1/2] .
$$
Here H is the normalized terminal reflection partner of s=0. Say b(w)<0 after interchanging the sides if needed. Convexity of a gives a(0)≥a(w)/(1−W)≥y and therefore b(0)≤1/2−y. These are values at the start of the translated interval. By convexity, for a normalized argument s,
$$
 b(Ls)\le(1/2-y)(1-s/W)_+ ,\qquad
 z(Ls)\le y(1-s)+(1/2-y)(1-s/W)_+ .
$$
For the first inequality interpolate to b(w)<0, then use its nonpositive chord to zero at L. For the second interpolate the known upper bound 1/2 at zero to z(w) and then to zero at L. Also |U|−z≤min(z,1/2−z)≤1/4. For s<H, both triangular bounds on b give the additional upper bound
$$
 (1/2-y)\big((1-s/W)_++(1-(H-s)/W)_+\big)
$$
by the positive-cap inequality above.

The standard-library certificate chord_gap.py integrates a rational upper bound for the minimum of these estimates. Here are the details making the finite check exhaustive. Partition L∈[1/3,1/2], y∈[0,1/2], s∈[0,1] into respectively 8,16,64 equal subintervals. Denote the ends by subscripts 0,1. Use the rational bound C<13/60 and replace W by its upper bound 4/7+(2·13/60−1)/(7L₁). Replace H by its lower bound 2−1/(2L₀). For the first triangular term use s₀, and use s₁ for the reflected term. Only apply the reflected bound on cells with s₁ at or below the lower bound for H; there both distances in the triangular bounds are nonnegative, so replacing W by its upper bound raises each positive part. Use y₁ for the coefficient of 1−s and 1/2−y₀ for the nonnegative triangular factors. For each L,y box sum these upper bounds on the 64 cells, divided by 64 and multiplied by L₁. All replacements weakly raise the integral bound. The largest resulting rational number is
$$
 178483/4194304 < 43/1000 < A-1/4 .
$$
This excludes an improvement from the negative chord sector and completes the global theorem. The analytic proof of the other sectors and their five compiled scalar identities are in GlobalConcave.md and ConcaveDual.lean.

## Reproduction and status

    python3 chord_gap.py
    python3 signed_rows.py

The first script implements the continuum upper-sum proof with rational numbers. The second checks 50,625 signed terminal-envelope pairs, including 4,500 negative-cap pairs within the two-cap regime. These examples test the real arc bookkeeping; the containment argument above is the proof. The complete geometric theorem is written, with exact numerical certificates. The retained terminal upper-support hypothesis and a convex real lift of the lower domain are substantive. The area and the attaining example come from the Deldor14/CubeJerry polygon, and the two-arc reflection formula and global moment identities are attributed in the accompanying papers. No asymptotic formula for the interval extremal number follows.
