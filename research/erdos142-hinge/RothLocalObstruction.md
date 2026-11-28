# A single sealed progression controls the cost of a nonextendible prescription

Use [N]={0,…,N−1}. All progressions below have positive step. A prescription S is a subset of [N] containing no three-term progression. An extension is a three-free superset in [N]. A window has exactly L terms.

Let a(N,L) be the minimum cardinality of a prescription with no extension meeting all windows. Let b(N,L) be the minimum cardinality of a prescription for which one specified window is missed by **every** extension. Take N≥8L+1 so both minima exist by the digital construction in the preceding paper. For a single window W the latter condition is elementary: W is disjoint from S, and every z∈W completes a triple with two sites of S. In fact if one z did not, S∪{z} would itself be an extension meeting W.

**Localization theorem.** Fix ℓ=⌈exp(C₀√log N)⌉ with C₀ sufficiently large for the two-color witness below. Uniformly for ℓ¹⁶≤L and N≥8L+1, as N→∞,
$$
0\le b(N,L)-a(N,L)\le O(\ell^6)=o(\sqrt L).
$$
The result compares windows of the **same** length. In particular every 3-free prescription of cardinality at most (2/√3−δ)√L extends to a 3-free set hitting all L-windows, for any fixed δ>0 and all sufficiently large N in this range. For L=2·4^m a prescription of exactly √(2L) sites already seals one window of step three in [3L]. For every L there is such a prescription with fewer than 2√(2L) sites when N≥12L.

The restriction on the size of the ambient interval allows L smaller than every fixed power of N. The leading constant for a(N,L)/√L remains undetermined. This is a structural result on the auxiliary extension problem associated with the unrestricted Roth number.

## From failure to a single window, without shortening it

Clearly a≤b. Let S realize a. The earlier construction gives |S|≤4√L. Let C=D(S) consist of S and all sites of [N] completing a triple with a pair in S. Its size M is O(L). Choose a 3-free H meeting every ℓ-term progression, available by Cao's theorem. Put T=⌊L/(3ℓ)⌋. A window is rich if it contains at least T elements of C. [Two-color witness](https://arxiv.org/html/2609.31798v1) · [Earlier construction and representative count](RothPinnedWindows.md)

There are O(ℓ⁵) distinct steps of rich windows, even when all starting positions are used. If M<T there are none. Otherwise choose K=⌈8LM/T²⌉=O(ℓ²). Among the rich steps take a maximal collection for which each pair q,r satisfies max(q/g,r/g)>K, with g=gcd(q,r). In one representative window per selected step mark exactly T points of C. Each pair of marked sets intersects in at most 1+L/K ≤ T²/(4M), using T²/M→∞. If k=⌈2M/T⌉ representatives existed, inclusion–exclusion through the pair term would give union size at least kT−choose(k,2)T²/(4M)>M. Thus there are O(M/T)=O(ℓ) representatives. At most K² step ratios have both reduced numerator and denominator ≤K, giving the claimed count.

Starting from V=S, process the rich windows one step at a time and one residue chain at a time. Within a chain visit windows in increasing order of their right endpoint. Skip windows already hit by V. For each remaining one adjoin its **rightmost** site outside D(V), if it has one. If it has none, the current V is a free extension of S sealing that one L-window. Stop in that case.

For each step q at most 2M/T sites are adjoined. To see this, take three successive successful choices on a single chain, at points p₁,p₂,p₃ in windows W₁,W₂,W₃, ignoring skipped windows. W₂ starts strictly after p₁, since its right endpoint is no earlier and it is still unhit. Every site of W₁ strictly after p₁ was already forbidden at that choice. The forbidden set increases, so p₂ must be strictly after the end of W₁. W₃ starts after p₂. Consequently every other selected window is disjoint on the chain. Distinct residue chains of one step are disjoint as well. Each selected window costs T marked sites of C with multiplicity at most two. The bound applies to any initial segment, including a run that stops on a failure.

The total number of sites adjoined is E=O(ℓ⁶). If the whole rich-window sweep succeeded, V would meet all rich windows. Moreover the number of newly forbidden sites is at most E+3|S|E+3 choose(E,2)=o(L/ℓ). In each other window, H originally occupies at least ⌊L/ℓ⌋ sites, fewer than T of which were in D(S). It still has at least L/(3ℓ) candidates outside D(V), for all large N. Join two remaining points of H by an edge if they form a triple with some point of V. The maximum degree is ≤3|V|=O(√L). As in the previous paper, the distribution on graph-independent subsets with activity z=p/(1−p), p=1/(2(1+3|V|)), hits any specified set of b candidates except with probability at most exp(−pb/2). As √L/ℓ≫log N, some independent subset hits every nonrich window simultaneously. Adjoining it to V would extend S to a three-free set hitting **every** window, contrary to the definition of S. Therefore the sweep stops with an actual sealed L-window, and b≤a+E.

## A sharper count of the candidate completions

Fix a window W with starting residue a modulo q, disjoint from a prescription S of f points. Relative to a, let the coordinates of two distinct sites be x<y. Their possible completion coordinates are 2x−y, (x+y)/2 if integral, and 2y−x. If two lie in W, two of 2x−y, x+y, 2y−x vanish modulo q. Any two of these congruences imply
$$
x+y\equiv3x\equiv3y\equiv0\pmod q.
$$
The identities follow from (2x−y)+(2y−x)=x+y. When x and y both vanish modulo q their sites lie on the residue chain containing W. Since they are outside W, the whole window lies in a single one of the three intervals cut out on that chain by the two sites. The possible completions lie respectively to the left, between, and to the right of those sites. Only one can lie in W.

It follows immediately that for 3∤q there are at most choose(f,2) sites of W covered by pairs of S. For 3|q, a pair that can contribute more than once must come from the two classes a+q/3 and a−q/3, one site from each. Pairs internal to either single class cannot contribute at all, since none of the three necessary congruences holds. If u,v are the class sizes, the number D of covered sites is at most
$$
\binom f2-\binom u2-\binom v2+2uv.
$$
This is ≤3f²/4: four times the upper bound subtracted from 3f² gives f²−(u+v)²+3(u−v)²+2(f−u−v)≥0. Thus b≥2√(L/3). Combining with localization gives the improved lower bound for a. If only windows with 3∤q are tested, the same greedy and completion arguments apply to those steps, giving a lower bound (√2−o(1))√L on a nonextendible prescription for that restricted family. For that version an interval of step one from the previous digital construction still gives the O(√L) upper bound used at the start.

## Using both endpoints of a pair

Put P=4^m, u=P−1. Take the base-four set D_m with digits 0 and 1 and prescribe
$$
X=\{3(u-x)+1:x\in D_m\},\qquad Y=\{3u+2+3y:y\in D_m\}.
$$
Both parts are three-free. They occupy distinct nonzero residues modulo three, so a triple using both parts is impossible. Every t=0,…,P−1 can be written as x+2y and also as 2x′+y′ with digits from D_m. The completion with the midpoint in Y gives 3(P+t), and the completion with the midpoint in X gives 3(P−1−t). Their union is the full window 0,3,…,3(2P−1). The seed has 2√P sites, it fits in [6P], and it is disjoint from the window. For general L use the least P=4^m≥L/2. Then P<2L when L≥2. The unconditional obstruction improves the previous construction's upper constant.

With m=7, 256 prescribed sites exclude all **32,768** sites of one arithmetic progression. [Lean proof for every m](RothLocalObstruction.lean)

## Verification scope

Seven theorems in the Lean file check the separation of every other greedy interval, the congruence implication, the quadratic inequality, and the size, freeness, range and whole forbidden window of the digital family. The rich-slope sweep and the probabilistic extension are written proofs. The [integer verifier](check_roth_local_obstruction.py) checks the pair bounds on 458,524 disjoint window/prescription pairs at N=9,13,16 and checks all endpoint completions of the digital examples through m=7. At N=13, L=5, a=3 and b=4, so exact equality at every finite N would be false. [Earlier finite-family enumerator](check_roth_pinned_windows.py)
