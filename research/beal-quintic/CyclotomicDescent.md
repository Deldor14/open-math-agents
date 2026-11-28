# A cyclotomic restriction on primitive quintic sums

Suppose that positive coprime integers a,b satisfy a⁵+b⁵=cᵖ with p prime. For **every prime 29 ≤ p ≤ 239 with p ≢ 1 mod 5**, let S(p) be the auxiliary primes on its line in `cyclotomic_witnesses.txt` (the first number is p). Then

    p² · ∏_{q∈S(p)} q  divides  ab.

Moreover, for ζ a primitive fifth root of unity, a+bζ is a pth power in ℤ[ζ]. For p=29 the required divisor of ab is 29²·59·929 = 46,096,051. For p=89 it is 89²·179·1069·5519 = 8,365,100,124,649. These conclusions also apply if the original exponent of c is any multiple of p, by replacing c with the corresponding power. Each prime power may divide a different summand.

The proof combines theorems of Billerey, Chen, Dieulefait and Freitas (BCDF) with 99 explicit finite residue tests. It gives necessary conditions on a putative solution. The complete signatures for primes 7 through 53 were treated by Stoll, assuming GRH for p ≥ 23. The divisibility proof here is independent of GRH. No priority claim is made. [Stoll, Theorem 8.8](https://arxiv.org/pdf/1506.04286). 

## Cyclotomic factorization

Set D=a+b. BCDF exclude 5|D for a nontrivial primitive solution. This also provides the context for the elementary Lean restrictions on the 5|D branch in the earlier note. [BCDF, Theorem 5](https://arxiv.org/pdf/1703.06530).

Let L=ℚ(ζ), F=ℚ(√5), and ε=1+ζ+ζ⁻¹, choosing √5=2ε−1. The five factors a+bζⁱ of cᵖ are pairwise coprime as ideals in ℤ[ζ]. A common prime ideal would either divide a and b or divide a difference of distinct fifth roots, hence lie over 5 and divide D. Thus D=sᵖ for a positive integer s (also directly from gcd(D,(a⁵+b⁵)/D)=1). The class number of L is one by Minkowski's bound, which here is less than 2. The units are μ₁₀ times powers of ε. Indeed, for a unit u the quotient u/ū is a root of unity by Kronecker's theorem and reduces to 1 at 1−ζ, hence belongs to μ₅. Dividing u by a square root of u/ū in μ₅ gives a real unit. The units of ℤ[(1+√5)/2] are ±εⁿ. Since p is coprime to 10, we obtain

    α = a+bζ = εʲ γᵖ,      0 ≤ j < p,   γ ∈ ℤ[ζ].

## Congruence at the exponent prime

Let f be the order of p modulo 5, m=p² and e=pᶠ−1. Modulo p the ring ℤ[ζ] is a product of fields of order pᶠ. For every unit V modulo m one therefore has Vᵖᵉ=1 modulo m, by raising 1+pH to the pth power. Every primitive linear form a+bζ is a unit modulo p because f>1. The first certificate on each line establishes that εᵉ has order p modulo m.

If p∤D, divide α by D=sᵖ and put x=b/D modulo m. The element A=1+x(ζ−1) must satisfy Aᵉ=εʲᵉ modulo m. Testing all x modulo m and all j modulo p gives exactly the two pairs (j,x)=(0,0),(0,1) for every listed p. Thus p²|ab.

If p|D, then m|D since D=sᵖ. Here p∤b and α≡b(ζ−1) modulo m, so αᵉ≡εʲᵉ. Taking the norm to the real subfield and using ε(1−ζ)(1−ζ⁻¹)=√5 gives (√5 b²)ᵉ≡ε⁽²ʲ⁺¹⁾ᵉ. Real conjugation sends √5 to −√5 and ε to −ε⁻¹. Since e is even, it follows that ε²⁽²ʲ⁺¹⁾ᵉ≡1. The computed order forces j=(p−1)/2. Thus only 0 and (p−1)/2 can occur globally.

## Removing the exceptional class at an auxiliary prime

Every listed q is prime with q≡−1 mod 5 and q≡1 mod p. First we show q∤c. For the modular input normalize a,b by signs and interchange as in section 12 of BCDF. These operations preserve the prime factors of c. Under this normalization the residual Frey representation is congruent to that of J₅(0,1) at level supported at 2 and 5. If q divided c, the Frey Jacobian would have multiplicative reduction there, and the level-raising congruence would give a_v(J₅(0,1))²≡(Nv+1)² at the coefficient prime over p, for v|q in F. Here Nv=q, since q splits in F. [BCDF, Theorem 1.8, Proposition 5.14, sections 9.7 and 12](https://arxiv.org/pdf/2205.15861).

The reference curve is y²=x⁵+1. For clarity, its two-dimensional Frobenius traces at v vanish. On the full characteristic-zero Tate module the automorphism x↦ζx has four one-dimensional eigenspaces, one for each nontrivial fifth root. This follows also from its action on dx/y and x dx/y and their conjugates. The polarization pairs opposite eigenspaces. Frobenius at q interchanges the members of each pair since q≡−1 mod 5. On the paired plane it has trace zero and determinant q by the symplectic pairing, hence its square is −q on the full Tate module. Each two-dimensional real-multiplication block has determinant q (the cyclotomic determinant), so each has trace zero as well. The level-raising congruence would now imply p|q+1, contrary to q≡1 mod p. This proves q∤c and therefore q∤D.

Reduce A=(a+bζ)/D at q and set x=b/D in the prime field. Since the residue fields of ℤ[ζ] have order q², necessarily

    A^((q²−1)/p) = ε^(j(q²−1)/p)  modulo q.

In each of the two quadratic factors put u=ζ+ζ⁻¹, a root of u²+u−1 over the prime field. The norm of A is 1+(u−2)x(1−x). With k=(q−1)/p, the same test becomes

    (1+(u−2)x(1−x))ᵏ = (1+u)²ᵏʲ  for both u.

For every certified (p,q) the solutions with j=0 are exactly x=0,1. There are no x for j=(p−1)/2. Since every exponent has at least one such q, the global unit class must be j=0. The exceptional chart p|D is excluded, p²|ab, and every certified q divides ab. Coprimality of the listed prime powers proves the stated product.

## Independent finite checks

The certificate contains 33 exponent primes and 66 auxiliary primes. Both implementations verify both tables and check primality and coverage. The Python verifier reduces quartic polynomials modulo Φ₅, expands all lifts x₀+tp modulo p², and uses the two quadratic norms at q. The C++ verifier raises each residue directly to its exponent by cyclic convolution in the five-dimensional group ring modulo z⁵−1, then projects to Φ₅ by subtracting the fifth coefficient. It uses no Taylor expansions or finite-field norm trick. The modular inputs and the deductions above are a written mathematical argument; the two programs certify its finite computations.

    python3 verify_cyclotomic.py
    c++ -O2 -std=c++17 verify_cyclotomic_direct.cpp -o verify_direct
    ./verify_direct cyclotomic_witnesses.txt
