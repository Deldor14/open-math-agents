import Mathlib

/-!
# OEIS A046932: period of `xⁿ + x + 1` over GF(2), Bartholdi's conjecture

Source: https://oeis.org/A046932
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the period of `xⁿ + x + 1` over `GF(2)`: the least `m > 0` such that `xⁿ + x + 1`
divides `x^m + 1`. Conjectures (OEIS entry): `a(2^k - 1) = 2^(a(k)) - 1` (Bartholdi, 2000), and
more generally `a((2^(km) - 1)/(2^m - 1)) = (2^(a(k) m) - 1)/(2^m - 1)` (for `m = 1` this is
Bartholdi's conjecture).

Conventions:
* `n ≥ 2`, so `xⁿ + x + 1` has nonzero constant term and the period exists; in the conjectures
  `k ≥ 2` and `m ≥ 1`. `main` states the general conjecture together with Bartholdi's.
-/

namespace OMA.S_oeis_a046932

open Polynomial

/-- The period of `xⁿ + x + 1` over `GF(2)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (X ^ n + X + 1 : (ZMod 2)[X]) ∣ X ^ m + 1}

end OMA.S_oeis_a046932


/-! Frobenius linearization for the upper-bound direction in the period
conjectures of Bartholdi and Alekseyev (OEIS A046932). -/
namespace Deldor14.TrinomialPeriod
open Polynomial
local notation "F" => ZMod 2
local notation "P" => Polynomial F
private noncomputable def L (m : ℕ) : P →ₗ[F] P :=
  Polynomial.lsum (fun n => (LinearMap.id : F →ₗ[F] F).smulRight (X^(2^(m*n)) : P))
private lemma mono (m i : ℕ) (z : F) :
    L m (monomial i z)=z • (X^(2^(m*i)) : P) := by
  simp [L,Polynomial.lsum_apply,Polynomial.sum_monomial_index]
private lemma atom (m i : ℕ) : L m (X^i)=(X^(2^(m*i)) : P) := by
  simpa [← C_mul_X_pow_eq_monomial] using mono m i 1
private lemma shift (m j : ℕ) (g : P) :
    L m (g*X^j)=(L m g)^(2^(m*j)) := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg => rw [add_mul,map_add,map_add,hf,hg,add_pow_char_pow]
  | monomial i z =>
    rcases (by decide : ∀ x : F, x=0 ∨ x=1) z with rfl | rfl
    · simp
    · rw [← C_mul_X_pow_eq_monomial,map_one,one_mul,←pow_add,atom,atom,
        Nat.mul_add,pow_add,pow_mul]
theorem preserves_divisibility (m : ℕ) {f g : P} (h : f ∣ g) : L m f ∣ L m g := by
  obtain ⟨w,rfl⟩ := h
  induction w using Polynomial.induction_on' with
  | add u v hu hv => rw [mul_add,map_add]; exact dvd_add hu hv
  | monomial i z =>
    rcases (by decide : ∀ x : F, x=0 ∨ x=1) z with rfl | rfl
    · simp
    · rw [← C_mul_X_pow_eq_monomial,map_one,one_mul,shift]
      exact dvd_pow_self _ (by positivity)
theorem linearized_period (m k t : ℕ) (h : (X^k+X+1 : P) ∣ X^t+1) :
    (X^(2^(m*k))+X^(2^m)+X : P) ∣ X^(2^(m*t))+X := by
  have h1 : L m 1 = X := by simpa using atom m 0
  have hx : L m X = X^(2^m) := by simpa using atom m 1
  simpa only [map_add,atom,h1,hx] using preserves_divisibility m h
private theorem reflect_expand (d : ℕ) (hd : d ≠ 0) {f g : P}
    (h : expand F d f ∣ expand F d g) : f ∣ g := by
  obtain ⟨w,hw⟩ := h
  refine ⟨contract d w,?_⟩
  have e := congrArg (contract d) hw
  rwa [contract_expand d hd,mul_comm ((expand F d) f) w,contract_mul_expand hd,mul_comm] at e
theorem lift_steps (m k t : ℕ) (hm : 1 ≤ m) (h : (X^k+X+1 : P) ∣ X^t+1) :
    let q := 2^m
    (X^((q^k-1)/(q-1))+X+1 : P) ∣ X^((q^t-1)/(q-1))+1 := by
  let q : ℕ := 2^m
  have hq : 1 < q := one_lt_pow₀ (by decide) (by omega)
  have e (i : ℕ) : (q-1)*((q^i-1)/(q-1))+1=q^i := by
    rw [Nat.mul_div_cancel' (Nat.sub_one_dvd_pow_sub_one q i)]
    have := pow_pos (by omega : 0<q) i
    omega
  change (X^((q^k-1)/(q-1))+X+1 : P) ∣ X^((q^t-1)/(q-1))+1
  apply reflect_expand (q-1) (by omega)
  apply (mul_dvd_mul_iff_left (X_ne_zero (R:=F))).mp
  have hlin := linearized_period m k t h
  simp only [map_add,map_one,map_pow,expand_X,←pow_mul]
  have v (i : ℕ) : (X : P)*X^((q-1)*((q^i-1)/(q-1)))=X^(q^i) := by
    rw [← pow_succ',e]
  have short : (X : P)*X^(q-1)=X^q := by
    rw [←pow_succ',Nat.sub_add_cancel hq.le]
  rw [mul_add,mul_add,mul_add,v,v,short,mul_one]
  simpa only [q,pow_mul] using hlin

open OMA.S_oeis_a046932
private theorem period_facts (n : ℕ) (hn : 2 ≤ n) :
    0 < a n ∧ (X^n+X+1 : P) ∣ X^(a n)+1 ∧
       ∀ t, (X^n+X+1 : P) ∣ X^t+1 → a n ∣ t := by
  let f : P := X^n+X+1
  let x := AdjoinRoot.mk f X
  have mon : f.Monic := by
    change (X^n+X+1 : P).Monic
    rw [add_assoc]
    apply monic_X_pow_add
    apply lt_of_le_of_lt (degree_add_le _ _)
    simp [show (1 : WithBot ℕ)<n by exact_mod_cast (by omega : 1<n)]
  let _ : Module.Finite F (AdjoinRoot f) := mon.finite_adjoinRoot
  let _ : Finite (AdjoinRoot f) := Module.finite_of_finite F
  have neg : -(1 : AdjoinRoot f)=1 := by
    simpa only [map_neg,map_one] using congrArg (AdjoinRoot.of f) (by decide : -(1:F)=1)
  have one (y : AdjoinRoot f) : y+1=0 ↔ y=1 := by rw [add_eq_zero_iff_eq_neg,neg]
  have roots (t : ℕ) : f ∣ X^t+1 ↔ x^t=1 := by
    rw [← AdjoinRoot.mk_eq_zero,map_add,map_pow,map_one,one]
  have h0 : x^n+x=1 := by
    apply (one _).mp
    simpa only [f,map_add,map_pow,map_one,x] using (AdjoinRoot.mk_eq_zero.mpr (dvd_refl f))
  have unit : IsUnit x := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨x^(n-1)+1,?_⟩
    rwa [mul_add,mul_one,←pow_succ',Nat.sub_add_cancel (by omega)]
  have pos := unit.isOfFinOrder.orderOf_pos
  have eq : a n = orderOf x := by
    unfold a
    have mem : orderOf x ∈ {t : ℕ | 0<t ∧ f ∣ X^t+1} := ⟨pos,(roots _).mpr (pow_orderOf_eq_one x)⟩
    apply le_antisymm (Nat.sInf_le mem)
    obtain ⟨ht,hh⟩ := Nat.sInf_mem (Set.nonempty_of_mem mem)
    exact Nat.le_of_dvd ht (orderOf_dvd_of_pow_eq_one ((roots _).mp hh))
  rw [eq]
  exact ⟨pos,(roots _).mpr (pow_orderOf_eq_one x),fun t ht => orderOf_dvd_of_pow_eq_one ((roots t).mp ht)⟩

theorem generalized_upper_divisibility (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    a ((2^(k*m)-1)/(2^m-1)) ∣ (2^(a k*m)-1)/(2^m-1) := by
  let q : ℕ := 2^m
  have hq : 1<q := one_lt_pow₀ (by decide) (by omega)
  have b : 2 ≤ (q^k-1)/(q-1) := by
    apply (Nat.le_div_iff_mul_le (by omega)).mpr
    have e := Nat.pow_le_pow_right (by omega : 0<q) hk
    rw [pow_two] at e
    have u : q-1≤q := by omega
    have h2 := Nat.mul_le_mul_left q (show 2≤q by omega)
    omega
  have lift := lift_steps m k (a k) hm (period_facts k hk).2.1
  have result := (period_facts _ b).2.2 _ lift
  simpa only [q,←pow_mul,Nat.mul_comm m] using result

end Deldor14.TrinomialPeriod
#print axioms Deldor14.TrinomialPeriod.linearized_period

#print axioms Deldor14.TrinomialPeriod.lift_steps

#print axioms Deldor14.TrinomialPeriod.generalized_upper_divisibility
