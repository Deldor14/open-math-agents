import Mathlib

/-!
# OEIS A052130: when is `m` 'sufficiently large'?

Source: https://oeis.org/A052130
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Let `N(m, n)` be the number of integers in `[1, 2^m]` with exactly `m - n` prime factors (with
multiplicity); for fixed `n` it is constant for `m` sufficiently large, and A052130 lists the
limits. The entry states (a conjecture asked about by R. G. Wilson v, see A126281) that `m` is
sufficiently large precisely when `2^m > 3^(m-n)`, for `n > 1`.

Conventions:
* '`m` is sufficiently large' means `N(m', n) = N(m, n)` for every `m' ≥ m`. `m ≥ n` (so that
  `m - n` is a genuine count), `n ≥ 2`.
-/

namespace OMA.S_oeis_a052130

/-- `N(m, n) = #{k ∈ [1, 2^m] | Ω(k) = m - n}`. -/
def N (m n : ℕ) : ℕ :=
  ((Finset.Icc 1 (2 ^ m)).filter fun k => ArithmeticFunction.cardFactors k = m - n).card

end OMA.S_oeis_a052130
namespace Deldor14.Stabilization
open Finset ArithmeticFunction OMA.S_oeis_a052130
private def row (m n : ℕ) : Finset ℕ :=
  (Icc 1 (2^m)).filter fun k => cardFactors k=m-n
private lemma row_mem (m n k : ℕ) : k ∈ row m n ↔ 1≤k ∧ k≤2^m ∧ cardFactors k=m-n := by
  simp only [row,mem_filter,mem_Icc];tauto
private lemma odd_bound (k : ℕ) (hp : 0<k) (ho : ¬2∣k) : 3^(cardFactors k) ≤ k := by
  have prod_bound (l : List ℕ) (h : ∀ p ∈ l, 3≤p) : 3^l.length ≤ l.prod := by
    induction l with
    | nil => simp
    | cons x l ih =>
      simp only [List.length_cons,List.prod_cons,pow_succ']
      exact Nat.mul_le_mul (h x (by simp)) (ih (fun p hp => h p (by simp [hp])))
  rw [cardFactors_apply]
  calc
    3^k.primeFactorsList.length ≤ k.primeFactorsList.prod := prod_bound _ ?_
    _ = k := Nat.prod_primeFactorsList hp.ne'
  intro p mem
  have low := (Nat.prime_of_mem_primeFactorsList mem).two_le
  have dvd := Nat.dvd_of_mem_primeFactorsList mem
  by_contra! h
  have : p=2 := by omega
  exact ho (this ▸ dvd)
private lemma next_iff (m n : ℕ) (hm : n ≤ m) :
    N (m+1) n = N m n ↔ 2^(m+1) < 3^(m+1-n) := by
  let evenrow := (row m n).image (fun k => 2*k)
  have dbl (k : ℕ) (hk : k≠0) : cardFactors (2*k)=1+cardFactors k := by
    rw [cardFactors_mul (by decide) hk,cardFactors_apply_prime Nat.prime_two]
  have incl : evenrow ⊆ row (m+1) n := by
    intro x hx
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hx
    obtain ⟨p,b,c⟩ := (row_mem _ _ _).mp hk
    apply (row_mem _ _ _).mpr
    rw [dbl k (by omega),c,pow_succ]
    omega
  have cc : evenrow.card = N m n := card_image_of_injective _ (fun x y h => by omega)
  constructor
  · intro h
    by_contra! b
    let w:=3^(m+1-n)
    have hw : w ∈ row (m+1) n := (row_mem _ _ _).mpr
      ⟨by dsimp [w];exact Nat.succ_le_of_lt (pow_pos (by decide : 0 < (3:ℕ)) _),b,cardFactors_apply_prime_pow (by decide : Nat.Prime 3)⟩
    have eq : evenrow=row (m+1) n := eq_of_subset_of_card_le incl (by change N (m+1) n ≤ _;omega)
    rw [←eq] at hw
    obtain ⟨z,_,hz⟩ := mem_image.mp hw
    have oddw : Odd w := (by decide : Odd (3:ℕ)).pow
    obtain ⟨j,hj⟩ := oddw
    omega
  · intro cut
    have rev : row (m+1) n ⊆ evenrow := by
      intro x hx
      obtain ⟨hp,b,c⟩ := (row_mem _ _ _).mp hx
      have ev : 2∣x := by
        by_contra ne
        have too := odd_bound x hp ne
        rw [c] at too
        omega
      obtain ⟨j,rfl⟩ := ev
      refine mem_image.mpr ⟨j,(row_mem _ _ _).mpr ?_,rfl⟩
      rw [dbl j (by omega)] at c
      rw [pow_succ] at b
      omega
    exact (congrArg Finset.card (Subset.antisymm rev incl)).trans cc
theorem corrected (n m : ℕ) (hm : n ≤ m) :
    (∀ j ≥ m, N j n=N m n) ↔ 2^(m+1)<3^(m+1-n) := by
  constructor
  · intro h; exact (next_iff m n hm).mp (h (m+1) (by omega))
  · intro h j hj
    obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hj
    have run (t : ℕ) : N (m+t) n=N m n ∧ 2^(m+t+1)<3^(m+t+1-n) := by
      induction t with
      | zero => simpa using And.intro (Eq.refl (N m n)) h
      | succ t ih =>
        constructor
        · exact ((next_iff (m+t) n (by omega)).mpr ih.2).trans ih.1
        · rw [show m+(t+1)+1=(m+t+1)+1 by omega,
            show m+t+1+1-n=(m+t+1-n)+1 by omega,pow_succ,pow_succ]
          omega
    exact (run d).1
end Deldor14.Stabilization
#print axioms Deldor14.Stabilization.corrected
