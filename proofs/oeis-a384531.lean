import OMAStatements.S_oeis_a384531
import Mathlib

/- Formalization of Werner Schulte's adjacent-gcd identity; see also
David Radcliffe, Notes on two arithmetical functions, linked from OEIS A384531. -/
namespace Deldor14.Schulte
open Finset

def term (n i : ℕ) := (i+1).gcd n * (i+2).gcd n
def total (n : ℕ) := ∑ i ∈ range n, term n i
def pillai (n : ℕ) := ∑ i ∈ range n, i.gcd n

def residuePairs {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (co : m.Coprime n) :
    Fin (m*n) ≃ Fin m × Fin n where
  toFun i := (⟨i.val%m,Nat.mod_lt _ hm⟩,⟨i.val%n,Nat.mod_lt _ hn⟩)
  invFun v := ⟨Nat.chineseRemainder co v.1.val v.2.val,
    Nat.chineseRemainder_lt_mul co _ _ hm.ne' hn.ne'⟩
  left_inv i := by
    apply Fin.ext
    apply Nat.ModEq.eq_of_lt_of_lt _ (Nat.chineseRemainder_lt_mul co _ _ hm.ne' hn.ne') i.isLt
    exact (Nat.chineseRemainder_modEq_unique co (Nat.mod_modEq _ _).symm (Nat.mod_modEq _ _).symm).symm
  right_inv v := by
    apply Prod.ext <;> apply Fin.ext
    · have h := (Nat.chineseRemainder co v.1.val v.2.val).property.1
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt v.1.isLt] using h
    · have h := (Nat.chineseRemainder co v.1.val v.2.val).property.2
      simpa only [Nat.ModEq,Nat.mod_eq_of_lt v.2.isLt] using h

theorem multiplicative (m n : ℕ) (co : m.Coprime n) : total (m*n)=total m*total n := by
  by_cases hm : m=0
  · simp [hm,total]
  by_cases hn : n=0
  · simp [hn,total]
  let e := residuePairs (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) co
  have edge (i : Fin (m*n)) : term (m*n) i.val =
      term m (e i).1.val * term n (e i).2.val := by
    have lm := Nat.mod_modEq i.val m
    have ln := Nat.mod_modEq i.val n
    change _ = term m (i.val%m) * term n (i.val%n)
    simp only [term,co.gcd_mul,(lm.add_right 1).gcd_eq,(lm.add_right 2).gcd_eq,
      (ln.add_right 1).gcd_eq,(ln.add_right 2).gcd_eq]
    ring
  unfold total
  simp only [← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ x : Fin m × Fin n, term m x.1.val * term n x.2.val :=
      Fintype.sum_equiv e _ _ edge
    _ = _ := by rw [Fintype.sum_prod_type]; simp only [← Finset.mul_sum,← Finset.sum_mul]

theorem shift (f : ℕ → ℕ) (n : ℕ) (period : f n=f 0) :
    (∑ i ∈ range n, f (i+1)) = ∑ i ∈ range n, f i := by
  have edge := Finset.sum_range_succ' f n
  rw [Finset.sum_range_succ,period] at edge
  omega

theorem block_sum (f : ℕ → ℕ) (k p : ℕ) :
    (∑ i ∈ range (k*p), f i) = ∑ j ∈ range k, ∑ r ∈ range p, f (j*p+r) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem single_block {p : ℕ} (prime : p.Prime) (e j : ℕ) :
    (∑ r ∈ range p, (j*p+r).gcd (p^(e+1))) = p*(j.gcd (p^e))+(p-1) := by
  let f := fun r : ℕ => (j*p+r).gcd (p^(e+1))
  have pos := prime.pos
  have off {r : ℕ} (hr : r<p-1) : f (r+1)=1 := by
    have nod : ¬p∣j*p+(r+1) := by
      intro h
      have bad : p ∣ r+1 := (Nat.dvd_add_iff_right (dvd_mul_left p j)).mpr h
      have := Nat.le_of_dvd (by omega : 0<r+1) bad
      omega
    exact ((prime.coprime_iff_not_dvd.mpr nod).symm.pow_right _).gcd_eq_one
  have s : (∑ r ∈ range (p-1), f (r+1))=p-1 := by
    calc _ = ∑ _r ∈ range (p-1), 1 := Finset.sum_congr rfl (fun r hr => off (mem_range.mp hr))
         _ = _ := by simp
  change (∑ r ∈ range p, f r) = _
  conv_lhs => rw [show p=p-1+1 by omega,Finset.sum_range_succ',s]
  have f0 : f 0=p*(j.gcd (p^e)) := by
    simp only [f,add_zero,pow_succ,Nat.gcd_mul_right]
    exact Nat.mul_comm _ _
  rw [f0]; omega

theorem pillai_step {p : ℕ} (prime : p.Prime) (e : ℕ) :
    pillai (p^(e+1))=p*pillai (p^e)+p^e*(p-1) := by
  unfold pillai
  conv_lhs => arg 1; rw [pow_succ]
  rw [block_sum]
  simp only [single_block prime,Finset.sum_add_distrib,← Finset.mul_sum]
  simp

theorem pillai_prime {p : ℕ} (prime : p.Prime) (e : ℕ) :
    pillai (p^(e+1))=(p+(e+1)*(p-1))*p^e := by
  induction e with
  | zero => rw [pillai_step prime]; simp [pillai]
  | succ e ih => rw [pillai_step prime,ih,pow_succ]; ring

theorem adjacent_prime {p : ℕ} (prime : p.Prime) (e : ℕ) :
    total (p^e)+p^e = 2*pillai (p^e) := by
  let n := p^e
  have single (i : ℕ) : term n i+1=(i+1).gcd n+(i+2).gcd n := by
    have unit {j : ℕ} (h : ¬p∣j) : j.gcd n=1 :=
      ((prime.coprime_iff_not_dvd.mpr h).symm.pow_right _).gcd_eq_one
    by_cases h : p∣i+1
    · have no : ¬p∣i+2 := by
        intro both
        have one : p∣1 := (Nat.dvd_add_iff_right h).mpr both
        exact prime.not_dvd_one one
      simp [term,unit no]
    · simp [term,unit h,Nat.add_comm (Nat.gcd _ _) 1]
  have first := shift (fun i => i.gcd n) n (by simp)
  have second := shift (fun i => (i+1).gcd n) n (by simp)
  change (∑ i ∈ range n, (i+2).gcd n) = ∑ i ∈ range n, (i+1).gcd n at second
  change total n+n=2*pillai n
  unfold total pillai
  calc
    _ = ∑ i ∈ range n, (term n i+1) := by simp [Finset.sum_add_distrib]
    _ = _ := by simp only [single,Finset.sum_add_distrib]; omega

theorem local_formula {p : ℕ} (prime : p.Prime) (e : ℕ) :
    total (p^(e+1))= ((2*(e+1)+1)*p-2*(e+1))*p^e := by
  have edge := adjacent_prime prime (e+1)
  rw [pillai_prime prime,pow_succ] at edge
  obtain ⟨r,pr⟩ : ∃ r, p=r+1 := ⟨p-1,by have := prime.pos; omega⟩
  have h : (2*(e+1)+1)*p - 2*(e+1) = (2*(e+1)+1)*r+1 := by rw [pr,Nat.mul_add]; omega
  rw [h]
  rw [pr] at edge ⊢
  simp only [Nat.add_sub_cancel] at edge
  rw [pow_succ]
  nlinarith

end Deldor14.Schulte

open Finset OMA.S_oeis_a384531 Deldor14.Schulte

theorem OMA.solution : type_of% @OMA.S_oeis_a384531.main := by
  intro n hn
  change a n = total n
  rw [Nat.multiplicative_factorization total multiplicative (by decide +kernel) hn.ne']
  apply Finset.prod_congr rfl
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have pos := prime.factorization_pos_of_dvd hn.ne' (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨e,he⟩ : ∃ e, n.factorization p=e+1 := ⟨n.factorization p-1,by omega⟩
  change ((2*n.factorization p+1)*p-2*n.factorization p)*p^(n.factorization p-1)=total (p^n.factorization p)
  rw [he,local_formula prime]
  simp
