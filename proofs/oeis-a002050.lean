import OMAStatements.S_oeis_a002050
import Mathlib

open OMA.S_oeis_a002050 Finset
namespace Deldor14.OrderedBell

/-- Euler's period works simultaneously for all bases after a bounded number
of powers. For prime powers a nonunit becomes zero. The CRT combines the bounds. -/
private theorem powerPeriod (m : ℕ) : 0 < m → ∃ N : ℕ, ∀ n ≥ N, ∀ x t : ℕ,
    x^(n+m.totient*t) ≡ x^n [MOD m] := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => exact fun _ => ⟨0,fun _ _ _ _ => Nat.modEq_one⟩
  | prime_pow p k hp hk =>
    intro _
    refine ⟨k,?_⟩
    intro n hn x t
    by_cases d : p ∣ x
    · have z : p^k ∣ x^n := (pow_dvd_pow_of_dvd d k).trans (pow_dvd_pow x hn)
      rw [pow_add]
      exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left z _)).trans
        (Nat.modEq_zero_iff_dvd.mpr z).symm
    · have co : Nat.Coprime x (p^k) := (hp.coprime_iff_not_dvd.mpr d).symm.pow_right _
      rw [pow_add,pow_mul]
      simpa using ((Nat.ModEq.pow_totient co).pow t).mul_left (x^n)
  | coprime a b ha hb cop ia ib =>
    intro _
    obtain ⟨A,hA⟩ := ia (by omega)
    obtain ⟨B,hB⟩ := ib (by omega)
    refine ⟨max A B,?_⟩
    intro n hn x t
    apply (Nat.modEq_and_modEq_iff_modEq_mul cop).mp
    rw [Nat.totient_mul cop]
    constructor
    · simpa [mul_assoc] using hA n (le_trans (le_max_left ..) hn) x (b.totient*t)
    · simpa [mul_assoc,mul_left_comm,mul_comm] using hB n (le_trans (le_max_right ..) hn) x (a.totient*t)

variable {R : Type} [CommRing R]

private def delta : ℕ → (ℕ → R) → ℕ → R
  | 0,f,x => f x
  | j+1,f,x => delta j f (x+1)-delta j f x

private theorem diffConst (j x : ℕ) (c : R) : delta (j+1) (fun _ => c) x=0 := by
  induction j generalizing x with
  | zero => simp [delta]
  | succ j ih => rw [delta,ih,ih,sub_self]

private theorem diffX (j x : ℕ) (f : ℕ → R) :
    delta (j+1) (fun y => (y:R)*f y) x =
      ((x:R)+j+1)*delta (j+1) f x + (j+1:R)*delta j f x := by
  induction j generalizing x with
  | zero => simp [delta]; ring
  | succ j ih =>
    rw [delta,ih,ih]
    simp only [delta,Nat.cast_add_one]
    ring

private theorem stirling (n j : ℕ) :
    delta j (fun x : ℕ => (x:R)^n) 0 = (j.factorial:R)*Nat.stirlingSecond n j := by
  induction n generalizing j with
  | zero =>
    cases j with
    | zero => simp [delta]
    | succ j => simp [diffConst]
  | succ n ih =>
    cases j with
    | zero => simp [delta]
    | succ j =>
      simp only [pow_succ',diffX,Nat.cast_zero,zero_add,ih,Nat.factorial_succ,
        Nat.stirlingSecond_succ_succ,Nat.cast_add,Nat.cast_mul,Nat.cast_add_one]
      ring

private theorem linear (j n x : ℕ) (c : ℕ → R) (f : ℕ → ℕ → R) :
    delta j (fun y => ∑ i ∈ range n,c i*f i y) x =
      ∑ i ∈ range n,c i*delta j (f i) x := by
  induction j generalizing x with
  | zero => rfl
  | succ j ih =>
    rw [delta,ih,ih,← sum_sub_distrib]
    apply sum_congr rfl
    intro i _; simp [delta,mul_sub]

private theorem truncated (m n : ℕ) (hm : 0 < m) :
    (orderedBell n : ZMod m) =
      ∑ j ∈ range m,delta j (fun x : ℕ => (x:ZMod m)^n) 0 := by
  simp only [orderedBell,Nat.cast_sum,Nat.cast_mul,stirling]
  let f := fun j : ℕ => (j.factorial:ZMod m)*Nat.stirlingSecond n j
  change (∑ j ∈ range (n+1), f j)=∑ j ∈ range m,f j
  by_cases lim : n+1 ≤ m
  · apply sum_subset (range_mono lim)
    intro j _ outside
    simp only [mem_range,not_lt] at outside
    simp [f,Nat.stirlingSecond_eq_zero_of_lt (show n<j by omega)]
  · symm
    apply sum_subset (range_mono (by omega))
    intro j _ outside
    simp only [mem_range,not_lt] at outside
    have z : (j.factorial : ZMod m)=0 := by
      exact (ZMod.natCast_eq_zero_iff ..).mpr (Nat.dvd_factorial hm outside)
    simp [f,z]

private theorem transform (m n : ℕ) (hm : 0 < m) : (a n : ZMod m)+1 =
    ∑ j ∈ range m,delta j (fun x : ℕ => ((x:ZMod m)+1)^n) 0 := by
  have zeroth : orderedBell 0=1 := by decide
  have split : insert 0 (Icc 1 n)=range (n+1) := by
    ext x; simp; omega
  have all : (a n : ZMod m)+1 = ∑ k ∈ range (n+1),(n.choose k : ZMod m)*orderedBell k := by
    rw [← split,sum_insert (by simp)]
    simp [a,zeroth,add_comm]
  rw [all]
  simp_rw [truncated m _ hm,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← linear]
  congr 2
  funext x
  rw [add_pow]
  apply sum_congr rfl
  intro i _; simp [mul_comm]

theorem result : type_of% @OMA.S_oeis_a002050.main := by
  intro m hm
  obtain ⟨N,per⟩ := powerPeriod m hm
  refine ⟨m.totient,N,Nat.totient_pos.mpr hm,dvd_rfl,?_⟩
  intro n hn
  apply (ZMod.natCast_eq_natCast_iff ..).mp
  apply add_right_cancel (b := (1:ZMod m))
  rw [transform m _ hm,transform m _ hm]
  have same : (fun x : ℕ => ((x:ZMod m)+1)^(n+m.totient)) =
      (fun x : ℕ => ((x:ZMod m)+1)^n) := by
    funext x
    have e := (ZMod.natCast_eq_natCast_iff ..).mpr (per n hn (x+1) 1)
    simpa using e
  rw [same]
end Deldor14.OrderedBell

theorem OMA.solution : type_of% @OMA.S_oeis_a002050.main := Deldor14.OrderedBell.result
