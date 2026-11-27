import OMAStatements.S_oeis_a002114
import Mathlib

open OMA.S_oeis_a002114 Finset
namespace Deldor14.Glaisher

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

private def inner (n k : ℕ) : ℤ :=
  ∑ j ∈ range (2*k+1),(-1:ℤ)^j*((2*k).choose j:ℤ)*((k:ℤ)-j)^(2*n)

private def numerator (n : ℕ) : ℤ := ∑ k ∈ range (n+1),(-1:ℤ)^(n+k)*inner n k

private theorem asDiff (n k : ℕ) : inner n k =
    delta (2*k) (fun x : ℕ => ((x:ℤ)-(k:ℤ))^(2*n)) 0 := by
  let f : ℕ → ℤ := fun x => ((x:ℤ)-(k:ℤ))^(2*n)
  have bridge (j x : ℕ) : delta j f x=(fwdDiff 1)^[j] f x := by
    induction j generalizing x with
    | zero => rfl
    | succ j ih =>
      rw [delta,Function.iterate_succ_apply',fwdDiff,ih,ih]
  rw [bridge (2*k) 0,fwdDiff_iter_eq_sum_shift]
  unfold inner
  apply sum_congr rfl; intro j hj
  have le : j≤2*k := by simpa using hj
  have sign : (-1:ℤ)^(2*k-j)=(-1:ℤ)^j := by
    rw [neg_one_pow_eq_ite,neg_one_pow_eq_ite]
    have e : Even (2*k-j) ↔ Even j := by simp only [Nat.even_iff];omega
    simp only [e]
  simp only [f,sign,zero_add,nsmul_eq_mul,mul_one,zsmul_eq_mul,Int.cast_id,Nat.cast_id]
  rw [show (j:ℤ)-k = -((k:ℤ)-j) by ring,(even_two.mul_right n).neg_pow]

private theorem factor (n k : ℕ) : ((2*k).factorial:ℤ) ∣ inner n k := by
  rw [asDiff]
  let c : ℕ → ℤ := fun i => (-(k:ℤ))^(2*n-i)*((2*n).choose i:ℤ)
  have expand (x : ℕ) : ((x:ℤ)-k)^(2*n) = ∑ i ∈ range (2*n+1),c i*(x:ℤ)^i := by
    rw [sub_eq_add_neg,add_pow]; apply sum_congr rfl; intro i hi; dsimp [c];ring
  simp_rw [expand]
  rw [linear]
  apply Finset.dvd_sum
  intro i hi
  rw [stirling]
  exact dvd_mul_of_dvd_right (dvd_mul_right _ _) _

private theorem halfMod {m : ℕ} {u v : ℤ} (h : u ≡ v [ZMOD (2*(m:ℤ))]) :
    u/2 ≡ v/2 [ZMOD (m:ℤ)] := by
  obtain ⟨t,ht⟩ := Int.modEq_iff_dvd.mp h
  have ev : v=u+(m*t)*2 := by linarith
  rw [ev,Int.add_mul_ediv_right _ _ (by decide : (2:ℤ)≠0),Int.modEq_iff_dvd]
  use t;ring

private theorem truncSum (m b n : ℕ) (hm : 0 < m) (cut : m≤2*b) (hn : b≤n) :
    numerator n ≡ ∑ k ∈ range b,(-1:ℤ)^(n+k)*inner n k [ZMOD (m:ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff]
  simp only [numerator,Int.cast_sum,Int.cast_mul]
  symm; apply sum_subset (range_mono (by omega))
  intro k hk h
  have le : m≤2*k := by simp only [mem_range,not_lt] at h; omega
  have fac : (m:ℤ) ∣ ((2*k).factorial:ℤ) := by exact_mod_cast Nat.dvd_factorial hm le
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr (fac.trans (factor n k)),mul_zero]

private theorem samePowers (m : ℕ) (hm : 0 < m) : ∃ N : ℕ,∀ n ≥ N,∀ x : ℤ,
    x^(2*(n+m.totient)) ≡ x^(2*n) [ZMOD (2*(m:ℤ))] := by
  obtain ⟨N,p⟩ := powerPeriod (2*m) (by omega)
  refine ⟨N,?_⟩;intro n hn x
  have d : (2*m).totient ∣ 2*m.totient := by
    rcases Nat.even_or_odd m with e|o
    · rw [Nat.totient_two_mul_of_even e]
    · rw [Nat.totient_two_mul_of_odd o]; exact dvd_mul_left _ _
  obtain ⟨t,ht⟩ := d
  have q := p (2*n) (by omega) x.natAbs t
  rw [← ht,← Nat.mul_add] at q
  have z : ((x.natAbs:ℤ)^(2*(n+m.totient))) ≡ (x.natAbs:ℤ)^(2*n) [ZMOD (2*(m:ℤ))] := by
    exact_mod_cast q
  simpa [Int.natCast_natAbs,← abs_pow,pow_mul,abs_of_nonneg (sq_nonneg x)] using z


private theorem parity (n : ℕ) (hn : 2≤n) : numerator n ≡ 2 [ZMOD 4] := by
  have t := truncSum 4 2 n (by decide) (by decide) hn
  have a0 : inner n 0=0 := by norm_num [inner,show 2*n≠0 by omega]
  have a1 : inner n 1=2 := by
    simp [inner,sum_range_succ,pow_mul,show n≠0 by omega]
  apply t.trans
  simp only [sum_range_succ,sum_range_zero,a0,a1,mul_zero,add_zero,zero_add]
  rw [neg_one_pow_eq_ite]
  split <;> decide

theorem result : type_of% @OMA.S_oeis_a002114.main := by
  intro m hm
  by_cases small : m≤2
  · rcases (show m=1 ∨ m=2 by omega) with rfl|rfl
    · exact ⟨1,1,by decide,by decide,by decide,fun _ _ => by change _ % 1 = _ % 1; omega⟩
    · refine ⟨1,2,by decide,by decide,by decide,?_⟩
      intro n hn
      exact halfMod (m := 2) ((parity (n+1) (by omega)).trans (parity n hn).symm)
  obtain ⟨N,p⟩ := samePowers m hm
  refine ⟨m.totient,max N (2*m),Nat.totient_pos.mpr hm,dvd_rfl,by omega,?_⟩
  intro n hn
  apply halfMod
  change numerator (n+m.totient) ≡ numerator n [ZMOD (2*(m:ℤ))]
  have tr (r : ℕ) (hr : m≤r) : numerator r ≡
      ∑ k ∈ range m,(-1:ℤ)^(r+k)*inner r k [ZMOD (2*(m:ℤ))] := by
    exact_mod_cast truncSum (2*m) m r (by omega) (by omega) hr
  apply (tr _ (by omega)).trans
  apply Int.ModEq.trans _ (tr n (by omega)).symm
  apply Int.ModEq.sum
  intro k _
  have sign : (-1:ℤ)^(n+m.totient+k)=(-1:ℤ)^(n+k) := by
    rw [show n+m.totient+k=n+k+m.totient by omega,pow_add,(Nat.totient_even (by omega : 2 < m)).neg_one_pow,mul_one]
  rw [sign]
  apply Int.ModEq.mul_left
  apply Int.ModEq.sum
  intro j _
  exact (p n (by omega) ((k:ℤ)-j)).mul_left _

end Deldor14.Glaisher
theorem OMA.solution : type_of% @OMA.S_oeis_a002114.main := Deldor14.Glaisher.result
