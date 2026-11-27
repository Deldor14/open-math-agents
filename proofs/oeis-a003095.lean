import OMAStatements.S_oeis_a003095
import Mathlib

open OMA.S_oeis_a003095
namespace Deldor14.Periods

theorem propagate {M x y : ℕ} (h : a x ≡ a y [MOD M]) (s : ℕ) :
    a (x+s) ≡ a (y+s) [MOD M] := by
  induction s with
  | zero => exact h
  | succ s ih => exact (ih.pow 2).add_right 1

theorem block (j : ℕ) : a (6*j+1) ≡ a 1 [MOD 20] := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 6*(j+1)+1 = (6*j+1)+6 by omega]
    exact (propagate ih 6).trans (by decide +kernel)

theorem residue (j r : ℕ) (hr : 1≤r) : a (6*j+r) ≡ a r [MOD 20] := by
  convert propagate (block j) (r-1) using 1 <;> congr 1 <;> omega

theorem gain {M B x y : ℕ} (h : a x ≡ a y [MOD M]) (hh : B ∣ a x+a y) :
    a (x+1) ≡ a (y+1) [MOD M*B] := by
  apply Nat.modEq_iff_dvd.mpr
  have h₁ := Nat.modEq_iff_dvd.mp h
  have h₂ : (B:ℤ) ∣ (a x:ℤ)+a y := by exact_mod_cast hh
  obtain ⟨v,hv⟩ := h₁
  obtain ⟨w,hw⟩ := h₂
  refine ⟨v*w,?_⟩
  simp only [a, Nat.cast_add, Nat.cast_pow, Nat.cast_mul,Nat.cast_one]
  linear_combination ((a x:ℤ)+a y)*hv + (M:ℤ)*v*hw

theorem contact (j t B : ℕ) (d : B∣20) (h : B∣a 6+a (6+t)) :
    B ∣ a (6*j+6)+a (6*j+6+t) := by
  have r := ((residue j 6 (by decide)).add (residue j (6+t) (by omega))).of_dvd d
  rw [←Nat.add_assoc] at r
  exact (Nat.modEq_zero_iff_dvd.mp (r.trans (Nat.modEq_zero_iff_dvd.mpr h)))

theorem event (t B : ℕ) (d : B∣20) (hit : B∣a 6+a (6+t)) (k : ℕ) :
    ∃ N, ∀ n ≥ N, a (n+t) ≡ a n [MOD B^k] := by
  induction k with
  | zero => exact ⟨0,fun n _ => Nat.modEq_one⟩
  | succ k ih =>
    obtain ⟨N,hN⟩ := ih
    let j := 6*N+6
    have middle := hN j (by dsimp [j]; omega)
    have touch : B ∣ a (j+t)+a j := by
      rw [add_comm]; exact contact N t B d hit
    have next := gain middle touch
    refine ⟨j+1,fun n hn => ?_⟩
    have step := propagate next (n-(j+1))
    rw [show j+t+1+(n-(j+1))=n+t by omega,show j+1+(n-(j+1))=n by omega] at step
    simpa only [pow_succ] using step

theorem minimal {t B small : ℕ} (d : small∣20) (e : small∣B)
    (diff : ∀ q, 0 < q → q < t → ¬ a (6+q) ≡ a 6 [MOD small])
    (k : ℕ) (hk : 0 < k) (q : ℕ) (qpos : 0 < q) (qt : q < t) :
    ¬ ∃ N, ∀ n ≥ N, a (n+q) ≡ a n [MOD B^k] := by
  rintro ⟨N,hN⟩
  have now := (hN (6*N+6) (by omega)).of_dvd (e.trans (dvd_pow_self B hk.ne'))
  have r := (residue N (6+q) (by omega)).of_dvd d
  rw [← Nat.add_assoc] at r
  exact diff q qpos qt ((r.symm.trans now).trans ((residue N 6 (by decide)).of_dvd d))

end Deldor14.Periods
open Deldor14.Periods

theorem OMA.solution : type_of% @OMA.S_oeis_a003095.main := by
  intro k hk
  have two : ∀ q, 0 < q → q < 2 → ¬ a (6+q) ≡ a 6 [MOD 2] := by
    intro q hp ht; interval_cases q <;> decide +kernel
  have ten : ∀ q, 0 < q → q < 6 → ¬ a (6+q) ≡ a 6 [MOD 10] := by
    intro q hp ht; interval_cases q <;> decide +kernel
  exact ⟨⟨event 2 2 (by decide) (by decide +kernel) k,
     minimal (by decide : 2∣20) (by decide : 2∣2) two k hk⟩,
    ⟨event 6 10 (by decide) (by decide +kernel) k,
     minimal (by decide : 10∣20) (by decide : 10∣10) ten k hk⟩,
    ⟨event 6 20 (by decide) (by decide +kernel) k,
     minimal (by decide : 10∣20) (by decide : 10∣20) ten k hk⟩⟩
