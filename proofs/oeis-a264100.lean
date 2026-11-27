import OMAStatements.S_oeis_a264100
import Mathlib

open OMA.S_oeis_a264100 Finset

/-- Each allowable length k+1 gains one common difference exactly when k divides n+1. -/
theorem OMA.solution : type_of% @OMA.S_oeis_a264100.main := by
  intro n
  have delta (r : ℕ) : totalLength (r+1)-totalLength r=endingWeight r := by
    simp [totalLength,sum_range_succ]
  rw [delta (n+1),delta n]
  let S := Icc 1 (n+1)
  have expand : endingWeight n=1+∑ k ∈ S,(k+1)*(n/k) := by
    unfold endingWeight
    congr 1
    apply sum_subset (Icc_subset_Icc_right (by omega))
    intro k hk h
    simp only [S,mem_Icc] at hk h
    rw [Nat.div_eq_of_lt (by omega : n<k),mul_zero]
  have update (k : ℕ) (hk : k∈S) :
      (k+1)*((n+1)/k)=(k+1)*(n/k)+(if k ∣ n+1 then k+1 else 0) := by
    have pos := (mem_Icc.mp hk).1
    by_cases divides : k ∣ n+1
    · simp [Nat.succ_div_of_dvd divides,divides,mul_add]
    · simp [Nat.succ_div_of_not_dvd divides,divides]
  have divisors : S.filter (fun k => k ∣ n+1)=(n+1).divisors := by
    ext k
    simp only [S,mem_filter,mem_Icc,Nat.mem_divisors]
    exact ⟨fun h => ⟨h.2,by omega⟩,fun d => ⟨⟨Nat.pos_of_dvd_of_pos d.1 (by omega),Nat.le_of_dvd (by omega) d.1⟩,d.1⟩⟩
  rw [expand,endingWeight]
  change (1+(∑ k ∈ S,(k+1)*((n+1)/k))) - _ = _
  rw [sum_congr rfl update,sum_add_distrib,← sum_filter,divisors,sum_add_distrib]
  simp <;> omega
