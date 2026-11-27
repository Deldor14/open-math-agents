import OMAStatements.S_oeis_a002791
import Mathlib

open OMA.S_oeis_a002791

theorem OMA.solution : type_of% @OMA.S_oeis_a002791.main := by
  intro n hn
  have split := Finset.sum_filter_add_sum_filter_not n.divisors (fun d => d ≤ 4) (fun d => d)
  simp only [not_le] at split
  have small : n.divisors.filter (· ≤ 4) = ({1,2,3,4} : Finset ℕ).filter (· ∣ n) := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_insert,Finset.mem_singleton]
    have nz : n≠0 := by omega
    have pos (h : d ∣ n) : 0 < d := Nat.pos_of_dvd_of_pos h hn
    constructor
    · rintro ⟨⟨h,_⟩,u⟩
      exact ⟨by have := pos h; omega,h⟩
    · rintro ⟨h,u⟩
      exact ⟨⟨u,nz⟩,by omega⟩
  unfold a
  rw [ArithmeticFunction.sigma_one_apply,← split,small]
  simp only [Finset.sum_filter,Finset.sum_insert (by decide : (1:ℕ) ∉ {2,3,4}),
    Finset.sum_insert (by decide : (2:ℕ) ∉ {3,4}),Finset.sum_insert (by decide : (3:ℕ) ∉ {4}),
    Finset.sum_singleton,one_dvd,if_true]
  have bound := Nat.mod_lt n (by decide : 0<6)
  generalize eq : n%6=r at *
  interval_cases r <;> norm_num [f] <;>
    split_ifs <;> push_cast <;> omega
