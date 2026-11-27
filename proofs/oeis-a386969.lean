import OMAStatements.S_oeis_a386969
import Mathlib

open OMA.S_oeis_a386969

namespace Deldor14.Recaman

def value (n : ℕ) : ℕ :=
  if n=0 then 0 else if n=1 then 4 else if n=2 then 2
  else if n%2=0 then 2*n+7 else n+5

theorem large (n : ℕ) (h : 3≤n) : value n = if n%2=0 then 2*n+7 else n+5 := by
  simp [value,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega]

theorem formula (a : ℕ → ℕ) (hz : a 0=0) (hs : ∀ n, a (n+1)=nextValue a n) :
    ∀ n, a n=value n := by
  have one : a 1=4 := by rw [hs 0]; simp [nextValue,hz]
  have two : a 2=2 := by
    change a (1+1) = 2
    rw [hs 1]
    have all : ∀ i : Fin 2, a i ≠ 2 := by intro i; fin_cases i <;> simp [hz,one]
    simpa [nextValue,one,all]
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain _ | m := n
    · exact hz
    by_cases small : m < 3
    · interval_cases m
      · exact one
      · exact two
      · rw [hs]; simp [nextValue,two,value]
    have hm := ih m (by omega)
    rw [hs]
    by_cases even : m%2=0
    · have hm' : a m=2*m+7 := by simpa only [large m (by omega), if_pos even] using hm
      have unused : ∀ i : Fin (m+1), a i ≠ a m-(m+1) := by
        intro i
        rw [ih i i.isLt,hm']
        have bound := i.isLt
        unfold value
        split_ifs <;> omega
      rw [nextValue,if_pos ⟨by omega,unused⟩,hm',large (m+1) (by omega),
        if_neg (by omega : ¬ (m+1)%2=0)]
      omega
    · have hm' : a m=m+5 := by simpa only [large m (by omega), if_neg even] using hm
      have seen : ¬ (m+1 ≤ a m ∧ ∀ i : Fin (m+1), a i ≠ a m-(m+1)) := by
        intro h
        exact h.2 ⟨1,by omega⟩ (by change a 1 = _; omega)
      rw [nextValue,if_neg seen,hm']
      unfold value
      split_ifs <;> omega

end Deldor14.Recaman
open Deldor14.Recaman

theorem OMA.solution : type_of% @OMA.S_oeis_a386969.main := by
  intro a hz hs
  have form := formula a hz hs
  constructor
  · intro n hn
    simpa [value,show n≠0 by omega,show n≠1 by omega,show n≠2 by omega] using form n
  · intro n
    simp only [lag,form]
    by_cases hn : n ≤ 6
    · interval_cases n <;> decide
    · have num : numerator n=0 := by
        unfold numerator
        split <;> omega
      rw [num,if_pos (by omega : 2≤n),if_pos (by omega : 4≤n)]
      rw [large n (by omega),large (n-2) (by omega),large (n-4) (by omega)]
      split_ifs <;> omega
