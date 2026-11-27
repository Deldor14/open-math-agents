import OMAStatements.S_oeis_a008784
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a008784.main := by
  intro k hk
  letI : NeZero k := ⟨by omega⟩
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x.val+k,(ZMod.natCast_eq_zero_iff _ k).mp ?_,?_⟩
    · push_cast
      simp [ZMod.natCast_self,hx]
    · have hle : k ≤ x.val+k := by omega
      have hsq := Nat.le_self_pow (by decide : 2≠0) (x.val+k)
      omega
  · rintro ⟨m,hm,_⟩
    refine ⟨m,?_⟩
    have h := (ZMod.natCast_eq_zero_iff _ k).mpr hm
    push_cast at h
    exact eq_neg_of_add_eq_zero_left h
