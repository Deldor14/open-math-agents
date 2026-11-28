import DivisorCover
import Mathlib.NumberTheory.Chebyshev

namespace ProgressionParity

theorem explicit_residue_spread {p N x : ℕ} (hp : Nat.Prime p) (size : 2<N) (room : p*(p-1)≤N)
    (A:Finset ℕ) (inside : A⊆Finset.Icc 1 N) (free : Free (·∈A) p) (hx : x∈A) :
    (((p:ℝ)-1)*Real.log 2-Real.log p)/Real.log ((N:ℝ)-1) ≤ (otherHoles A N p x).card := by
  have raw := residue_spread hp room A inside free hx
  change Nat.lcmUpto (p-1) ≤ (N-1)^(otherHoles A N p x).card at raw
  have cp := Nat.pos_of_ne_zero (Nat.lcmUpto_ne_zero (p-1))
  have cmp : ((Nat.lcmUpto (p-1):ℕ):ℝ) ≤ ((N-1:ℕ):ℝ)^(otherHoles A N p x).card := by
    exact_mod_cast raw
  have logcmp := Real.log_le_log (by exact_mod_cast cp) cmp
  rw [Real.log_pow, Nat.cast_sub (by omega : 1≤N),Nat.cast_one] at logcmp
  have lower := Chebyshev.psi_ge (p-1)
  rw [Chebyshev.psi_eq_log_lcmUpto] at lower
  have ppos := hp.one_lt
  have id : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤p),Nat.cast_one]
  rw [id,sub_add_cancel] at lower
  have base : 1<(N:ℝ)-1 := by
    have h : (2:ℝ)<N := by exact_mod_cast size
    linarith
  exact (div_le_iff₀ (Real.log_pos base)).mpr (lower.trans logcmp)

#print axioms explicit_residue_spread
end ProgressionParity
