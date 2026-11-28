import SubgoldenPropagation
import SubgoldenRoth

/-! A kernel-checked dilation strictly below the golden ratio. -/
namespace Erdos142SubgoldenCertified
open Erdos142Subgolden Erdos142SubgoldenRoth

abbrev a₀ : ℕ := 4562434482930074992257302805716424014589
abbrev b₀ : ℕ := 6843651724395112488385954208574636021885
abbrev A : ℕ := 1228486447903706602897128832867410584139008865935410435140931996515083613738234
abbrev B : ℕ := 1987732827426824293039715854248087351655413086765588296069533904065114759739395

theorem endpoints : orbit a₀ b₀ 92 = (A,B) := by decide +kernel

def cost : ℕ := C*loss a₀ b₀ 92 + 2^92

theorem less_than_golden : A < B ∧ B^2 < A*B + A^2 := by decide

set_option maxRecDepth 12000 in
theorem grid (t : ℕ) : (cost+1)*rothNumberNat (A*t) ≤ cost*rothNumberNat (B*t) := by
  have hseed := digit (a := a₀) (b := B) (by decide) t
  have hs : (C:ℤ)*profile t a₀ ≤ profile t (orbit a₀ b₀ 92).2 := by simpa only [endpoints] using hseed
  have h := relative_gain (profile t) (mono t) (sub t) (glue t) a₀ b₀ 92 C (by decide) hs
  rw [endpoints] at h
  have co : (cost : ℤ) = (C:ℤ)*(loss a₀ b₀ 92:ℤ)+(2:ℤ)^92 := by
    unfold cost
    push_cast
    rfl
  rw [← co] at h
  change (rothNumberNat (A*t):ℤ) ≤ (cost:ℤ)*((rothNumberNat (B*t):ℤ)-(rothNumberNat (A*t):ℤ)) at h
  have hv : ((cost:ℤ)+1)*(rothNumberNat (A*t):ℤ) ≤ (cost:ℤ)*(rothNumberNat (B*t):ℤ) := by nlinarith only [h]
  exact_mod_cast hv

/-- Strict growth at every sufficiently large integer, at a specified rational below φ. -/
theorem eventual : ∃ N, ∀ n ≥ N, (2*cost+1)*rothNumberNat n ≤ 2*cost*rothNumberNat (B*n/A) :=
  round_grid (by decide : 0<A) grid

#print axioms endpoints
#print axioms less_than_golden
#print axioms grid
#print axioms eventual
end Erdos142SubgoldenCertified
