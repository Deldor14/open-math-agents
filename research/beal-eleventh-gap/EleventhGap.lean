import Mathlib

namespace EleventhGap

def poly (x s : ℝ) : ℝ :=
  x^5 + 55*x^4*s + 330*x^3*s^2 + 462*x^2*s^3 + 165*x*s^4 + 11*s^5

theorem symmetric (a b : ℝ) :
    1024*(a^11+b^11) = (a+b)*poly ((a+b)^2) ((a-b)^2) := by
  unfold poly
  ring

theorem fifth_gap {x s : ℝ} (hs : 1 ≤ s) (hx : 1024*s^2 ≤ x) :
    (x+11*s-1)^5 < poly x s ∧ poly x s < (x+11*s)^5 := by
  obtain ⟨w, hw, rfl⟩ := exists_nonneg_add_of_le hs
  obtain ⟨z, hz, rfl⟩ := exists_nonneg_add_of_le hx
  constructor <;> rw [← sub_pos] <;> unfold poly <;> ring_nf <;> positivity

end EleventhGap

#print axioms EleventhGap.symmetric
#print axioms EleventhGap.fifth_gap
