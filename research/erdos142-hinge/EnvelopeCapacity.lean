import Mathlib

noncomputable section
namespace Erdos142Envelope

def pos (x : ℝ) := max 0 x
def leftCost (b c d : ℝ) :=
  max 0 (max ((b+d-1)/2) (b+d-1-c))
def rightCost (b c d : ℝ) :=
  max 0 (max (b-(1+c)/2) (max (d-(1+c)/2) (b+d-1-c)))
def leastCost (b c d : ℝ) :=
  min (d-c) (min (pos (b-c)) (min (leftCost b c d) (rightCost b c d)))
def overlap (b c d s : ℝ) := pos (min b (min (d-c) (min (s-c) (b+d-s))))

private lemma nonneg_pos (x : ℝ) : 0 ≤ pos x := le_max_left _ _
private lemma alt_pair (x y : ℝ) : x ≤ pos (min x y) ∨ y ≤ pos (min x y) := by
  apply min_le_iff.mp
  exact le_max_right _ _

theorem reflected_mass (b c d v s : ℝ)
    (hb' : b ≤ 1) (hc : 0 ≤ c)
    (hv : (0 ≤ v ∧ v ≤ 1 ∧ s = v+1) ∨ (1 ≤ v ∧ v ≤ 2 ∧ s = v-1)) :
    2*leastCost b c d ≤
      pos (min v (2*b-v)) + pos (min (v-2*c) (2*d-v)) + 2*overlap b c d s := by
  let x := pos (min v (2*b-v))
  let y := pos (min (v-2*c) (2*d-v))
  let z := overlap b c d s
  let t := (x+y+2*z)/2
  have hx : 0 ≤ x := nonneg_pos _
  have hy : 0 ≤ y := nonneg_pos _
  have hz : 0 ≤ z := nonneg_pos _
  have ht : 2*t=x+y+2*z := by dsimp only [t]; ring
  have htn : 0 ≤ t := by linarith
  change 2*leastCost b c d ≤ x+y+2*z
  by_contra! bad
  have low : t < leastCost b c d := by linarith
  obtain ⟨hdc, hdif0, hleft0, hright0⟩ := (show t < d-c ∧ t < pos (b-c) ∧
      t < leftCost b c d ∧ t < rightCost b c d by
    simpa only [leastCost,lt_min_iff] using low)
  have hdif : t < b-c := (lt_max_iff.mp hdif0).resolve_left (not_lt_of_ge htn)
  have hleft : t < (b+d-1)/2 ∨ t < b+d-1-c := by
    simpa only [leftCost, lt_max_iff, not_lt_of_ge htn, false_or] using hleft0
  have hright : t < b-(1+c)/2 ∨ t < d-(1+c)/2 ∨ t < b+d-1-c := by
    simpa only [rightCost, lt_max_iff, not_lt_of_ge htn, false_or] using hright0
  have hcross0 : min b (min (d-c) (min (s-c) (b+d-s))) ≤ z := le_max_right _ _
  have hcross : s-c ≤ z ∨ b+d-s ≤ z := by
    simp only [min_le_iff] at hcross0
    rcases hcross0 with h | h | h | h
    · exfalso; linarith
    · exfalso; linarith
    · exact Or.inl h
    · exact Or.inr h
  have ha : v ≤ x ∨ 2*b-v ≤ x := alt_pair _ _
  have hh : v-2*c ≤ y ∨ 2*d-v ≤ y := alt_pair _ _
  rcases hv with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ <;>
    rcases ha with ha | ha <;> rcases hh with hh | hh <;> rcases hcross with hk | hk <;>
    rcases hleft with hl | hl <;> rcases hright with hr | hr | hr <;>
    linarith only [hb',hc,h1,h2,h3,hx,hy,hz,ht,htn,hdc,hdif,ha,hh,hk,hl,hr]
theorem early_capacity (b c d s : ℝ) (hs : 2*s = b+d-1) (hs0 : 0 ≤ s)
    (hsc : s ≤ c) (hgap : s ≤ b-c) (hb : b ≤ d-c) :
    leastCost b c d = s := by
  have hl : leftCost b c d = s := by
    unfold leftCost
    have hm : (b + d - 1) / 2 = s := by linarith
    have hn : b + d - 1 - c ≤ s := by linarith
    rw [hm, max_eq_left hn, max_eq_right hs0]
  have hr : s ≤ rightCost b c d := by
    calc
      s ≤ d-(1+c)/2 := by linarith
      _ ≤ max (d-(1+c)/2) (b+d-1-c) := le_max_left _ _
      _ ≤ max (b-(1+c)/2) _ := le_max_right _ _
      _ ≤ max 0 _ := le_max_right _ _
  have hdc : s ≤ d-c := by linarith
  have hp : s ≤ pos (b-c) := hgap.trans (le_max_right _ _)
  simp only [leastCost, hl, min_eq_left hr, min_eq_right hp, min_eq_right hdc]

#print axioms reflected_mass
#print axioms early_capacity
end Erdos142Envelope
