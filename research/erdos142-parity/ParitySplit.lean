import Lean

namespace ProgressionParity

/-- Every point in a run of the given length belongs to the predicate. -/
def Run (P : Nat → Prop) (a d : Nat) : Nat → Prop
  | 0 => True
  | m + 1 => P a ∧ Run P (a+d) d m

def Free (P : Nat → Prop) (length : Nat) : Prop :=
  ∀ a d, 0 < d → ¬ Run P a d length

def Part (P : Nat → Prop) (bit : Nat) : Nat → Prop :=
  fun i => P (2*i+bit)

theorem interleave (P : Nat → Prop) (a d m : Nat) :
    Run P a d (2*m) ↔ Run P a (2*d) m ∧ Run P (a+d) (2*d) m := by
  induction m generalizing a with
  | zero => simp [Run]
  | succ m ih =>
    rw [show 2*(m+1) = (2*m+1)+1 by omega]
    change (P a ∧ P (a+d) ∧ Run P (a+d+d) d (2*m)) ↔
      (P a ∧ Run P (a+2*d) (2*d) m) ∧
      (P (a+d) ∧ Run P (a+d+2*d) (2*d) m)
    rw [ih]
    have e₁ : a+d+d = a+2*d := by omega
    have e₂ : a+d+d+d = a+d+2*d := by omega
    rw [e₂, e₁]
    exact ⟨fun ⟨x,y,u,v⟩ => ⟨⟨x,u⟩,⟨y,v⟩⟩, fun ⟨⟨x,u⟩,⟨y,v⟩⟩ => ⟨x,y,u,v⟩⟩

theorem scale (P : Nat → Prop) (b a d m : Nat) :
    Run (Part P b) a d m ↔ Run P (2*a+b) (2*d) m := by
  induction m generalizing a with
  | zero => simp [Run]
  | succ m ih =>
    change (P (2*a+b) ∧ Run (Part P b) (a+d) d m) ↔
      (P (2*a+b) ∧ Run P (2*a+b+2*d) (2*d) m)
    rw [ih, show 2*(a+d)+b = 2*a+b+2*d by omega]

theorem evenStart (P : Nat → Prop) (a t m : Nat) :
    Run P (2*a) (2*t+1) (2*m) ↔
    Run (Part P 0) a (2*t+1) m ∧ Run (Part P 1) (a+t) (2*t+1) m := by
  rw [interleave, scale, scale]
  simp only [Nat.add_zero, show 2*(a+t)+1 = 2*a+(2*t+1) by omega]

theorem oddStart (P : Nat → Prop) (a t m : Nat) :
    Run P (2*a+1) (2*t+1) (2*m) ↔
    Run (Part P 1) a (2*t+1) m ∧ Run (Part P 0) (a+t+1) (2*t+1) m := by
  rw [interleave, scale, scale]
  simp only [Nat.add_zero, show 2*(a+t+1) = 2*a+1+(2*t+1) by omega]

private theorem parity (x : Nat) : (∃ j, x=2*j) ∨ (∃ j, x=2*j+1) := by
  by_cases h : x%2=0
  · exact Or.inl ⟨x/2, by omega⟩
  · exact Or.inr ⟨x/2, by omega⟩

/-- Exact parity reduction for every even forbidden length, including length six. -/
theorem free_iff (P : Nat → Prop) (m : Nat) :
    Free P (2*m) ↔
    Free (Part P 0) (2*m) ∧ Free (Part P 1) (2*m) ∧
    (∀ a t, ¬ (Run (Part P 0) a (2*t+1) m ∧ Run (Part P 1) (a+t) (2*t+1) m)) ∧
    (∀ a t, ¬ (Run (Part P 1) a (2*t+1) m ∧ Run (Part P 0) (a+t+1) (2*t+1) m)) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a d hd hr
      exact h (2*a+0) (2*d) (by omega) ((scale P 0 a d (2*m)).mp hr)
    · intro a d hd hr
      exact h (2*a+1) (2*d) (by omega) ((scale P 1 a d (2*m)).mp hr)
    · intro a t hr
      exact h (2*a) (2*t+1) (by omega) ((evenStart P a t m).mpr hr)
    · intro a t hr
      exact h (2*a+1) (2*t+1) (by omega) ((oddStart P a t m).mpr hr)
  · rintro ⟨he,ho,h₀,h₁⟩ a d hd hr
    rcases parity d with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rcases parity a with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact he i t (by omega) ((scale P 0 i t (2*m)).mpr hr)
      · exact ho i t (by omega) ((scale P 1 i t (2*m)).mpr hr)
    · rcases parity a with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · exact h₀ i t ((evenStart P i t m).mp hr)
      · exact h₁ i t ((oddStart P i t m).mp hr)

#print axioms free_iff

end ProgressionParity
