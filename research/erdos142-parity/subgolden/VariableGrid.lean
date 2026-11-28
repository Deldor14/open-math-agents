import FastPropagation

/-! A finite chain of arbitrary grid steps and a cover by right endpoints.
The list of charged indices may repeat an endpoint. -/

namespace Erdos142VariableGrid

structure Row where
  a : ℕ
  b : ℕ
  deriving DecidableEq

structure Stage where
  h : ℕ
  m : ℕ
  deriving DecidableEq

def Row.step (r : Row) (q : Stage) : Row := ⟨r.a+r.b,r.a+2*r.b+q.h⟩

def Row.valid (r : Row) (q : Stage) : Prop :=
  0 < q.h ∧ q.h ∣ r.a ∧ q.h ∣ r.b ∧
    (r.b/q.h ≤ r.a/q.h ∨ Erdos142Fast.walk (r.a/q.h) (r.b/q.h) q.m = r.b/q.h)

instance (r : Row) (q : Stage) : Decidable (r.valid q) := by unfold Row.valid; infer_instance

def Certified (r : ℕ → Row) (q : ℕ → Stage) (s : ℕ) : Prop :=
  ∀ i < s, r (i+1) = (r i).step (q i) ∧ (r i).valid (q i)

/-- An equivalent finite statement suitable for evaluating concrete tables. -/
theorem certified_iff (r : ℕ → Row) (q : ℕ → Stage) (s : ℕ) :
    Certified r q s ↔ ∀ i : Fin s, r (i.val+1) = (r i.val).step (q i.val) ∧ (r i.val).valid (q i.val) :=
  ⟨fun H i => H _ i.isLt, fun H i hi => H ⟨i,hi⟩⟩

def gap (P : ℕ → ℤ) (r : Row) := P r.b-P r.a

/-- The use of max allows a certified row to have m=0. -/
def multiplier (q : ℕ → Stage) : ℕ → ℕ
  | 0 => 1
  | n+1 => multiplier q n * max 1 (q n).m

theorem one_le_multiplier (q : ℕ → Stage) (s : ℕ) : 1 ≤ multiplier q s := by
  induction s with
  | zero => exact Nat.le_refl 1
  | succ s ih => exact Nat.mul_pos ih (Nat.le_max_left _ _)

variable (P : ℕ → ℤ) (mono : Monotone P) (sub : ∀ x y, P (x+y) ≤ P x+P y)
    (glue : ∀ x y, y ≤ x → P x+P y ≤ P (2*x+y))

include mono sub glue in
theorem scaled_chain (r : Row) (q : Stage) (ok : r.valid q) :
    gap P r ≤ (q.m:ℤ)*gap P (r.step q) := by
  obtain ⟨_,ha,hb,ends⟩ := ok
  have a := Nat.mul_div_cancel' ha
  have b := Nat.mul_div_cancel' hb
  let F (n : ℕ) := P (q.h*n)
  have mF : Monotone F := fun _ _ h => mono (Nat.mul_le_mul_left _ h)
  have sF (x y : ℕ) : F (x+y) ≤ F x+F y := by simpa [F,Nat.mul_add] using sub (q.h*x) (q.h*y)
  have gF (x y : ℕ) (yx : y ≤ x) : F x+F y ≤ F (2*x+y) := by
    simpa only [F,Nat.mul_add,show q.h*(2*x)=2*(q.h*x) by ring] using
      glue (q.h*x) (q.h*y) (Nat.mul_le_mul_left _ yx)
  have h := Erdos142Fast.chain F mF sF gF (r.a/q.h) (r.b/q.h) q.m ends
  simpa only [F,Nat.mul_add,Nat.mul_one,
    show q.h*(2*(r.b/q.h))=2*(q.h*(r.b/q.h)) by ring,a,b,gap,Row.step] using h

include mono sub glue in
theorem uniform_gap (r : ℕ → Row) (q : ℕ → Stage) (s : ℕ)
    (cert : Certified r q s) (i : ℕ) (hi : i ≤ s) :
    gap P (r i) ≤ (multiplier q s:ℤ)*gap P (r s) := by
  induction s with
  | zero =>
    have e : i=0 := by omega
    simp [e,multiplier]
  | succ s ih =>
    have step := cert s (by omega)
    have last : 0 ≤ gap P (r (s+1)) := by
      rw [step.1]
      exact sub_nonneg.mpr (mono (by unfold Row.step; dsimp; omega))
    rcases hi.eq_or_lt with e | smaller
    · subst i
      simpa using mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ multiplier q (s+1) by
        exact_mod_cast one_le_multiplier q (s+1)) last
    · have earlier := ih (fun k hk => cert k (by omega)) (by omega)
      have stepBound := scaled_chain P mono sub glue (r s) (q s) step.2
      rw [←step.1] at stepBound
      have larger := mul_le_mul_of_nonneg_right
        (show ((q s).m:ℤ) ≤ (max 1 (q s).m:ℕ) by exact_mod_cast Nat.le_max_right 1 (q s).m) last
      have all := earlier.trans (mul_le_mul_of_nonneg_left (stepBound.trans larger)
        (Int.natCast_nonneg (multiplier q s)))
      simpa [multiplier,mul_assoc] using all

include sub in
/-- Adding B to the left endpoint value eliminates the loss at each doubling.
This gives the coefficient B, also when the index is zero. -/
theorem right_from_uniform (r : ℕ → Row) (s : ℕ) (B : ℤ)
    (advance : ∀ i < s, (r (i+1)).a = (r i).a+(r i).b)
    (bound : ∀ i ≤ s, gap P (r i) ≤ B) (i : ℕ) (hi : i ≤ s) :
    P (r i).b ≤ (2:ℤ)^i*(P (r 0).a+B) := by
  have left (n : ℕ) (hn : n ≤ s) : P (r n).a+B ≤ (2:ℤ)^n*(P (r 0).a+B) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have prev := ih (by omega)
      have g := bound n (by omega)
      unfold gap at g
      have split := sub (r n).a (r n).b
      rw [advance n (by omega),pow_succ]
      linarith only [prev,g,split]
  have g := bound i hi
  unfold gap at g
  linarith only [g,left i hi]

def cost (indices : List ℕ) : ℕ := (indices.map (fun i => 2^i)).sum
def room (r : ℕ → Row) (indices : List ℕ) : ℕ := (indices.map (fun i => (r i).b)).sum

include sub glue in
theorem cost_bound (r : ℕ → Row) (indices : List ℕ) (H : ℤ)
    (charged : ∀ i ∈ indices, P (r i).b ≤ (2:ℤ)^i*H) :
    P (room r indices) ≤ (cost indices:ℤ)*H := by
  induction indices with
  | nil =>
    have z := glue 0 0 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at z
    simpa [room,cost] using (show P 0 ≤ 0 by omega)
  | cons i tail ih =>
    have head := charged i (by simp)
    have rest := ih (fun j h => charged j (List.mem_cons_of_mem i h))
    have both := (sub (r i).b (room r tail)).trans (add_le_add head rest)
    simpa only [room,cost,List.map_cons,List.sum_cons,Nat.cast_add,Nat.cast_pow,
      Nat.cast_ofNat,add_mul] using both

include mono sub glue in
theorem cover_bound (r : ℕ → Row) (q : ℕ → Stage) (s : ℕ)
    (cert : Certified r q s)
    (indices : List ℕ) (active : ∀ i ∈ indices, i ≤ s) {target : ℕ}
    (fit : target ≤ room r indices) :
    P target ≤ (cost indices:ℤ)*(P (r 0).a + (multiplier q s:ℤ)*gap P (r s)) := by
  apply (mono fit).trans
  apply cost_bound P sub glue
  intro i hi
  exact right_from_uniform P sub r s _
    (fun j hj => congrArg Row.a (cert j hj).1)
    (uniform_gap P mono sub glue r q s cert) i (active i hi)

include mono sub glue in
/-- A seed covered by the selected right endpoints bounds the initial value
by the terminal gap whenever the seed coefficient exceeds the cover cost. -/
theorem charged_seed (r : ℕ → Row) (q : ℕ → Stage) (s : ℕ) (cert : Certified r q s)
    (indices : List ℕ) (active : ∀ i ∈ indices, i ≤ s) {target C : ℕ}
    (fit : target ≤ room r indices) (seed : (C:ℤ)*P (r 0).a ≤ P target) :
    ((C:ℤ)-(cost indices:ℤ))*P (r 0).a ≤
      (cost indices:ℤ)*(multiplier q s:ℤ)*gap P (r s) := by
  have bound := seed.trans (cover_bound P mono sub glue r q s cert indices active fit)
  linarith only [bound]

#print axioms charged_seed
#print axioms scaled_chain
#print axioms uniform_gap
#print axioms right_from_uniform
#print axioms cost_bound
#print axioms cover_bound
end Erdos142VariableGrid
