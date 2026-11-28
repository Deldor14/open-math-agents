import SubgoldenPropagation

/-! Check a finite list of greedy chain lengths without expanding the extremal function. -/
namespace Erdos142Fast

def next (a b x : ℕ) : ℕ := min b (min (2*x+1-a) ((b+1+x)/2))

def walk (a b : ℕ) : ℕ → ℕ
  | 0 => a
  | t+1 => next a b (walk a b t)

structure Row where
  a : ℕ
  b : ℕ
  q : ℕ
  e : ℕ
  deriving DecidableEq

def Row.step (r : Row) (m : ℕ) : Row := ⟨r.a+r.b, r.a+2*r.b+1, 2*r.q, (2*r.e+1)*m⟩

def Row.ok (r : Row) (m : ℕ) : Bool := decide (r.b ≤ r.a) || (walk r.a r.b m == r.b)

def accepts (r : Row) : List ℕ → Bool
  | [] => true
  | m :: ms => r.ok m && accepts (r.step m) ms

def finish (r : Row) : List ℕ → Row
  | [] => r
  | m :: ms => finish (r.step m) ms

variable (F : ℕ → ℤ) (mono : Monotone F)
    (sub : ∀ x y, F (x+y) ≤ F x + F y)
    (glue : ∀ x y, y ≤ x → F x + F y ≤ F (2*x+y))

include mono sub glue

theorem chain (a b m : ℕ) (ends : b ≤ a ∨ walk a b m = b) :
    F b - F a ≤ (m:ℤ)*(F (a+2*b+1)-F (a+b)) := by
  let D := F (a+2*b+1)-F (a+b)
  have Dpos : 0 ≤ D := sub_nonneg.mpr (mono (by omega))
  by_cases ba : b ≤ a
  · exact (sub_nonpos.mpr (mono ba)).trans (mul_nonneg (Int.natCast_nonneg _) Dpos)
  have bounds (i : ℕ) : a ≤ walk a b i ∧ walk a b i ≤ b := by
    induction i with
    | zero => simp [walk]; omega
    | succ i ih => change a ≤ next a b (walk a b i) ∧ next a b (walk a b i) ≤ b; unfold next; omega
  have accum (i : ℕ) : F (walk a b i)-F a ≤ (i:ℤ)*D := by
    induction i with
    | zero => simp [walk]
    | succ i ih =>
      let x := walk a b i
      let y := next a b x
      have hx : a ≤ x ∧ x ≤ b := bounds i
      have hy : y ≤ b ∧ y ≤ 2*x+1-a ∧ y ≤ (b+1+x)/2 := by dsimp [y,next]; omega
      have fit : y+(a+b-x)+max y (a+b-x) ≤ a+2*b+1 := by omega
      have h := Erdos142ScaleSteps.one_step F mono sub glue (a+b) (a+2*b+1) x y (by omega) fit
      change F y-F a ≤ ((i+1:ℕ):ℤ)*D
      change F x-F a ≤ (i:ℤ)*D at ih
      change F y-F x ≤ D at h
      push_cast; linarith
  simpa only [ends.resolve_left ba] using accum m

def Bound (F : ℕ → ℤ) (x : ℕ) (r : Row) : Prop :=
  F r.a ≤ (r.q:ℤ)*F x+(r.e:ℤ)*(F r.b-F r.a)

theorem step (x : ℕ) (r : Row) (m : ℕ) (prev : Bound F x r) (ok : r.ok m = true) :
    Bound F x (r.step m) := by
  have hh : r.b ≤ r.a ∨ walk r.a r.b m = r.b := by simpa [Row.ok] using ok
  have h := chain F mono sub glue r.a r.b m hh
  have W := mul_le_mul_of_nonneg_left h (show (0:ℤ) ≤ 2*(r.e:ℤ)+1 by positivity)
  have S := sub r.a r.b
  unfold Bound at *; simp only [Row.step, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  nlinarith only [W,S,prev]

theorem run (x : ℕ) (r : Row) (ms : List ℕ) (h : Bound F x r) (ok : accepts r ms = true) :
    Bound F x (finish r ms) := by
  induction ms generalizing r with
  | nil => exact h
  | cons m ms ih =>
    have hh : r.ok m = true ∧ accepts (r.step m) ms = true := by simpa only [accepts,Bool.and_eq_true] using ok
    exact ih (r.step m) (step F mono sub glue x r m h hh.1) hh.2

#print axioms run
end Erdos142Fast
