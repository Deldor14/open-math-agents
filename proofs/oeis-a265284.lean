import OMAStatements.S_oeis_a265284
import Mathlib

open OMA.S_oeis_a265284

namespace Deldor14.Rule94

def zig : ℕ → List Bool → List Bool
  | 0, tail => tail
  | k+1, tail => false :: true :: zig k tail

def evenRow (k : ℕ) := true :: true :: zig k [false,true,true]
def oddRow (k : ℕ) := true :: true :: true :: zig k [false,true,true,true]

theorem zig_append (k : ℕ) (tail rest : List Bool) :
    zig k tail ++ rest = zig k (tail ++ rest) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zig,List.cons_append,ih]

theorem scan_even (k : ℕ) (b : Bool) :
    scan b true (zig k [false,true,true,false,false]) =
      true :: zig k [false,true,true,true] := by
  induction k generalizing b with
  | zero => cases b <;> rfl
  | succ k ih => cases b <;> simp [zig,scan,rule94,ih]

theorem scan_odd (k : ℕ) (b : Bool) :
    scan b true (zig k [false,true,true,true,false,false]) =
      true :: zig k [false,true,false,true,true] := by
  induction k generalizing b with
  | zero => cases b <;> rfl
  | succ k ih => cases b <;> simp [zig,scan,rule94,ih]

theorem extend_tail (k : ℕ) (tail : List Bool) :
    zig k (false :: true :: tail) = false :: true :: zig k tail := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zig,ih]

theorem even_next (k : ℕ) : next (evenRow k) = oddRow k := by
  simp only [next,evenRow,oddRow,List.cons_append,zig_append]
  change true :: true :: scan true true (zig k [false,true,true,false,false]) = _
  rw [scan_even]

theorem odd_next (k : ℕ) : next (oddRow k) = evenRow (k+2) := by
  simp only [next,oddRow,evenRow,List.cons_append,zig_append]
  change true :: true :: false :: scan true true (zig k [false,true,true,true,false,false]) = _
  rw [scan_odd]
  simp only [extend_tail,zig]

theorem rows (t : ℕ) : row (2*t+2) = evenRow (2*t) ∧ row (2*t+3) = oddRow (2*t) := by
  induction t with
  | zero => constructor <;> rfl
  | succ t ih =>
    have e : row (2*(t+1)+2) = evenRow (2*(t+1)) := by
      rw [show 2*(t+1)+2 = (2*t+3)+1 by omega,row,ih.2,odd_next]
      congr 1 <;> omega
    exact ⟨e,by rw [show 2*(t+1)+3 = (2*(t+1)+2)+1 by omega,row,e,even_next]⟩

theorem count_zig (k : ℕ) (tail : List Bool) : ones (zig k tail) = k + ones tail := by
  induction k with
  | zero => simp [zig]
  | succ k ih => simp [zig,ones,ih,Nat.cast_add]; ring

theorem counts (t : ℕ) :
    ones (row (2*t+2)) = 2*(t:ℤ)+4 ∧ ones (row (2*t+3)) = 2*(t:ℤ)+6 := by
  rw [(rows t).1,(rows t).2]
  constructor <;> simp [evenRow,oddRow,ones,count_zig] <;> ring

theorem totals (t : ℕ) : a (2*t+2) = 2*(t:ℤ)^2+10*t+8 ∧
    a (2*t+3) = 2*(t:ℤ)^2+12*t+14 := by
  induction t with
  | zero => decide
  | succ t ih =>
    have e : a (2*(t+1)+2) = 2*((t+1:ℕ):ℤ)^2+10*(t+1:ℕ)+8 := by
      calc a (2*(t+1)+2) = a (2*t+3) + ones (row (2*(t+1)+2)) := by
              rw [show 2*(t+1)+2=(2*t+3)+1 by omega,a]
           _ = _ := by rw [ih.2,(counts (t+1)).1]; push_cast; ring
    refine ⟨e,?_⟩
    rw [show 2*(t+1)+3=(2*(t+1)+2)+1 by omega,a,e]
    have h := (counts (t+1)).2
    rw [show 2*(t+1)+3=(2*(t+1)+2)+1 by omega] at h
    rw [h]; push_cast; ring

theorem all_closed (n : ℕ) (pos : 0 < n) :
    4*a n = 2*(n:ℤ)^2+12*n-(-1)^n+1 := by
  by_cases one : n=1
  · subst n; decide
  let t := (n-2)/2
  rcases (show n=2*t+2 ∨ n=2*t+3 by dsimp [t]; omega) with h | h
  · rw [h,(totals t).1,pow_add,pow_mul]; push_cast; norm_num; ring
  · rw [h,(totals t).2,pow_add,pow_mul]; push_cast; norm_num; ring

theorem rec_five (n : ℕ) : a (n+5) = 2*a (n+4)-2*a (n+2)+a (n+1) := by
  have h5 := all_closed (n+5) (by omega)
  have h4 := all_closed (n+4) (by omega)
  have h2 := all_closed (n+2) (by omega)
  have h1 := all_closed (n+1) (by omega)
  push_cast at *
  simp only [pow_add] at *
  norm_num at *
  linarith

end Deldor14.Rule94

open Deldor14.Rule94

theorem OMA.solution : type_of% @OMA.S_oeis_a265284.main := by
  refine ⟨all_closed,?_,?_,?_,?_⟩
  · rintro n hn even
    have h := all_closed n (by omega)
    rw [even.neg_one_pow] at h
    omega
  · intro n odd
    have h := all_closed n (by obtain ⟨k,hk⟩ := odd; omega)
    rw [odd.neg_one_pow] at h
    omega
  · intro n hn
    obtain ⟨t,rfl⟩ : ∃ t, n=t+5 := ⟨n-5,by omega⟩
    simpa using rec_five t
  · intro n
    by_cases small : n ≤ 4
    · interval_cases n <;> decide
    · obtain ⟨t,rfl⟩ : ∃ t, n=t+5 := ⟨n-5,by omega⟩
      change a (t+5)-2*a (t+4)+2*a (t+2)-a (t+1)=0
      linarith [rec_five t]
