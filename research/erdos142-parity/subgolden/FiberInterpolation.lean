import ExactInterpolation

/-! Exact passage from weighted finite-block inequalities to any rational
grid. Grid interpolation follows @eilamc14 in DoublingGrowth. -/

namespace Erdos142CyclicFiber
open Erdos142GridInterpolation

theorem interpolate_blocks (C L : ℕ) (hL : 0<L)
    (block : ∀ q d : ℕ, d≤L →
      C*((L-d)*rothNumberNat q+d*rothNumberNat (q+1)) ≤ L*rothNumberNat (L*q+d))
    (A x : ℕ) (hA : 0<A) : (C:ℤ)*(interp A x : ℤ) ≤ (interp A (L*x) : ℤ) := by
  let q := x/A
  let r := x%A
  let e := (L*r)/A
  let b := (L*r)%A
  have hr : r<A := Nat.mod_lt _ hA
  have hb : b<A := Nat.mod_lt _ hA
  have he : e<L := (Nat.div_lt_iff_lt_mul hA).mpr (Nat.mul_lt_mul_of_pos_left hr hL)
  have hx : A*q+r=x := Nat.div_add_mod _ _
  have hs : A*e+b=L*r := Nat.div_add_mod _ _
  have split : L*x = A*(L*q+e)+b := by
    calc L*x = L*(A*q+r) := congrArg (L*·) hx.symm
         _ = A*(L*q)+(L*r) := by ring
         _ = _ := by rw [← hs]; ring
  have hq : (L*x)/A=L*q+e := by rw [split,Nat.mul_add_div hA,Nat.div_eq_of_lt hb,Nat.add_zero]
  have hmod : (L*x)%A=b := by rw [split,Nat.mul_add_mod,Nat.mod_eq_of_lt hb]
  have lo := block q e he.le
  have hi := block q (e+1) he
  have lo' : (C:ℤ)*(((L:ℤ)-e)*rothNumberNat q+(e:ℤ)*rothNumberNat (q+1)) ≤
      (L:ℤ)*rothNumberNat (L*q+e) := by
    zify [he.le] at lo
    exact lo
  have hi' : (C:ℤ)*(((L:ℤ)-(e+1))*rothNumberNat q+((e:ℤ)+1)*rothNumberNat (q+1)) ≤
      (L:ℤ)*rothNumberNat (L*q+e+1) := by
    have h : C*((L-(e+1))*rothNumberNat q+(e+1)*rothNumberNat (q+1)) ≤
        L*rothNumberNat (L*q+e+1) := by simpa [Nat.add_assoc] using hi
    zify [show e+1≤L by omega] at h
    exact h
  have h := add_le_add
    (mul_le_mul_of_nonneg_left lo' (show 0≤(A:ℤ)-b by omega))
    (mul_le_mul_of_nonneg_left hi' (show (0:ℤ)≤b by positivity))
  unfold interp
  rw [hq,hmod]
  change (C:ℤ)*(((A-r)*rothNumberNat q+r*rothNumberNat (q+1) : ℕ) : ℤ) ≤ _
  push_cast [Nat.cast_sub hr.le, Nat.cast_sub hb.le]
  apply le_of_mul_le_mul_left (a := (L:ℤ)) _ (by exact_mod_cast hL)
  have eq : (A:ℤ)*e+b=(L:ℤ)*r := by exact_mod_cast hs
  linear_combination h + (C:ℤ)*((rothNumberNat q:ℤ)-rothNumberNat (q+1))*eq

#print axioms interpolate_blocks
end Erdos142CyclicFiber
