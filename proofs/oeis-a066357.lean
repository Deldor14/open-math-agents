import OMAStatements.S_oeis_a066357
import Mathlib

namespace Deldor14.CatalanValuation
open OMA.S_oeis_a066357

private def oddPart : ℕ → ℕ
  | 0 => 1
  | n+1 => (2*n+1)*oddPart n
private theorem oddProd (n : ℕ) : Odd (oddPart n) := by
  induction n with
  | zero => decide
  | succ n ih => exact (show Odd (2*n+1) from ⟨n,rfl⟩).mul ih

private theorem split (n : ℕ) : (2*n).factorial = 2^n*n.factorial*oddPart n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by omega,Nat.factorial_succ (2*n+1),Nat.factorial_succ (2*n),
      Nat.factorial_succ n,ih,pow_succ,oddPart]
    ring

private theorem centralFact (n : ℕ) : n.centralBinom*n.factorial^2=(2*n).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (n:=2*n) (k:=n) (by omega)
  rwa [show 2*n-n=n by omega, mul_assoc,← pow_two] at h

private theorem doubling (n : ℕ) :
    (2*n).centralBinom*(oddPart n)^2=n.centralBinom*oddPart (2*n) := by
  apply Nat.eq_of_mul_eq_mul_right (show 0<2^(2*n)*n.factorial^2 by positivity)
  calc
    _ = (2*n).centralBinom*(2^n*n.factorial*oddPart n)^2 := by
      rw [show 2*n=n*2 by omega,pow_mul]; ring
    _ = (2*(2*n)).factorial := by rw [← split,centralFact]
    _ = 2^(2*n)*(n.centralBinom*n.factorial^2)*oddPart (2*n) := by rw [centralFact,split (2*n)]
    _ = _ := by ring

private theorem pos (n : ℕ) : 0<catalan n := by
  have h := Nat.centralBinom_pos n
  rw [← succ_mul_catalan_eq_centralBinom] at h
  exact Nat.pos_of_mul_pos_left h

private theorem recC (n : ℕ) : ((n:ℤ)+2)*catalan (n+1)=2*(2*n+1)*(catalan n:ℤ) := by
  have h := congrArg (fun z : ℕ => (z:ℤ)) (Nat.succ_mul_centralBinom_succ n)
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  push_cast at h
  apply mul_left_cancel₀ (show (n:ℤ)+1≠0 by positivity)
  linear_combination h

private def leftOdd (n : ℕ) : ℤ := (oddPart n:ℤ)^2*(2*n+1)
private def rightOdd (n : ℕ) : ℤ := oddPart (2*n)
private theorem evenRow (n : ℕ) :
    leftOdd n*catalan (2*n)=((n:ℤ)+1)*rightOdd n*catalan n := by
  have h := doubling n
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  have ei := congrArg (fun z : ℕ => (z:ℤ)) h
  push_cast at ei
  unfold leftOdd rightOdd
  linear_combination ei
private theorem oddRow (n : ℕ) :
    leftOdd n*catalan (2*n+1)=(4*(n:ℤ)+1)*rightOdd n*catalan n := by
  have h := recC (2*n)
  push_cast at h
  apply mul_left_cancel₀ (show 2*((n:ℤ)+1)≠0 by positivity)
  linear_combination leftOdd n*h + 2*(4*(n:ℤ)+1)*evenRow n

private theorem vp (x : ℤ) (hx : Odd x) : x.natAbs.factorization 2=0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro h
  obtain ⟨k,hk⟩ := hx.natAbs
  omega

theorem result : type_of% @OMA.S_oeis_a066357.main := by
  intro n
  let z := (4*(n:ℤ)+1)*rightOdd n+2*((n:ℤ)+1)*rightOdd n-(2:ℤ)^(2*n+1)*leftOdd n
  have hl : Odd (leftOdd n) := by
    have ho : Odd (oddPart n:ℤ) := by exact_mod_cast oddProd n
    exact ho.pow.mul (show Odd (2*(n:ℤ)+1) from ⟨n,rfl⟩)
  have hr : Odd (rightOdd n) := by unfold rightOdd; exact_mod_cast oddProd (2*n)
  have hz : Odd z := by
    obtain ⟨k,hk⟩ := hr
    dsimp [z]
    rw [hk,pow_succ]
    exact ⟨2*(n:ℤ)*(2*k+1)+k+((n:ℤ)+1)*(2*k+1)-2^(2*n)*leftOdd n,by ring⟩
  have eq : leftOdd n*a n=z*(catalan n:ℤ) := by
    unfold a z
    linear_combination oddRow n + 2*evenRow n
  have hnz : (catalan n:ℤ)≠0 := by exact_mod_cast (pos n).ne'
  have nzOdd (w : ℤ) (hw : Odd w) : w≠0 := by obtain ⟨k,h⟩ := hw; omega
  have anz : a n≠0 := by
    intro h
    rw [h,mul_zero] at eq
    exact (mul_ne_zero (nzOdd _ hz) hnz) eq.symm
  have v := congrArg (fun t : ℤ => t.natAbs.factorization 2) eq
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at v
  rw [Nat.factorization_mul (Int.natAbs_ne_zero.mpr (nzOdd _ hl)) (Int.natAbs_ne_zero.mpr anz),
      Nat.factorization_mul (Int.natAbs_ne_zero.mpr (nzOdd _ hz)) (pos n).ne'] at v
  simpa only [Finsupp.add_apply,vp _ hl,vp _ hz,zero_add] using And.intro anz v

end Deldor14.CatalanValuation
theorem OMA.solution : type_of% @OMA.S_oeis_a066357.main := Deldor14.CatalanValuation.result
