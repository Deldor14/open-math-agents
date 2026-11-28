import Mathlib.NumberTheory.Chebyshev
import RothInducedWindow
import RothInducedTradeoff

open Finset
namespace Erdos142InducedTriples
open Erdos142ExactDefects

private theorem accumulate (M : ℕ → ℕ) (L : ℕ) (hL : 0<L)
    (step : ∀ j<L, 20*L*(2*M j) ≤ 20*L*M (j+1)+2^(j+1)*M 0) :
    19*(2^L*M 0) ≤ 20*M L := by
  have sum (j : ℕ) (hj : j≤L) :
      20*L*(2^j*M 0) ≤ 20*L*M j+j*(2^j*M 0) := by
    induction j with
    | zero => simp
    | succ j ih =>
      have p := ih (by omega)
      have q := step j (by omega)
      rw [pow_succ] at q ⊢
      nlinarith only [p,q]
  have all := sum L le_rfl
  have h : L*(19*(2^L*M 0)) ≤ L*(20*M L) := by nlinarith only [all]
  exact Nat.le_of_mul_le_mul_left h hL

/-- Finite certificate for a whole run of dyadic scales. When size deficits,
    covers and boundary terms have small total cost at every scale, the final
    shift must be a multiple of every positive integer through 2^k. -/
theorem run_divisibility (N k : ℕ) (positive : 0<rothNumberNat N)
    (A C D : ℕ → Finset ℕ) (t : ℕ → ℕ) (ht : ∀ j, 0<t j)
    (fit : ∀ j, A j ⊆ range (2^j*N))
    (free : ∀ j, ThreeAPFree (↑(A j) : Set ℕ))
    (hc : ∀ j, Covers (A j) (C j) (t j)) (hd : ∀ j, Covers (A j) (D j) (2*t j))
    (cost : ∀ j≤k+3, 80*(k+3)*(rothNumberNat (2^j*N)-(A j).card+
      (C j).card+(D j).card+rothNumberNat (2*t j)) ≤ rothNumberNat (2^j*N))
    (last : t (k+3)≤2^k*N) : ∀ b : ℕ, 0<b → b≤2^k → b ∣ t (k+3) := by
  let L := k+3
  let M (j : ℕ) := rothNumberNat (2^j*N)
  let d (j : ℕ) := M j-(A j).card+(C j).card+(D j).card+rothNumberNat (2*t j)
  have Lpos : 0<L := by dsimp [L]; omega
  have start : M 0=rothNumberNat N := by simp [M]
  have two (j : ℕ) : 2^(j+1)*N=2^j*N+2^j*N := by rw [pow_succ]; ring
  have upper (j : ℕ) : M j ≤ 2^j * M 0 := by
    induction j with
    | zero => simp
    | succ j ih =>
      have u : M (j+1) ≤ M j+M j := by dsimp [M]; rw [two]; apply rothNumberNat_add_le
      rw [pow_succ]
      nlinarith only [u,ih]
  choose p first _ _ four mods using fun j =>
    cover_tradeoff (A j) (C j) (D j) (2^j*N) (t j) (ht j) (fit j) (free j) (hc j) (hd j)
  have bounds (j : ℕ) : M j≤2*p j+4*d j ∧ 2*M j≤M (j+1)+8*d j := by
    have a := first j
    have b := four j
    have c := rothNumberNat_add_le (2^j*N) (t j)
    have e := rothNumberNat_add_le (2^(j+1)*N) (2*t j)
    rw [two] at e
    have u := rothNumberNat.monotone (show t j≤2*t j by omega)
    have h : 2*(2^j*N)=2^j*N+2^j*N := by omega
    rw [h] at b
    dsimp [d,M] at *
    rw [two]
    omega
  have terminal := accumulate M L Lpos (fun j hj => by
    have c : 80*L*d j≤M j := cost j (by dsimp [L] at *; omega)
    have mul := Nat.mul_le_mul_left (20*L) (bounds j).2
    have u := upper j
    rw [pow_succ]
    nlinarith only [c,mul,u])
  have cL : 80*L*d L≤M L := cost L le_rfl
  have c1 : 80*d L≤M L := by
    have mon := Nat.mul_le_mul_right (80*d L) (show 1≤L by omega)
    nlinarith only [mon,cL]
  have pL := (bounds L).1
  have powL : 2^L=8*2^k := by simp [L,pow_add,Nat.mul_comm]
  rw [powL,start] at terminal
  have pos : 0<2^k*rothNumberNat N := Nat.mul_pos (pow_pos (by decide) _) positive
  have scale : 2^L*N+t L≤(9*2^k)*N := by
    rw [powL]
    nlinarith only [last]
  apply sieve_from_bound (mods L) scale
  nlinarith only [terminal,c1,pL,pos]

/-- An exact finite window with one scale good simultaneously for all sets
    and all positive steps up to the specified (possibly varying) bound. -/
theorem exists_good_scale (N k : ℕ) (H : ℕ → ℕ) (positive : 0<rothNumberNat N)
    (boundary : H (k+3)≤2^k*N) (gap : (2^k+1)*H (k+3)<2^(2^k)) :
    ∃ j≤k+3, ∀ (A C D : Finset ℕ) (t : ℕ), 0<t → t≤H j → A ⊆ range (2^j*N) →
      ThreeAPFree (↑A : Set ℕ) → Covers A C t → Covers A D (2*t) →
      rothNumberNat (2^j*N) <
        80*(k+3)*(rothNumberNat (2^j*N)-A.card+C.card+D.card+rothNumberNat (2*t)) := by
  classical
  by_contra! failed
  let M (j : ℕ) := rothNumberNat (2^j*N)
  have data (j : ℕ) : ∃ (A C D : Finset ℕ) (t : ℕ),
      0<t ∧ A ⊆ range (2^j*N) ∧ ThreeAPFree (↑A : Set ℕ) ∧ Covers A C t ∧ Covers A D (2*t) ∧
      (j≤k+3 → t≤H j ∧ 80*(k+3)*(M j-A.card+C.card+D.card+rothNumberNat (2*t))≤M j) := by
    by_cases h : j≤k+3
    · obtain ⟨A,C,D,t,ht,bd,fit,fr,hc,hd,sz⟩ := failed j h
      exact ⟨A,C,D,t,ht,fit,fr,hc,hd,fun _ => ⟨bd,sz⟩⟩
    · exact ⟨∅,∅,∅,1,by decide,empty_subset _,by simp,by simp [Covers],by simp [Covers],
        fun e => False.elim (h e)⟩
  choose A C D t ht fit fr hc hd cost using data
  have term := (cost (k+3) le_rfl).1
  have ds := run_divisibility N k positive A C D t ht fit fr hc hd (fun j hj => (cost j hj).2)
    (term.trans boundary)
  have divides : Nat.lcmUpto (2^k) ∣ t (k+3) := Finset.lcm_dvd (fun i hi =>
    ds i (mem_Icc.mp hi).1 (mem_Icc.mp hi).2)
  have lim := Nat.le_of_dvd (ht _) divides
  have prod := Nat.mul_le_mul_left (2^k+1) (lim.trans term)
  exact (Chebyshev.two_pow_le_mul_lcmUpto (2^k)).not_gt (prod.trans_lt gap)

#print axioms run_divisibility
#print axioms exists_good_scale
end Erdos142InducedTriples
