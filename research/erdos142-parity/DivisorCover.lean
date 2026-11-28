import FirstGap
import Mathlib.Algebra.GCDMonoid.Finset

namespace ProgressionParity
open scoped BigOperators

private lemma progression_through {k N d x:ℕ} (hk : 0<k) (hd : 0<d)
    (room : k*d≤N) (hx : x∈Finset.Icc 1 N) :
    ∃ a t : ℕ, 1≤a ∧ t<k ∧ a+t*d=x ∧ a+(k-1)*d≤N := by
  obtain ⟨xp,xn⟩ := Finset.mem_Icc.mp hx
  let i := (x-1)/d
  let r := (x-1)%d
  have rl : r<d := Nat.mod_lt _ hd
  have sum : r+i*d=x-1 := by simpa only [r,i,Nat.mul_comm d _] using Nat.mod_add_div (x-1) d
  by_cases big : k-1 ≤ i
  · have le := Nat.mul_le_mul_right d big
    refine ⟨x-(k-1)*d,k-1,by omega,by omega,by omega,by omega⟩
  · have id : (k-1)*d+d=k*d := by rw [← Nat.succ_mul];exact congrArg (·*d) (by omega)
    exact ⟨r+1,i,by omega,by omega,by omega,by omega⟩

def separation (x y:ℕ) : ℕ := (x-y)+(y-x)

def otherHoles (A:Finset ℕ) (N p x:ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun y => y∉A ∧ y%p≠x%p)

theorem stride_divisor_witness {p N x d:ℕ} (hp:Nat.Prime p) (hd:0<d) (short:d<p)
    (room : p*d≤N) (A:Finset ℕ) (inside : A⊆Finset.Icc 1 N)
    (fa : Free (·∈A) p) (hx : x∈A) :
    ∃ y ∈ otherHoles A N p x, d ∣ separation x y := by
  obtain ⟨a,t,lo,tk,atx,last⟩ := progression_through hp.pos hd room (inside hx)
  have miss : ∃ j<p, a+j*d ∉ A := by
    by_contra! cover
    exact fa a d hd ((run_iff_forall _ _ _ _).mpr cover)
  obtain ⟨j,jk,out⟩ := miss
  have jy : j*d≤(p-1)*d := Nat.mul_le_mul_right _ (by omega)
  have interval : a+j*d∈Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have other : (a+j*d)%p≠x%p := by
    intro same
    have mod : a+j*d ≡ a+t*d [MOD p] := by rw [atx];exact same
    have co : p.Coprime d := hp.coprime_iff_not_dvd.mpr (fun dv => (not_le_of_gt short) (Nat.le_of_dvd hd dv))
    have jt := (Nat.ModEq.cancel_right_of_coprime co (mod.add_left_cancel' a)).eq_of_lt_of_lt jk tk
    exact out ((jt ▸ atx) ▸ hx)
  refine ⟨a+j*d,Finset.mem_filter.mpr ⟨interval,out,other⟩,?_⟩
  rw [← atx]
  dsimp [separation]
  rw [Nat.add_sub_add_left,Nat.add_sub_add_left,← Nat.sub_mul,← Nat.sub_mul]
  exact dvd_add (dvd_mul_left _ _) (dvd_mul_left _ _)

theorem lcm_divides_hole_distances {p N x:ℕ} (hp:Nat.Prime p) (room:p*(p-1)≤N)
    (A:Finset ℕ) (inside : A⊆Finset.Icc 1 N) (fa : Free (·∈A) p) (hx : x∈A) :
    (Finset.Icc 1 (p-1)).lcm id ∣ ∏ y ∈ otherHoles A N p x, separation x y := by
  apply Finset.lcm_dvd
  intro d hd
  obtain ⟨dp,ds⟩ := Finset.mem_Icc.mp hd
  obtain ⟨y,hy,dv⟩ := stride_divisor_witness hp dp (by omega)
    ((Nat.mul_le_mul_left p ds).trans room) A inside fa hx
  exact dv.trans (Finset.dvd_prod_of_mem _ hy)

theorem residue_spread {p N x:ℕ} (hp:Nat.Prime p) (room:p*(p-1)≤N)
    (A:Finset ℕ) (inside : A⊆Finset.Icc 1 N) (fa : Free (·∈A) p) (hx : x∈A) :
    (Finset.Icc 1 (p-1)).lcm id ≤ (N-1)^(otherHoles A N p x).card := by
  let S := otherHoles A N p x
  have xp := Finset.mem_Icc.mp (inside hx)
  have props {y:ℕ} (hy:y∈S) : 0<separation x y ∧ separation x y≤N-1 := by
    obtain ⟨iy,out,_⟩ := Finset.mem_filter.mp hy
    have yp := Finset.mem_Icc.mp iy
    have ne : x≠y := fun eq => out (eq ▸ hx)
    dsimp [separation];omega
  have pos : 0<∏ y ∈ S, separation x y := Finset.prod_pos (fun y hy => (props hy).1)
  have lower := Nat.le_of_dvd pos (lcm_divides_hole_distances hp room A inside fa hx)
  apply lower.trans
  have upper := Finset.prod_le_prod' (s := S) (f := separation x) (g := fun _ => N-1)
    (fun y hy => (props hy).2)
  simpa only [Finset.prod_const] using upper

#print axioms lcm_divides_hole_distances
#print axioms residue_spread
end ProgressionParity
