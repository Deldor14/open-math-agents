import RothGuardedDigits
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

open Finset
open Erdos142LongDigits
namespace Erdos142PrimeRows

/-- Different occupied residues may carry independently chosen free rows. -/
theorem fibered_free {k b w : ℕ} (hk : 2≤k) (bp : 0<b) (guard : 2*w≤b+1)
    (A U : Finset ℕ) (row : ℕ → Finset ℕ) (fit : U ⊆ range w)
    (outer : Free k U) (inner : ∀ u ∈ U, Free k (row u))
    (members : ∀ z ∈ A, z%b ∈ U ∧ z/b ∈ row (z%b)) : Free k A := by
  intro x e he points
  let value (i : ℕ) := x+i*e
  let low (i : ℕ) := value i%b
  let high (i : ℕ) := value i/b
  have ins (i : ℕ) (hi : i<k) : low i ∈ U ∧ high i ∈ row (low i) := members _ (points i hi)
  have trunc (i j : ℕ) (hi : i<k) (hj : j<k) : (value i+value j)%b=low i+low j := by
    rw [Nat.add_mod]
    apply Nat.mod_eq_of_lt
    have l := mem_range.mp (fit (ins i hi).1)
    have r := mem_range.mp (fit (ins j hj).1)
    change low i+low j<b
    omega
  have seq (i : ℕ) : value i+value (i+2)=value (i+1)+value (i+1) := by dsimp [value];ring
  have lm (i : ℕ) (h : i+2<k) : low i+low (i+2)=low (i+1)+low (i+1) := by
    rw [← trunc i _ (by omega) h,seq,trunc _ _ (by omega) (by omega)]
  have reb (i : ℕ) : low i+b*high i=value i := Nat.mod_add_div _ _
  have hm (i : ℕ) (h : i+2<k) : high i+high (i+2)=high (i+1)+high (i+1) := by
    apply Nat.eq_of_mul_eq_mul_left bp
    simp only [Nat.mul_add]
    linarith only [reb i,reb (i+1),reb (i+2),seq i,lm i h]
  have lo := constant_of_midpoints hk U outer low (fun i hi => (ins i hi).1) lm
  have sub (i : ℕ) (hi : i<k) : high i ∈ row (low 0) := by rw [← lo i hi]; exact (ins i hi).2
  have hi := constant_of_midpoints hk _ (inner _ (ins 0 (by omega)).1) high sub hm
  have one := reb 1
  rw [lo 1 (by omega),hi 1 (by omega),reb] at one
  simp [value] at one
  omega

/-- Observed heights are translated copies of seed sites, cropped to [0,T). -/
def shifted (T σ : ℕ) (V : Finset ℕ) :=
  (range T).filter (fun h => h+σ ∈ V.image (fun v => T+v))

theorem shifted_free {k : ℕ} (hk : 0<k) (T σ : ℕ) (V : Finset ℕ) (hv : Free k V) :
    Free k (shifted T σ V) := by
  intro x e he pts
  obtain ⟨v,hv0,eq⟩ := mem_image.mp (mem_filter.mp (pts 0 hk)).2
  simp only [Nat.zero_mul,Nat.add_zero] at eq
  apply hv v e he
  intro i hi
  obtain ⟨y,hy,el⟩ := mem_image.mp (mem_filter.mp (pts i hi)).2
  have ze : y=v+i*e := by omega
  rwa [← ze]

/-- For every individual height exactly |V| of the 2T shifts accept it. -/
def options (T h : ℕ) (V : Finset ℕ) := V.image (fun v => T+v-h)

theorem options_card {T h : ℕ} (hh : h<T) (V : Finset ℕ) : (options T h V).card=V.card := by
  apply card_image_of_injective
  intro x y e
  dsimp only at e
  omega

theorem options_range {T h : ℕ} (V : Finset ℕ) (fit : V ⊆ range T) :
    options T h V ⊆ range (2*T) := by
  intro x hx
  obtain ⟨v,hv,rfl⟩ := mem_image.mp hx
  have cap := mem_range.mp (fit hv)
  apply mem_range.mpr
  omega

theorem mem_options {T h σ : ℕ} (hh : h<T) (V : Finset ℕ) :
    σ ∈ options T h V ↔ h ∈ shifted T σ V := by
  constructor
  · intro inO
    obtain ⟨v,hv,rfl⟩ := mem_image.mp inO
    exact mem_filter.mpr ⟨mem_range.mpr hh,mem_image.mpr ⟨v,hv,by omega⟩⟩
  · intro inS
    obtain ⟨v,hv,eq⟩ := mem_image.mp (mem_filter.mp inS).2
    exact mem_image.mpr ⟨v,hv,by omega⟩

/-- A full period of a progression with coprime step visits each residue once. -/
theorem residue_bijective {p : ℕ} (pos : 0<p) (a q : ℕ) (unit : q.Coprime p) :
    Function.Bijective (fun i : Fin p => (⟨(a+i.val*q)%p,Nat.mod_lt _ pos⟩ : Fin p)) := by
  apply (Finite.injective_iff_bijective).mp
  intro i j eq
  have rem := congrArg Fin.val eq
  have ed : ((a+i.val*q:ℕ):ZMod p)=((a+j.val*q:ℕ):ZMod p) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mpr rem
  have uq := (ZMod.isUnit_iff_coprime q p).mpr unit
  push_cast at ed
  have same : (i.val:ZMod p)=j.val := uq.mul_right_cancel (add_left_cancel ed)
  have g := (ZMod.natCast_eq_natCast_iff' i.val j.val p).mp same
  exact Fin.ext (by simpa only [Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using g)

#print axioms fibered_free
#print axioms shifted_free
#print axioms options_card
#print axioms mem_options
#print axioms residue_bijective
end Erdos142PrimeRows
