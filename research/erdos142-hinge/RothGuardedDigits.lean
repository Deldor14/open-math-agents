import RothLongDigitInformation

open Finset
namespace Erdos142LongDigits

/-- A finite progression expressed by its local midpoint equations can
    run in either direction inside a digit. A free seed forces constancy. -/
theorem constant_of_midpoints {k : ℕ} (hk : 2≤k) (U : Finset ℕ) (free : Free k U)
    (f : ℕ → ℕ) (inside : ∀ i<k, f i ∈ U)
    (mid : ∀ i, i+2<k → f i+f (i+2)=f (i+1)+f (i+1)) :
    ∀ i<k, f i=f 0 := by
  have line : ∀ i, i<k → f i+i*f 0=f 0+i*f 1 := by
    intro i
    induction i using Nat.twoStepInduction with
    | zero => simp
    | one => simp [Nat.add_comm]
    | more i prev next =>
      intro hi
      have h1 := prev (by omega)
      have h2 := next (by omega)
      have h3 := mid i hi
      simp only [Nat.succ_mul] at h2 ⊢
      omega
  by_cases up : f 0<f 1
  · exfalso
    let e := f 1-f 0
    have id : f 1=f 0+e := by dsimp [e]; omega
    apply free (f 0) e (by dsimp [e]; omega)
    intro i hi
    have h := line i hi
    rw [id,Nat.mul_add] at h
    convert inside i hi using 1
    omega
  · by_cases down : f 1<f 0
    · exfalso
      let e := f 0-f 1
      have id : f 0=f 1+e := by dsimp [e]; omega
      have rev (i : ℕ) (hi : i<k) : f i+i*e=f 0 := by
        have h := line i hi
        nth_rw 1 [id] at h
        rw [Nat.mul_add] at h
        omega
      apply free (f (k-1)) e (by dsimp [e]; omega)
      intro i hi
      have near := rev (k-1-i) (by omega)
      have last := rev (k-1) (by omega)
      have index : k-1=(k-1-i)+i := by omega
      have dist := congrArg (fun j => j*e) index
      change (k-1)*e=(k-1-i+i)*e at dist
      rw [Nat.add_mul] at dist
      convert inside (k-1-i) (by omega) using 1
      omega
    · have id : f 1=f 0 := by omega
      intro i hi
      have h := line i hi
      rw [id] at h
      omega

def digitProduct (b : ℕ) (U V : Finset ℕ) :=
  (U ×ˢ V).image (fun p => p.1+b*p.2)

theorem product_card {m : ℕ} (hm : 0<m) (U V : Finset ℕ) (fit : U ⊆ range m) :
    (digitProduct (2*m) U V).card=U.card*V.card := by
  apply Eq.trans (card_image_of_injOn ?_) (card_product _ _)
  rintro ⟨u,v⟩ hp ⟨u',v'⟩ hp' eq
  have hu := mem_range.mp (fit (mem_product.mp hp).1)
  have hu' := mem_range.mp (fit (mem_product.mp hp').1)
  change u+2*m*v=u'+2*m*v' at eq
  have rem := congrArg (fun z => z%(2*m)) eq
  simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (by omega : u<2*m),
    Nat.mod_eq_of_lt (by omega : u'<2*m)] at rem
  apply Prod.ext rem
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0<2*m) (Nat.add_left_cancel (rem ▸ eq))

/-- A guarded integer digit product preserves avoidance of k-term
    progressions, including seeds with nonconstant three-term progressions. -/
theorem product_free {k m : ℕ} (hk : 2≤k) (hm : 0<m) (U V : Finset ℕ)
    (fit : U ⊆ range m) (hu : Free k U) (hv : Free k V) :
    Free k (digitProduct (2*m) U V) := by
  intro x e he points
  let b := 2*m
  have bp : 0<b := by dsimp [b]; omega
  let value (i : ℕ) := x+i*e
  let low (i : ℕ) := value i%b
  let high (i : ℕ) := value i/b
  have digits (i : ℕ) (hi : i<k) : low i ∈ U ∧ high i ∈ V := by
    obtain ⟨⟨u,v⟩,mem,eq⟩ := mem_image.mp (points i hi)
    change u+b*v=value i at eq
    have small : u<b := by have := mem_range.mp (fit (mem_product.mp mem).1); dsimp [b]; omega
    dsimp only [low,high]
    rw [← eq]
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt small]
    rw [Nat.mul_comm b v,Nat.add_mul_div_right _ _ bp,Nat.div_eq_of_lt small,zero_add]
    exact mem_product.mp mem
  have trunc (i j : ℕ) (hi : i<k) (hj : j<k) : (value i+value j)%b=low i+low j := by
    rw [Nat.add_mod]
    apply Nat.mod_eq_of_lt
    have l := mem_range.mp (fit (digits i hi).1)
    have r := mem_range.mp (fit (digits j hj).1)
    change low i+low j<2*m
    omega
  have seq (i : ℕ) : value i+value (i+2)=value (i+1)+value (i+1) := by dsimp [value]; ring
  have lowmid (i : ℕ) (h : i+2<k) : low i+low (i+2)=low (i+1)+low (i+1) := by
    rw [← trunc i _ (by omega) h,seq,trunc _ _ (by omega) (by omega)]
  have reb (i : ℕ) : low i+b*high i=value i := Nat.mod_add_div _ _
  have highmid (i : ℕ) (h : i+2<k) : high i+high (i+2)=high (i+1)+high (i+1) := by
    apply Nat.eq_of_mul_eq_mul_left bp
    simp only [Nat.mul_add]
    linarith only [reb i,reb (i+1),reb (i+2),seq i,lowmid i h]
  have l := constant_of_midpoints hk U hu low (fun i hi => (digits i hi).1) lowmid 1 (by omega)
  have r := constant_of_midpoints hk V hv high (fun i hi => (digits i hi).2) highmid 1 (by omega)
  have one := reb 1
  rw [l,r,reb] at one
  simp [value] at one
  omega

#print axioms constant_of_midpoints
#print axioms product_card
#print axioms product_free
end Erdos142LongDigits
