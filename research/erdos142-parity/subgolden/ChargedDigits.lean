import Mathlib

/-! # Exact cardinality of a mixed-width digit sphere

Credit: @Deldor14. Evaluate the one-digit generating polynomials at a base
larger than the total number of vectors and extract the digit at energy 459.
-/

namespace Erdos142Charged
open Finset

def charge (j : ℕ) : ℕ := ((((j:ℤ)-14)*((j:ℤ)-15))/2).toNat

theorem charge_sq {j : ℕ} (hj : j < 31) :
    8*(charge j:ℤ)+1=(2*(j:ℤ)-29)^2 := by interval_cases j <;> decide

def energy (v : List ℕ) : ℕ := (v.map charge).sum

def widths : List ℕ := [30,30,30,31,31,31,31,31,31,31,31,31]

private def prepend (x : ℕ × List ℕ) : List ℕ := x.1::x.2

private theorem prepend_injective : Function.Injective prepend := by
  rintro ⟨i,v⟩ ⟨j,w⟩ h
  obtain ⟨rfl,rfl⟩:=List.cons.inj h
  rfl

def digits : List ℕ → Finset (List ℕ)
  | [] => {[]}
  | d::ds => ((range d) ×ˢ digits ds).image prepend

theorem mem_digits {ds v : List ℕ} : v ∈ digits ds ↔ List.Forall₂ (·<·) v ds := by
  induction ds generalizing v with
  | nil => cases v <;> simp [digits]
  | cons d ds ih =>
    cases v with
    | nil => simp [digits,prepend]
    | cons j v =>
      constructor
      · intro h
        obtain ⟨⟨i,t⟩,hp,e⟩:=mem_image.mp h
        have a:=mem_range.mp (mem_product.mp hp).1
        have b:=ih.mp (mem_product.mp hp).2
        have both:=List.Forall₂.cons a b
        exact e ▸ both
      · intro h
        obtain ⟨hj,hv⟩:=List.forall₂_cons.mp h
        exact mem_image.mpr ⟨(j,v),mem_product.mpr ⟨mem_range.mpr hj,ih.mpr hv⟩,rfl⟩

def sphere (ds : List ℕ) (E : ℕ) : Finset (List ℕ) := (digits ds).filter (fun v => energy v=E)

theorem mem_sphere {v ds : List ℕ} {E : ℕ} :
    v∈sphere ds E ↔ List.Forall₂ (·<·) v ds ∧ energy v=E := by simp [sphere,mem_digits]



/-- A base larger than the number of objects precludes every carry between
their weight classes. This identity uses no bound on the maximum weight. -/
theorem extract_card {α : Type*} (A : Finset α) (h : α→ℕ) {B w : ℕ} (big : A.card < B)
    (positive : 0 < w) :
    (∑ x∈A, B^(h x))/(B^w)%B=(A.filter (fun x=>h x=w)).card := by
  classical
  have bp : 0 < B := by omega
  have wp : 0 < B^w := Nat.pow_pos bp
  let low:=fun x=> if h x < w then B^(h x) else 0
  let high:=fun x=> if w < h x then B^(h x-(w+1)) else 0
  let indicator:=fun x=> if h x = w then 1 else 0
  have split (x) : B^(h x)=low x+B^w*indicator x+B^(w+1)*high x := by
    rcases lt_trichotomy (h x) w with l|e|r
    · simp [low,high,indicator,l,l.ne,not_lt_of_ge l.le]
    · simp [low,high,indicator,e]
    · have exp : (w+1)+(h x-(w+1))=h x := by omega
      simp [low,high,indicator,r,r.ne',not_lt_of_ge r.le,←pow_add,exp]
  have sum_split := Finset.sum_congr (s₁:=A) rfl (fun x _ => split x)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at sum_split
  have range_low (x) : low x ≤ B^(w-1) := by
    by_cases l : h x < w
    · simp only [low,if_pos l]
      exact Nat.pow_le_pow_right bp (by omega)
    · simp [low,l]
  have small : (∑ x∈A, low x) < B^w := by
    calc _ ≤ ∑ _x∈A, B^(w-1) := Finset.sum_le_sum (fun x _ => range_low x)
         _ = A.card*B^(w-1) := by simp
         _ < B*B^(w-1) := Nat.mul_lt_mul_of_pos_right big (Nat.pow_pos bp)
         _ = B^(w-1)*B := Nat.mul_comm _ _
         _ = B^((w-1)+1) := (pow_succ _ _).symm
         _ = B^w := congrArg (B^·) (by omega)
  have mid : (∑ x∈A, indicator x)=(A.filter (fun x=>h x=w)).card := by
    simp [indicator,Finset.sum_boole]
  let C := (A.filter (fun x=>h x=w)).card
  have cap : C < B := (Finset.card_filter_le _ _).trans_lt big
  have form : (∑ x∈A, B^(h x)) = (∑ x∈A, low x)+B^w*(C+B*(∑ x∈A, high x)) := by
    rw [sum_split,mid,pow_succ]
    dsimp [C]
    ring
  rw [form,Nat.add_mul_div_left _ _ wp,Nat.div_eq_of_lt small,Nat.zero_add,
    Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt cap]

/-- Evaluate the one-coordinate generating polynomial at B. -/
def oneDigit (B : ℕ) : ℕ → ℕ
  | 0 => 0
  | d+1 => oneDigit B d+B^(charge d)

/-- Product of the digit generating polynomials. This recursion has one call per
coordinate and never traverses the set of vectors. -/
def packed (B : ℕ) : List ℕ → ℕ
  | [] => 1
  | d::ds => oneDigit B d*packed B ds

private theorem oneDigit_eq (B d : ℕ) : oneDigit B d=∑ j∈range d, B^(charge j) := by
  induction d with
  | zero => simp [oneDigit]
  | succ d ih => simp [oneDigit,Finset.sum_range_succ,ih]

theorem digits_card (ds : List ℕ) : (digits ds).card=ds.prod := by
  induction ds with
  | nil => simp [digits]
  | cons d ds ih =>
    simp [digits,Finset.card_image_of_injective _ prepend_injective,ih]

theorem generating_identity (B : ℕ) (ds : List ℕ) :
    (∑ v∈digits ds, B^(energy v))=packed B ds := by
  induction ds with
  | nil => simp [digits,energy,packed]
  | cons d ds ih =>
    rw [digits,Finset.sum_image (fun i _ j _ e => prepend_injective e),Finset.sum_product,packed]
    simp only [prepend,energy,List.map_cons,List.sum_cons,pow_add]
    change (∑ i∈range d, ∑ v∈digits ds, B^(charge i)*B^(energy v))=_
    simp_rw [←Finset.mul_sum,ih]
    rw [←Finset.sum_mul,←oneDigit_eq]

theorem sphere_card_eq_packed (ds : List ℕ) {E B : ℕ} (big : ds.prod < B)
    (ep : 0 < E) : (sphere ds E).card=packed B ds/(B^E)%B := by
  have h:=extract_card (digits ds) energy (by rwa [digits_card] : (digits ds).card<B) ep
  rw [generating_identity] at h
  exact h.symm

/-- Exact charge-459 coefficient for three width-30 and nine width-31 digits. -/
theorem sphere_card : (sphere widths 459).card=2303115151489024 := by
  rw [sphere_card_eq_packed widths (B:=2^64) (by decide) (by decide)]
  decide +kernel

theorem sphere_card_gt : 2^51 < (sphere widths 459).card := by
  rw [sphere_card]; decide

end Erdos142Charged
#print axioms Erdos142Charged.charge_sq
#print axioms Erdos142Charged.mem_sphere
#print axioms Erdos142Charged.generating_identity
#print axioms Erdos142Charged.sphere_card_eq_packed
#print axioms Erdos142Charged.sphere_card
#print axioms Erdos142Charged.sphere_card_gt
