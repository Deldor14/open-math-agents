import Mathlib

/-! Gaussian-weighted midpoint defects of a set represented by two digits.
The outer digit is drawn from a progression-free alphabet. -/

namespace Erdos142WeightedDefect
open Finset

def pack (H : ℕ) (p : ℕ × ℕ) := H*p.1+p.2

def grid (H : ℕ) (A E : Finset ℕ) := (A ×ˢ E).image (pack H)

noncomputable def weight (κ : ℝ) (u v w : ℕ) : ℝ :=
  Real.exp (-κ*((u:ℝ)+w-2*v)^2)

noncomputable def W (κ : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ u ∈ S, ∑ v ∈ S, ∑ w ∈ S, weight κ u v w

private theorem inj {H h : ℕ} (A E : Finset ℕ) (small : 2*h < H) (low : ∀ u ∈ E, u ≤ h) :
    Set.InjOn (pack H) (A ×ˢ E : Finset _) := by
  rintro ⟨a,u⟩ hau ⟨b,v⟩ hbv eq
  have hu : u < H := by have := low u (mem_product.mp hau).2;omega
  have hv : v < H := by have := low v (mem_product.mp hbv).2;omega
  change H*a+u=H*b+v at eq
  have unit := congrArg (fun n => n%H) eq
  simp [Nat.add_mod,Nat.mod_eq_of_lt hu,Nat.mod_eq_of_lt hv] at unit
  subst v
  have ab := Nat.eq_of_mul_eq_mul_left (by omega : 0 < H) (Nat.add_right_cancel eq)
  simp [ab]

theorem grid_card {H h : ℕ} (A E : Finset ℕ) (small : 2*h < H)
    (low : ∀ u ∈ E, u ≤ h) : (grid H A E).card=A.card*E.card := by
  rw [grid,card_image_of_injOn (inj A E small low),card_product]

private theorem separated {H h a b c u v w : ℕ}
    (neq : a+c ≠ b+b) (hu : u ≤ h) (hv : v ≤ h) (hw : w ≤ h) :
    (H:ℝ)-2*h ≤ |(pack H (a,u):ℝ)+pack H (c,w)-2*pack H (b,v)| := by
  have ru : (u:ℝ) ≤ h := by exact_mod_cast hu
  have rv : (v:ℝ) ≤ h := by exact_mod_cast hv
  have rw' : (w:ℝ) ≤ h := by exact_mod_cast hw
  simp only [pack, Nat.cast_add, Nat.cast_mul]
  rcases lt_or_gt_of_ne neq with l|l
  · have s : H*(a+c+1) ≤ H*(b+b) := Nat.mul_le_mul_left _ l
    have ss : (H:ℝ)*(a+c+1) ≤ H*(b+b) := by exact_mod_cast s
    apply le_trans _ (neg_le_abs _)
    linarith only [ss,ru,rw',Nat.cast_nonneg (α:=ℝ) v]
  · have s : H*(b+b+1) ≤ H*(a+c) := Nat.mul_le_mul_left _ l
    have ss : (H:ℝ)*(b+b+1) ≤ H*(a+c) := by exact_mod_cast s
    apply le_trans _ (le_abs_self _)
    linarith only [ss,rv,Nat.cast_nonneg (α:=ℝ) u,Nat.cast_nonneg (α:=ℝ) w]

private theorem block {κ : ℝ} (hκ : 0 ≤ κ) {H h a b c : ℕ} (E : Finset ℕ)
    (small : 2*h < H) (low : ∀ u ∈ E, u ≤ h) (neq : a+c ≠ b+b) :
    (∑ u ∈ E, ∑ v ∈ E, ∑ w ∈ E, weight κ (pack H (a,u)) (pack H (b,v)) (pack H (c,w))) ≤
      (E.card:ℝ)^3 * Real.exp (-κ*((H:ℝ)-2*h)^2) := by
  let B := Real.exp (-κ*((H:ℝ)-2*h)^2)
  calc _ ≤ ∑ _u ∈ E, ∑ _v ∈ E, ∑ _w ∈ E, B := by
            refine sum_le_sum (fun u hu => sum_le_sum (fun v hv => sum_le_sum (fun w hw => ?_)))
            have dist := separated (H:=H) neq (low u hu) (low v hv) (low w hw)
            have Hh : (2:ℝ)*h < H := by exact_mod_cast small
            have sq := sq_le_sq₀ (sub_nonneg.mpr Hh.le) (abs_nonneg _) |>.2 dist
            rw [sq_abs] at sq
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left sq (neg_nonpos.mpr hκ))
       _ = _ := by simp [B];ring

private theorem expand {H h : ℕ} (A E : Finset ℕ) (small : 2*h < H)
    (low : ∀ u ∈ E, u ≤ h) (κ : ℝ) :
    W κ (grid H A E) =
      ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, ∑ u ∈ E, ∑ v ∈ E, ∑ w ∈ E,
        weight κ (pack H (a,u)) (pack H (b,v)) (pack H (c,w)) := by
  unfold W grid
  simp_rw [sum_image (fun x hx y hy he => inj A E small low hx hy he),sum_product]
  apply sum_congr rfl
  intro a _
  rw [sum_comm (s:=E) (t:=A)]
  apply sum_congr rfl
  intro b _
  conv_lhs => arg 2; ext u; rw [sum_comm (s:=E) (t:=A)]
  rw [sum_comm (s:=E) (t:=A)]

theorem two_digit_bound {κ : ℝ} (hκ : 0 ≤ κ) {H h : ℕ} (A E : Finset ℕ)
    (small : 2*h < H) (low : ∀ u ∈ E, u ≤ h) (free : ThreeAPFree (A : Set ℕ)) :
    W κ (grid H A E) ≤ A.card*W κ E +
      ((A.card*E.card:ℕ):ℝ)^3 * Real.exp (-κ*((H:ℝ)-2*h)^2) := by
  rw [expand A E small low κ]
  let B := (E.card:ℝ)^3 * Real.exp (-κ*((H:ℝ)-2*h)^2)
  calc _ ≤ ∑ a ∈ A, ∑ b ∈ A, ∑ c ∈ A, ((if b=a ∧ c=a then W κ E else 0)+B) := by
            refine sum_le_sum (fun a ha => sum_le_sum (fun b hb => sum_le_sum (fun c hc => ?_)))
            by_cases he : b=a ∧ c=a
            · obtain ⟨hba,hca⟩ := he
              subst b c
              simp only [and_self,if_true]
              have same (u v w : ℕ) : weight κ (pack H (a,u)) (pack H (a,v)) (pack H (a,w)) =
                  weight κ u v w := by
                unfold weight pack
                push_cast
                ring_nf
              simp_rw [same]
              exact le_add_of_nonneg_right (by dsimp [B];positivity)
            · rw [if_neg he,zero_add]
              apply block hκ E small low
              intro eq
              have h1 := free ha hb hc eq
              apply he
              exact ⟨h1.symm,by omega⟩
       _ = _ := by
         simp_rw [sum_add_distrib]
         have diag (a : ℕ) (ha : a ∈ A) :
             (∑ b ∈ A, ∑ c ∈ A, if b=a ∧ c=a then W κ E else 0) = W κ E := by
           simp_rw [ite_and]
           simp [ha,sum_ite_irrel]
         rw [sum_congr rfl diag]
         simp [B]
         ring

theorem grid_free {H h : ℕ} (A E : Finset ℕ) (small : 2*h < H)
    (low : ∀ u ∈ E, u ≤ h) (FA : ThreeAPFree (A : Set ℕ)) (FE : ThreeAPFree (E : Set ℕ)) :
    ThreeAPFree (grid H A E : Set ℕ) := by
  intro x hx y hy z hz hap
  obtain ⟨⟨a,u⟩,mx,rfl⟩ := mem_image.mp hx
  obtain ⟨⟨b,v⟩,my,rfl⟩ := mem_image.mp hy
  obtain ⟨⟨c,w⟩,mz,rfl⟩ := mem_image.mp hz
  obtain ⟨ha,hu⟩ := mem_product.mp mx
  obtain ⟨hb,hv⟩ := mem_product.mp my
  obtain ⟨hc,hw⟩ := mem_product.mp mz
  have hi : a+c=b+b := by
    by_contra neq
    have sep := separated (H:=H) neq (low u hu) (low v hv) (low w hw)
    have eqr : (pack H (a,u):ℝ)+pack H (c,w)=pack H (b,v)+pack H (b,v) := by exact_mod_cast hap
    rw [show (pack H (a,u):ℝ)+pack H (c,w)-2*pack H (b,v)=0 by linarith,abs_zero] at sep
    have inp : (2:ℝ)*h < H := by exact_mod_cast small
    linarith
  have ab := FA ha hb hc hi
  have lo : u+w=v+v := by
    change (H*a+u)+(H*c+w)=(H*b+v)+(H*b+v) at hap
    have prod := congrArg (fun n : ℕ => H*n) hi
    nlinarith only [prod,hap]
  exact congrArg (pack H) (Prod.ext ab (FE hu hv hw lo))

theorem relative_bound {κ : ℝ} (hκ : 0 ≤ κ) {H h : ℕ}
    (A E : Finset ℕ) (hA : A.Nonempty) (hE : E.Nonempty)
    (small : 2*h < H) (low : ∀ u ∈ E, u ≤ h) (free : ThreeAPFree (A : Set ℕ)) :
    W κ (grid H A E)/(grid H A E).card ≤ W κ E/E.card+
      ((grid H A E).card:ℝ)^2*Real.exp (-κ*((H:ℝ)-2*h)^2) := by
  rw [grid_card A E small low,Nat.cast_mul]
  have pa : (0:ℝ)<A.card := by exact_mod_cast hA.card_pos
  have pe : (0:ℝ)<E.card := by exact_mod_cast hE.card_pos
  apply (div_le_iff₀ (mul_pos pa pe)).2
  have bound := two_digit_bound hκ A E small low free
  rw [Nat.cast_mul] at bound
  apply bound.trans_eq
  field_simp

#print axioms grid_free
#print axioms relative_bound
#print axioms grid_card
#print axioms two_digit_bound
end Erdos142WeightedDefect
