import Mathlib

open Finset
namespace Erdos142CriticalSampling

variable {α : Type*}

def weight (family : Finset (Finset α)) (z : ℝ) : ℝ :=
  ∑ I ∈ family, z ^ I.card

theorem powerset_weight (V : Finset α) (z : ℝ) :
    weight V.powerset z = (1+z)^V.card := by
  simpa [weight] using (prod_one_add (f := fun _ : α => z) V).symm

/-- A compulsory fingerprint is counted once and removed before recursion. -/
theorem peel [DecidableEq α] (part : Finset (Finset α)) (F : Finset α)
    (required : ∀ I ∈ part, F ⊆ I) (z : ℝ) :
    weight part z = z ^ F.card * weight (part.image (fun I => I \ F)) z := by
  classical
  have inj : Set.InjOn (fun I : Finset α => I \ F) (↑part : Set (Finset α)) := by
    intro I hi J hj eq
    change I \ F = J \ F at eq
    have hI := sdiff_union_of_subset (required I hi)
    have hJ := sdiff_union_of_subset (required J hj)
    exact hI.symm.trans ((congrArg (fun X : Finset α => X ∪ F) eq).trans hJ)
  unfold weight
  rw [sum_image inj, mul_sum]
  apply sum_congr rfl
  intro I hI
  have hc := card_sdiff_add_card_inter I F
  rw [inter_eq_right.mpr (required I hI)] at hc
  rw [← pow_add]
  congr 1
  omega

/-- Changing the weight absorbs the number of possible small fingerprints. -/
theorem tilted_fingerprints (V : Finset α) (D : Finset (Finset α))
    (sub : D ⊆ V.powerset) {j : ℕ} (short : ∀ F ∈ D, F.card ≤ j)
    {z H : ℝ} (hz : 0 ≤ z) (hH : 1 ≤ H) :
    weight D z ≤ H^j * (1+z/H)^V.card := by
  have pos : 0 < H := by linarith
  have hscale : H*(z/H)=z := by field_simp
  calc
    weight D z ≤ ∑ F ∈ D, H^j*(z/H)^F.card := by
      apply sum_le_sum
      intro F hF
      calc
        z^F.card = H^F.card * (z/H)^F.card := by rw [← mul_pow, hscale]
        _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hH (short F hF))
          (pow_nonneg (div_nonneg hz pos.le) _)
    _ = H^j * weight D (z/H) := by rw [weight,mul_sum]
    _ ≤ H^j * weight V.powerset (z/H) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg pos.le _)
      apply sum_le_sum_of_subset_of_nonneg sub
      intro F _ _
      exact pow_nonneg (div_nonneg hz pos.le) _
    _ = _ := by rw [powerset_weight]

/-- A family's weighted count controls every individual rank. -/
theorem rank_weight (family : Finset (Finset α)) (s : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    ((family.filter (fun I => I.card = s)).card : ℝ)*z^s ≤ weight family z := by
  let D := family.filter (fun I => I.card = s)
  calc
    _ = ∑ _I ∈ D, z^s := by simp [D]
    _ = ∑ I ∈ D, z^I.card := by
      apply sum_congr rfl
      intro I hI
      rw [(mem_filter.mp hI).2]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun I _ _ => pow_nonneg hz I.card)

private theorem small_multiple {x P : ℤ} (lo : -P < x) (hi : x < P) (dvd : P ∣ x) :
    x = 0 := by
  by_cases h : 0 ≤ x
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h hi dvd
  · have e := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ -x by omega)
      (show -x < P by omega) (dvd_neg.mpr dvd)
    omega

/-- Modular progressions in the occupied half project to integer progressions in the bins. -/
theorem bin_projection {P L X Y Z i j k e f g : ℤ} (pos : 0 < L)
    (hX : 0 ≤ X ∧ 2*X < P) (hY : 0 ≤ Y ∧ 2*Y < P) (hZ : 0 ≤ Z ∧ 2*Z < P)
    (modular : P ∣ X+Z-2*Y)
    (xbin : X = 4*L*i+e) (ybin : Y=4*L*j+f) (zbin : Z=4*L*k+g)
    (he : 0 ≤ e ∧ e<L) (hf : 0 ≤ f ∧ f<L) (hg : 0 ≤ g ∧ g<L) :
    i+k=2*j := by
  have zero := small_multiple (x := X+Z-2*Y) (by omega) (by omega) modular
  have div : 4*L ∣ 2*f-e-g := ⟨i+k-2*j, by linear_combination xbin+zbin-2*ybin-zero⟩
  have err := small_multiple (x := 2*f-e-g) (by omega) (by omega) div
  have prod : 4*L*(i+k-2*j) = 0 := by linear_combination zero-xbin-zbin+2*ybin+err
  obtain h | h := mul_eq_zero.mp prod <;> omega

/-- The pairwise-uniform affine map includes equal target values. -/
theorem unique_affine_evaluations {F : Type*} [Field F] {i j : F} (ij : i ≠ j) (y z : F) :
    ∃! ab : F × F, ab.1*i+ab.2=y ∧ ab.1*j+ab.2=z := by
  let a := (z-y)/(j-i)
  have denom : j-i ≠ 0 := sub_ne_zero.mpr ij.symm
  have slope : a*(j-i)=z-y := div_mul_cancel₀ _ denom
  refine ⟨(a,y-a*i), ⟨by dsimp; ring, by dsimp; linear_combination slope⟩, ?_⟩
  rintro ⟨u,v⟩ ⟨hy,hz⟩
  change u*i+v=y at hy
  change u*j+v=z at hz
  have hu : u = a := (eq_div_iff denom).mpr (by linear_combination hz-hy)
  subst u
  exact Prod.ext rfl (by change v=y-a*i; linear_combination hy)

#print axioms powerset_weight
#print axioms peel
#print axioms tilted_fingerprints
#print axioms rank_weight
#print axioms bin_projection
#print axioms unique_affine_evaluations

end Erdos142CriticalSampling
