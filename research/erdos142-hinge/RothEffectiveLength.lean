import RothCriticalSampling
import Mathlib

open Finset Erdos142CriticalSampling
namespace Erdos142EffectiveLength

variable {α : Type*} [DecidableEq α]

/-- Decomposing by the actual fingerprint, not by all containers containing I,
accounts for its weight once. -/
theorem weighted_step (family D : Finset (Finset α)) (g : Finset α → Finset α)
    (mapped : ∀ I ∈ family, g I ∈ D) (inside : ∀ I ∈ family, g I ⊆ I)
    {p K : ℝ} (hp : 0 ≤ p)
    (child : ∀ F ∈ D, weight ((family.filter (fun I => g I = F)).image (fun I => I \ F)) p ≤ K) :
    weight family p ≤ weight D p * K := by
  classical
  calc
    weight family p = ∑ F ∈ D, weight (family.filter (fun I => g I = F)) p :=
      (sum_fiberwise_of_maps_to mapped (fun I => p^I.card)).symm
    _ ≤ ∑ F ∈ D, p^F.card * K := by
      apply sum_le_sum
      intro F hF
      rw [peel _ F]
      · exact mul_le_mul_of_nonneg_left (child F hF) (pow_nonneg hp _)
      · intro I hI
        have hs := inside I (mem_filter.mp hI).1
        rwa [(mem_filter.mp hI).2] at hs
    _ = _ := by rw [weight,sum_mul]

/-- Product of the stage prices for a finite decreasing-cap construction.
A family is at level i exactly when the predicate Level i holds for it. -/
theorem weighted_iteration (Level : ℕ → Finset (Finset α) → Prop) (price : ℕ → ℝ)
    {p terminal : ℝ} (hp : 0 ≤ p) (ht : 0 ≤ terminal) (hn : ∀ i, 0 ≤ price i)
    (base : ∀ A, Level 0 A → weight A p ≤ terminal)
    (split : ∀ i A, Level (i+1) A →
      ∃ (D : Finset (Finset α)) (g : Finset α → Finset α),
        weight D p ≤ price i ∧ (∀ I ∈ A, g I ∈ D) ∧ (∀ I ∈ A, g I ⊆ I) ∧
        ∀ F ∈ D, Level i ((A.filter (fun I => g I = F)).image (fun I => I \ F))) :
    ∀ j A, Level j A → weight A p ≤ terminal * ∏ i ∈ range j, price i := by
  intro j
  induction j with
  | zero => simpa using base
  | succ j ih =>
    intro A hA
    obtain ⟨D,g,cap,mapped,inside,rest⟩ := split j A hA
    have step := weighted_step A D g mapped inside hp (fun F hF => ih _ (rest F hF))
    have nonneg : 0 ≤ terminal * ∏ i ∈ range j, price i :=
      mul_nonneg ht (prod_nonneg (fun i _ => hn i))
    calc
      _ ≤ _ := step
      _ ≤ price j * (terminal * ∏ i ∈ range j, price i) :=
        mul_le_mul_of_nonneg_right cap nonneg
      _ = _ := by rw [prod_range_succ]; ring

omit [DecidableEq α] in
/-- Explicit weight cost of a stage with scale factor a and fingerprint budget T/a³. -/
theorem stage_weight (V : Finset α) (D : Finset (Finset α)) (sub : D ⊆ V.powerset)
    {j : ℕ} (short : ∀ F ∈ D, F.card ≤ j) {a p T : ℝ}
    (ha : 1 ≤ a) (hp : 0 ≤ p) (hj : (j:ℝ)*a^3 ≤ T)
    (volume : p*V.card ≤ 2*T*a) : weight D p ≤ Real.exp (3*T/a) := by
  have pa : 0 < a := by linarith
  have hs : 1 ≤ a^2 := by nlinarith
  have bound := tilted_fingerprints V D sub short hp hs
  have first : (a^2)^j ≤ Real.exp ((j:ℝ)*a^2) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (sq_nonneg a) (by linarith [Real.add_one_le_exp (a^2)]) _
  have second : (1+p/a^2)^V.card ≤ Real.exp ((V.card:ℝ)*(p/a^2)) := by
    rw [Real.exp_nat_mul]
    apply pow_le_pow_left₀ (by positivity)
    linarith [Real.add_one_le_exp (p/a^2)]
  have one : (j:ℝ)*a^2 ≤ T/a := (le_div_iff₀ pa).mpr (by nlinarith)
  have two : (V.card:ℝ)*(p/a^2) ≤ 2*T/a := by
    field_simp [pa.ne']
    nlinarith [mul_le_mul_of_nonneg_right volume pa.le]
  calc
    _ ≤ _ := bound
    _ ≤ _ := mul_le_mul first second (by positivity) (by positivity)
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr ((add_le_add one two).trans_eq (by ring))

theorem dyadic_prices (T : ℝ) (d : ℕ) :
    ∏ i ∈ range d, Real.exp (3*T/2^i) = Real.exp (6*T-6*T/2^d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [prod_range_succ,ih,← Real.exp_add,pow_succ]
    congr 1
    field_simp
    ring

/-- The covering hypotheses below are the finite output required of a container
theorem. The rest of the partition-function iteration is proved here. -/
theorem partition_bound (Level : ℕ → Finset (Finset α) → Prop) {p T : ℝ}
    (hp : 0 ≤ p) (ht : 0 ≤ T) (base : ∀ A, Level 0 A → weight A p ≤ Real.exp T)
    (covers : ∀ i A, Level (i+1) A →
      ∃ (V : Finset α) (D : Finset (Finset α)) (g : Finset α → Finset α) (j : ℕ),
        D ⊆ V.powerset ∧ (∀ F ∈ D, F.card ≤ j) ∧
        (j:ℝ)*(2^i:ℝ)^3 ≤ T ∧ p*V.card ≤ 2*T*2^i ∧
        (∀ I ∈ A, g I ∈ D) ∧ (∀ I ∈ A, g I ⊆ I) ∧
        ∀ F ∈ D, Level i ((A.filter (fun I => g I = F)).image (fun I => I \ F))) :
    ∀ d A, Level d A → weight A p ≤ Real.exp (7*T) := by
  intro d A hA
  have h := weighted_iteration Level (fun i => Real.exp (3*T/2^i)) hp
    (Real.exp_nonneg T) (fun i => Real.exp_nonneg _) base (by
      intro i B hB
      obtain ⟨V,D,g,j,sub,short,hj,vol,map,inc,rest⟩ := covers i B hB
      exact ⟨D,g,stage_weight V D sub short (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
        hp hj vol,map,inc,rest⟩) d A hA
  rw [dyadic_prices,← Real.exp_add] at h
  apply h.trans (Real.exp_le_exp.mpr _)
  have : 0 ≤ 6*T/2^d := by positivity
  linarith

/-- In the shifted half of the cyclic residue system, an integer midpoint
condition on the original sites lifts without wraparound. -/
theorem residue_midpoint {b x y z X Y Z c : ℤ}
    (hx : 0 ≤ x ∧ x<b) (hy : 0 ≤ y ∧ y<b) (hz : 0 ≤ z ∧ z<b)
    (rx : 2*b ∣ X-c-x) (ry : 2*b ∣ Y-c-y) (rz : 2*b ∣ Z-c-z)
    (ap : X+Z=2*Y) : x+z=2*y := by
  obtain ⟨u,hu⟩ := rx
  obtain ⟨v,hv⟩ := ry
  obtain ⟨w,hw⟩ := rz
  have dvd : 2*b ∣ x+z-2*y := ⟨-(u+w-2*v), by linear_combination ap-hu-hw+2*hv⟩
  by_cases h : 0 ≤ x+z-2*y
  · have := Int.eq_zero_of_dvd_of_nonneg_of_lt h (by omega) dvd
    omega
  · have := Int.eq_zero_of_dvd_of_nonneg_of_lt (show 0 ≤ -(x+z-2*y) by omega)
      (show -(x+z-2*y)<2*b by omega) (dvd_neg.mpr dvd)
    omega

/-- Progression-freeness for a set of integers, allowing either orientation. -/
def Free (k : ℕ) (X : Set ℤ) : Prop :=
  ∀ a d : ℤ, (∀ i : ℕ, i < k → a + (i:ℤ)*d ∈ X) → d=0

private theorem affine_of_midpoints {k : ℕ} (r : ℕ → ℤ)
    (mid : ∀ i, i+2<k → r i+r (i+2)=2*r (i+1)) :
    ∀ i, i<k → r i=r 0 + (i:ℤ)*(r 1-r 0) := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero => simp
  | one => intro _; push_cast; ring
  | more i h0 h1 =>
    intro hi
    have m := mid i hi
    have e0 := h0 (by omega)
    have e1 := h1 (by omega)
    push_cast at e1 ⊢
    linear_combination m - e0 + 2*e1

/-- Free choices within every occupied residue class combine to a free set. -/
theorem residue_union_free {k : ℕ} (hk : 0 < k) {X T : Set ℤ} {b c : ℤ}
    (half : ∀ t ∈ T, 0 ≤ t ∧ t<b) (tf : Free k T)
    (allowed : ∀ x ∈ X, (x-c) % (2*b) ∈ T)
    (fibers : ∀ t ∈ T, Free k {x | x ∈ X ∧ (x-c) % (2*b) = t}) : Free k X := by
  intro a d terms
  let x (i : ℕ) := a+(i:ℤ)*d
  let r (i : ℕ) := (x i-c) % (2*b)
  have inT (i : ℕ) (hi : i<k) : r i ∈ T := allowed _ (terms i hi)
  have divides (i : ℕ) : 2*b ∣ x i-c-r i := by
    refine ⟨(x i-c)/(2*b),?_⟩
    have h := Int.emod_add_mul_ediv (x i-c) (2*b)
    dsimp only [r]
    linarith
  have mid (i : ℕ) (hi : i+2<k) : r i+r (i+2)=2*r (i+1) := by
    apply residue_midpoint (half _ (inT i (by omega))) (half _ (inT (i+1) (by omega)))
      (half _ (inT (i+2) hi)) (divides i) (divides (i+1)) (divides (i+2))
    dsimp [x]
    ring
  have affine := affine_of_midpoints r mid
  have flat : r 1-r 0=0 := tf _ _ (fun i hi => (affine i hi) ▸ inT i hi)
  apply fibers (r 0) (inT 0 hk) a d
  intro i hi
  refine ⟨terms i hi, ?_⟩
  change r i = r 0
  simp [affine i hi,flat]

/-- At subcritical mean degree, the expected deletion charge leaves a constant
fraction of the mass of a residue class. -/
theorem alteration {u p edgeLoss : ℝ} (hu : 0 ≤ u) (hp : 0 ≤ p)
    (h : edgeLoss ≤ u*p/32) : u*p/5 ≤ u*(p/4)-edgeLoss := by
  nlinarith [mul_nonneg hu hp]

#print axioms weighted_step
#print axioms weighted_iteration
#print axioms stage_weight
#print axioms dyadic_prices
#print axioms partition_bound
#print axioms residue_midpoint
#print axioms residue_union_free
#print axioms alteration

end Erdos142EffectiveLength
