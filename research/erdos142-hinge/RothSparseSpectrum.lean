import Mathlib

open Finset
namespace Erdos142SparseSpectrum

/-- Endpoint pairs that can occur in the row of total frequency u. -/
def pairs (A B C : Finset ℤ) (u : ℤ) : Finset (ℤ × ℤ) :=
  (A ×ˢ C).filter (fun z => u-z.1-z.2 ∈ B)

/-- Centering at the middle site makes the step frequency the endpoint difference. -/
def differences (A B C : Finset ℤ) (u : ℤ) : Finset ℤ :=
  (pairs A B C u).image (fun z => z.2-z.1)

theorem row_iff (A B C : Finset ℤ) (u t : ℤ) :
    t ∈ differences A B C u ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a+b+c=u ∧ c-a=t := by
  constructor
  · intro ht
    obtain ⟨⟨a,c⟩, h, hdiff⟩ := mem_image.mp ht
    obtain ⟨hprod,hb⟩ := mem_filter.mp h
    obtain ⟨ha,hc⟩ := mem_product.mp hprod
    exact ⟨a,ha,u-a-c,hb,c,hc,by ring,hdiff⟩
  · rintro ⟨a,ha,b,hb,c,hc,hs,hd⟩
    apply mem_image.mpr
    refine ⟨(a,c), mem_filter.mpr ⟨mem_product.mpr ⟨ha,hc⟩,?_⟩,hd⟩
    change u-a-c ∈ B
    rwa [show u-a-c=b by omega]

/-- Realize every restricted-difference graph inside one common-spectrum row. -/
theorem graph_into_row (G : Finset (ℤ × ℤ)) (S : Finset ℤ)
    (support : ∀ z ∈ G, z.1 ∈ S ∧ z.2 ∈ S ∧ -(z.1+z.2) ∈ S) :
    G.image (fun z => z.2-z.1) ⊆ differences S S S 0 := by
  intro t ht
  obtain ⟨⟨a,c⟩,h,rfl⟩ := mem_image.mp ht
  obtain ⟨ha,hc,hb⟩ := support (a,c) h
  exact (row_iff _ _ _ _ _).mpr ⟨a,ha,-(a+c),hb,c,hc,by ring,rfl⟩

/-- The squared norm of restriction at step zero, in Fourier coordinates. -/
theorem diagonal_restriction {α β : Type*} (rows : Finset α) (fiber : α → Finset β)
    (v : α → β → ℂ) {K : ℝ} (bound : ∀ u ∈ rows, ((fiber u).card : ℝ) ≤ K) :
    (∑ u ∈ rows, ‖∑ t ∈ fiber u, v u t‖^2) ≤
      K * ∑ u ∈ rows, ∑ t ∈ fiber u, ‖v u t‖^2 := by
  rw [mul_sum]
  apply sum_le_sum
  intro u hu
  have tr := norm_sum_le (fiber u) (v u)
  have cs : (∑ t ∈ fiber u, ‖v u t‖)^2 ≤ (fiber u).card * ∑ t ∈ fiber u, ‖v u t‖^2 :=
    sq_sum_le_card_mul_sum_sq
  exact (pow_le_pow_left₀ (norm_nonneg _) tr 2).trans (cs.trans
    (mul_le_mul_of_nonneg_right (bound u hu) (sum_nonneg (fun t _ => sq_nonneg _))))

theorem sharp_row {β : Type*} (S : Finset β) :
    ‖∑ _t ∈ S, (1:ℂ)‖^2 = (S.card:ℝ)*∑ _t ∈ S, ‖(1:ℂ)‖^2 := by
  simp [pow_two]

/-- Parseval on the circle for an arbitrary finite set of integer characters. -/
theorem circle_parseval (S : Finset ℤ) (a : ℤ → ℂ) :
    ‖∑ n ∈ S, a n • fourierLp (T := (1:ℝ)) 2 n‖^2 =
      ∑ n ∈ S, ‖a n‖^2 := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, (orthonormal_fourier (T := (1:ℝ))).inner_sum]
  simp [map_sum, mul_comm, RCLike.mul_conj, ← Complex.ofReal_pow]

/-- Circle L² norm of the step-zero restriction versus the sum of the row L² norms. -/
theorem circle_diagonal (rows : Finset ℤ) (fiber : ℤ → Finset ℤ)
    (v : ℤ → ℤ → ℂ) {K : ℝ} (bound : ∀ u ∈ rows, ((fiber u).card : ℝ) ≤ K) :
    ‖∑ u ∈ rows, (∑ t ∈ fiber u, v u t) • fourierLp (T := (1:ℝ)) 2 u‖^2 ≤
      K * ∑ u ∈ rows, ‖∑ t ∈ fiber u, v u t • fourierLp (T := (1:ℝ)) 2 t‖^2 := by
  simp_rw [circle_parseval]
  exact diagonal_restriction rows fiber v bound

/-- Removing rows whose total absolute coefficient sum is at most b leaves
at most K favorable frequencies, of magnitude at most the mean L each. -/
theorem coefficient_tail {α : Type*} [DecidableEq α]
    (A S : Finset α) (sub : S ⊆ A) (z : α → ℂ) {L : ℝ}
    (small : ∀ i ∈ S, ‖z i‖ ≤ L) :
    ‖∑ i ∈ A, z i‖ ≤ S.card*L + ∑ i ∈ A \ S, ‖z i‖ := by
  apply (norm_sum_le A z).trans
  rw [← sum_sdiff sub]
  have h : (∑ i ∈ S, ‖z i‖) ≤ (S.card:ℝ)*L := by simpa using sum_le_sum small
  linarith

#print axioms row_iff
#print axioms graph_into_row
#print axioms diagonal_restriction
#print axioms sharp_row
#print axioms circle_parseval
#print axioms circle_diagonal
#print axioms coefficient_tail
end Erdos142SparseSpectrum
