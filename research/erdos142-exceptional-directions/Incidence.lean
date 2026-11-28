import Mathlib.Tactic

namespace Erdos142Incidence
open Finset
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def atTime (i : K) (p : V × V) : V := i • p.1 + p.2

/-- An affine line sampled at two distinct times gives a uniform ordered
pair when both direction and offset are uniform. -/
noncomputable def pairTimes (i j : K) (hij : i ≠ j) : (V × V) ≃ (V × V) where
  toFun p := (atTime i p, atTime j p)
  invFun xy := let u := (j-i)⁻¹ • (xy.2-xy.1)
               (u,xy.1-i • u)
  left_inv := by
    intro p
    have h : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    have recover : (j-i)⁻¹ • (atTime j p-atTime i p) = p.1 := by
      rw [show atTime j p-atTime i p = (j-i) • p.1 by unfold atTime; rw [sub_smul]; abel,
        smul_smul,inv_mul_cancel₀ h,one_smul]
    dsimp only
    rw [recover]
    unfold atTime
    simp
  right_inv := by
    intro xy
    have h : j-i ≠ 0 := sub_ne_zero.mpr hij.symm
    let u := (j-i)⁻¹ • (xy.2-xy.1)
    have diff : j • u-i • u=xy.2-xy.1 := by
      rw [←sub_smul]; dsimp [u]; rw [smul_smul,mul_inv_cancel₀ h,one_smul]
    change (i • u+(xy.1-i • u),j • u+(xy.1-i • u))=xy
    apply Prod.ext
    · dsimp; abel
    · dsimp
      calc
        _ = (j • u-i • u)+xy.1 := by abel
        _ = _ := by rw [diff]; abel

variable [Fintype V]

theorem cross (i j : K) (hij : i ≠ j) (f : V → ℝ) (center : ∑ x, f x=0) :
    (∑ p : V×V, f (atTime i p)*f (atTime j p))=0 := by
  classical
  calc
    _ = ∑ xy : V×V, f xy.1*f xy.2 := Equiv.sum_comp (pairTimes i j hij) (fun xy => f xy.1*f xy.2)
    _ = 0 := by rw [Fintype.sum_prod_type]; simp [←Finset.mul_sum,center]

theorem diagonal (i : K) (f : V → ℝ) :
    (∑ p : V×V, (f (atTime i p))^2) = (Fintype.card V : ℝ)*∑ x, (f x)^2 := by
  classical
  rw [Fintype.sum_prod_type]
  have shift (a : V) : (∑ b, f (atTime i (a,b))^2) = ∑ y, f y^2 :=
    Equiv.sum_comp (Equiv.addLeft (i • a)) (fun y => f y^2)
  simp [shift]

/-- Exact centered second moment, simultaneously valid for every subset of
sample times and every real observable of mean zero. -/
theorem line_variance (T : Finset K) (f : V → ℝ) (center : ∑ x, f x=0) :
    ∑ p : V×V, (∑ i ∈ T, f (atTime i p))^2 =
      (T.card : ℝ)*(Fintype.card V : ℝ)*∑ x, (f x)^2 := by
  classical
  have off (i : K) (hi : i∈T) :
      (∑ j∈T, ∑ p : V×V, f (atTime i p)*f (atTime j p)) =
         (Fintype.card V : ℝ)*∑ x, (f x)^2 := by
    rw [Finset.sum_eq_single i]
    · simpa [pow_two] using diagonal i f
    · intro j _ ne; exact cross i j ne.symm f center
    · simp [hi]
  simp_rw [pow_two,Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i∈T, ∑ j∈T, ∑ p : V×V, f (atTime i p)*f (atTime j p) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by rw [Finset.sum_congr rfl off]; simp [mul_assoc,pow_two]

/-- Pairs hitting one bin obey an exact variance formula. -/
theorem bin_variance [DecidableEq V] (T : Finset K) (U : Finset V) :
    let Q : ℝ := Fintype.card V
    let δ : ℝ := U.card / Q
    let X (p : V×V) : ℝ := (T.filter (fun i => atTime i p ∈ U)).card
    ∑ p : V×V, (X p - T.card*δ)^2 = (T.card:ℝ)*Q*(U.card:ℝ)*(1-δ) := by
  classical
  dsimp only
  let Q : ℝ := Fintype.card V
  have hQ : 0<Q := by dsimp [Q]; positivity
  let δ : ℝ := U.card/Q
  let ind (x : V) : ℝ := if x∈U then 1 else 0
  have sumI : ∑ x, ind x=(U.card:ℝ) := by simp [ind]
  have sqI (x : V) : ind x^2=ind x := by simp [ind]
  have center : (∑ x, (ind x-δ))=0 := by
    rw [Finset.sum_sub_distrib,sumI]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change (U.card:ℝ)-Q*δ=0
    dsimp [δ]; field_simp; ring
  have scaled : Q*δ=(U.card:ℝ) := by dsimp [δ]; field_simp
  have moment : (∑ x, (ind x-δ)^2)=(U.card:ℝ)*(1-δ) := by
    simp_rw [sub_sq,sqI,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sumI]
    rw [← Finset.sum_mul,← Finset.mul_sum,sumI]
    change (U.card:ℝ)-2*U.card*δ+Q*δ^2=_
    calc
      _ = (U.card:ℝ)-2*U.card*δ+(Q*δ)*δ := by ring
      _ = _ := by rw [scaled]; ring
  have count (p : V×V) : (∑ i∈T, (ind (atTime i p)-δ)) =
      ((T.filter fun i => atTime i p∈U).card:ℝ) - T.card*δ := by
    rw [Finset.sum_sub_distrib]
    simp [ind]
  have exact := line_variance T (fun x => ind x-δ) center
  simp_rw [count] at exact
  rw [moment] at exact
  convert exact using 1; ring

omit [Fintype V] in
/-- If a translating box and its orbit shifts are disjoint, a thick set
of offsets around a single good shift yields a full row of bad pairs. -/
theorem shadow_size [DecidableEq V] (T : Finset K) (B Row : Finset V) (a b : V)
    (separated : ∀ i∈T, ∀ j∈T, i≠j → ∀ u∈B, ∀ v∈B, i • a-j • a ≠ v-u)
    (stays : ∀ i∈T, ∀ u∈B, b+i • a+u ∈ Row) : T.card*B.card ≤ Row.card := by
  classical
  let f (z : K×V) := b+z.1 • a+z.2
  have inj : Set.InjOn f ↑(T ×ˢ B) := by
    intro p hp r hr eq
    have pIn := Finset.mem_product.mp hp
    have rIn := Finset.mem_product.mp hr
    change b+p.1 • a+p.2=b+r.1 • a+r.2 at eq
    have diff : p.1 • a-r.1 • a = r.2-p.2 := by
      calc
        _ = (b+p.1 • a+p.2)-(b+r.1 • a+r.2)+(r.2-p.2) := by abel
        _ = _ := by rw [eq]; simp
    have one : p.1=r.1 := by
      by_contra neq
      exact separated _ pIn.1 _ rIn.1 neq _ pIn.2 _ rIn.2 diff
    rw [one] at eq
    exact Prod.ext one (add_left_cancel eq)
  have sub : (T ×ˢ B).image f ⊆ Row := by
    intro r hr
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hr
    have zz := Finset.mem_product.mp hz
    exact stays z.1 zz.1 z.2 zz.2
  have bound := Finset.card_le_card sub
  simpa only [Finset.card_image_of_injOn inj,Finset.card_product] using bound

#print axioms line_variance
#print axioms bin_variance
#print axioms shadow_size
end Erdos142Incidence
