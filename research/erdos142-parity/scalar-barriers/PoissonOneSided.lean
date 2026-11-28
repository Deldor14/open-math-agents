import Mathlib

/-! A Poisson transform of any acceptance rule in [0,1] has a single
direction on the log-rate axis in which its values stay within a fixed
factor. All sums are over the actual infinite Poisson law. -/

namespace Erdos142PoissonSlope
open Real

noncomputable def weight (v : ℕ → ℝ) (μ : ℝ) (n : ℕ) : ℝ :=
  v n * (exp (-μ) * (μ^n/(n.factorial:ℝ)))

noncomputable def profile (v : ℕ → ℝ) (μ : ℝ) := ∑' n, weight v μ n
noncomputable def slope (v : ℕ → ℝ) (μ : ℝ) := ∑' n : ℕ, weight v μ n*((n:ℝ)-μ)

private theorem nonnegative (v : ℕ → ℝ) (lo : ∀ n, 0≤v n) {μ : ℝ} (hm : 0≤μ) (n : ℕ) :
    0≤weight v μ n := by unfold weight; positivity [lo n]

private theorem mass_summable (v : ℕ → ℝ) (lo : ∀ n, 0≤v n) (hi : ∀ n, v n≤1)
    {μ : ℝ} (hm : 0≤μ) : Summable (weight v μ) := by
  apply ((Real.summable_pow_div_factorial μ).mul_left (exp (-μ))).of_nonneg_of_le
    (nonnegative v lo hm)
  intro n
  exact mul_le_of_le_one_left (by positivity) (hi n)

private theorem slope_summable (v : ℕ → ℝ) (lo : ∀ n, 0≤v n) (hi : ∀ n, v n≤1)
    {μ : ℝ} (hm : 0≤μ) : Summable (fun n : ℕ => weight v μ n*((n:ℝ)-μ)) := by
  have first : Summable (fun n : ℕ => weight v μ n * (n:ℝ)) := by
    apply ((Real.summable_pow_div_factorial (μ*exp 1)).mul_left (exp (-μ))).of_nonneg_of_le
      (fun n => mul_nonneg (nonnegative v lo hm n) (Nat.cast_nonneg n))
    intro n
    have wn : weight v μ n ≤ exp (-μ)*(μ^n/(n.factorial:ℝ)) :=
      mul_le_of_le_one_left (by positivity) (hi n)
    have nb : (n:ℝ) ≤ (exp 1)^n := by
      rw [←exp_nat_mul, mul_one]
      linarith only [add_one_le_exp (n:ℝ)]
    have b := mul_le_mul wn nb (Nat.cast_nonneg n) (by positivity)
    rw [mul_pow]
    exact b.trans_eq (by ring)
  apply (first.sub ((mass_summable v lo hi hm).mul_right μ)).congr
  intro n; ring

private theorem tilt (v : ℕ → ℝ) (μ t : ℝ) (n : ℕ) :
    weight v (μ*exp t) n =
      exp (-μ*(exp t-1-t))*(weight v μ n*exp (((n:ℝ)-μ)*t)) := by
  unfold weight
  rw [mul_pow,←exp_nat_mul]
  calc _ = (v n*(μ^n/(n.factorial:ℝ)))*exp (-(μ*exp t)+(n:ℝ)*t) := by
              rw [exp_add]; ring
       _ = _ := by
         rw [show -(μ*exp t)+(n:ℝ)*t=(-μ*(exp t-1-t))+(-μ)+(((n:ℝ)-μ)*t) by ring,
           exp_add,exp_add]
         ring

/-- Unnormalized Poisson tangent. No division by the mass of the profile
is needed, so the zero profile is included. -/
theorem tangent (v : ℕ → ℝ) (lo : ∀ n, 0≤v n) (hi : ∀ n, v n≤1)
    {μ t : ℝ} (hm : 0≤μ) :
    exp (-μ*(exp t-1-t))*(profile v μ+slope v μ*t) ≤ profile v (μ*exp t) := by
  let c := exp (-μ*(exp t-1-t))
  have a := mass_summable v lo hi hm
  have b := (slope_summable v lo hi hm).mul_right t
  have lin := (a.add b).mul_left c
  have right := mass_summable v lo hi (mul_nonneg hm (exp_pos t).le)
  have per (n : ℕ) : c*(weight v μ n+(weight v μ n*((n:ℝ)-μ))*t) ≤ weight v (μ*exp t) n := by
    rw [tilt]
    apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
    have e := mul_le_mul_of_nonneg_left (add_one_le_exp (((n:ℝ)-μ)*t)) (nonnegative v lo hm n)
    linarith only [e]
  have h := lin.tsum_le_tsum per right
  rw [tsum_mul_left,a.tsum_add b,tsum_mul_right] at h
  exact h

theorem one_sided (v : ℕ → ℝ) (lo : ∀ n, 0≤v n) (hi : ∀ n, v n≤1)
    {μ : ℝ} (hm : 0≤μ) :
    ∃ sign : ℝ, (sign=1 ∨ sign= -1) ∧ ∀ z : ℝ, 0≤z → z≤1 → μ*z^2≤1 →
      exp (-1)*profile v μ ≤ profile v (μ*exp (sign*z)) := by
  let sign : ℝ := if 0 ≤ slope v μ then 1 else -1
  have choice : sign=1 ∨ sign= -1 := by dsimp [sign]; split <;> simp
  refine ⟨sign,choice,?_⟩
  intro z hz small cap
  have up : 0 ≤ slope v μ*(sign*z) := by
    dsimp [sign]; split <;> rename_i side
    · simp [mul_nonneg side hz]
    · simp; exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge side) hz
  have absval : |sign*z|=z := by rcases choice with h | h <;> simp [h,abs_of_nonneg hz]
  have sq : (sign*z)^2=z^2 := by rcases choice with h | h <;> simp [h]
  have bound := (le_abs_self _).trans (abs_exp_sub_one_sub_id_le (absval.trans_le small))
  rw [sq] at bound
  have scale : exp (-1) ≤ exp (-μ*(exp (sign*z)-1-sign*z)) := by
    apply exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left bound hm,cap]
  have Fpos : 0≤profile v μ := tsum_nonneg (nonnegative v lo hm)
  have gain := mul_le_mul scale (le_add_of_nonneg_right up) Fpos (exp_pos _).le
  exact gain.trans (tangent v lo hi hm)

#print axioms tangent
#print axioms one_sided
end Erdos142PoissonSlope
