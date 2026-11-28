import BernsteinInteger

/-! Stability of dyadic finite differences under integer rounding and
the simultaneous range for a positive atom in a mixture of powers. -/

namespace Erdos142Mixture
open Erdos142Bernstein Filter

theorem diff_sub (u v : ℕ → ℝ) (h k : ℕ) :
    diff (fun j => u j-v j) h k = diff u h k-diff v h k := by
  induction h generalizing k with
  | zero => rfl
  | succ h ih => simp only [diff,ih]; ring

theorem atom (c y : ℝ) (h k : ℕ) :
    diff (fun j => c*y^j) h k = c*y^k*(1-y)^h := by
  induction h generalizing k with
  | zero => simp [diff]
  | succ h ih => rw [diff,ih,ih,pow_succ y k,pow_succ (1-y) h]; ring

/-- A pointwise perturbation of size b·2⁻ᵏ contributes at most b·2⁻ᵏ(3/2)ʰ. -/
theorem error_bound (e : ℕ → ℝ) (b : ℝ)
    (err : ∀ k : ℕ, |e k| ≤ b*(1/2:ℝ)^k) (h k : ℕ) :
    |diff e h k| ≤ b*(1/2:ℝ)^k*(3/2:ℝ)^h := by
  induction h generalizing k with
  | zero => simpa [diff] using err k
  | succ h ih =>
    calc
      |diff e (h+1) k| ≤ |diff e h k|+|diff e h (k+1)| := abs_sub _ _
      _ ≤ _ := add_le_add (ih k) (ih (k+1))
      _ = _ := by rw [pow_succ (1/2:ℝ) k,pow_succ (3/2:ℝ) h];ring

/-- The lower error bound for rounding upward improves the usual absolute
error bound; subtracting the exact midpoint leaves a symmetric perturbation. -/
theorem ceiling_error (u v : ℕ → ℝ)
    (err : ∀ k : ℕ, 0 ≤ u k-v k ∧ u k-v k ≤ (1/2:ℝ)^k) (h k : ℕ) :
    (1/2:ℝ)*(1/2:ℝ)^k*((1/2:ℝ)^h-(3/2:ℝ)^h) ≤ diff u h k-diff v h k := by
  let e := fun j => (u j-v j)-(1/2:ℝ)*(1/2:ℝ)^j
  have he (j : ℕ) : |e j| ≤ (1/2:ℝ)*(1/2:ℝ)^j := by
    dsimp [e]
    exact abs_le.mpr ⟨by linarith [(err j).1],by linarith [(err j).2]⟩
  have lo := (abs_le.mp (error_bound e (1/2) he h k)).1
  dsimp only [e] at lo
  rw [diff_sub,diff_sub,atom,show (1:ℝ)-1/2=1/2 by norm_num] at lo
  linarith

/-- Pointwise Bernstein powers in the mixture provide a lower bound on the
unrounded differences. This finite conclusion includes equality in the
comparison with half of the usual absolute error. -/
theorem positive_of_atom (u v : ℕ → ℝ) {c y : ℝ}
    (err : ∀ k : ℕ, 0 ≤ u k-v k ∧ u k-v k ≤ (1/2:ℝ)^k)
    (signal : ∀ h k, c*y^k*(1-y)^h ≤ diff v h k) (h k : ℕ)
    (bound : (1/2:ℝ)*(1/2:ℝ)^k*(3/2:ℝ)^h ≤ c*y^k*(1-y)^h) :
    0 < diff u h k := by
  have lo := ceiling_error u v err h k
  have extra : 0 < (1/2:ℝ)*(1/2:ℝ)^k*(1/2:ℝ)^h := by positivity
  linarith only [lo,extra,bound,signal h k]

/-- For h≤αk, test only the worst permitted exponent. -/
theorem uniform_finite {u v : ℕ → ℝ} {c y α : ℝ}
    (hc : 0 ≤ c) (hy : 0 < y) (hy1 : y < 1)
    (err : ∀ k : ℕ, 0 ≤ u k-v k ∧ u k-v k ≤ (1/2:ℝ)^k)
    (signal : ∀ h k, c*y^k*(1-y)^h ≤ diff v h k) (h k : ℕ)
    (order : (h:ℝ) ≤ α*k) (margin : 1/2 ≤ c*(2*y*((1-y)/(3/2))^α)^k) :
    0 < diff u h k := by
  let b : ℝ := (1-y)/(3/2)
  have bpos : 0 < b := by dsimp [b]; positivity
  have ble : b ≤ 1 := by dsimp [b]; linarith
  have powle := Real.rpow_le_rpow_of_exponent_ge bpos ble order
  rw [Real.rpow_natCast,Real.rpow_mul_natCast bpos.le] at powle
  have hcmp := mul_le_mul_of_nonneg_left powle
    (show 0 ≤ c*(2*y)^k by positivity)
  change 1/2 ≤ c*(2*y*b^α)^k at margin
  rw [mul_pow,mul_pow,←mul_assoc] at margin
  have ratio : 1/2 ≤ c*(2*y)^k*b^h := by
    apply le_trans _ hcmp
    simpa only [mul_pow,mul_assoc] using margin
  have scaled := mul_le_mul_of_nonneg_right ratio
    (show 0 ≤ (1/2:ℝ)^k*(3/2:ℝ)^h by positivity)
  apply positive_of_atom u v err signal h k
  calc
    (1/2:ℝ)*(1/2:ℝ)^k*(3/2:ℝ)^h = (1/2:ℝ)*((1/2:ℝ)^k*(3/2:ℝ)^h) := by ring
    _ ≤ _ := scaled
    _ = c*y^k*(1-y)^h := by
      unfold b
      rw [show c*(2*y)^k*((1-y)/(3/2))^h*((1/2:ℝ)^k*(3/2:ℝ)^h) =
        c*((2*y)*(1/2))^k*(((1-y)/(3/2))*(3/2))^h by simp only [mul_pow]; ring]
      rw [show 2*y*(1/2)=y by ring,show ((1-y)/(3/2))*(3/2)=1-y by ring]

/-- The same lower bound holds simultaneously for all large k and all h≤αk. -/
theorem eventually_positive {u v : ℕ → ℝ} {c y α : ℝ}
    (hc : 0 < c) (hy : 0 < y) (hy1 : y < 1)
    (err : ∀ k : ℕ, 0 ≤ u k-v k ∧ u k-v k ≤ (1/2:ℝ)^k)
    (signal : ∀ h k, c*y^k*(1-y)^h ≤ diff v h k)
    (growth : 1 < 2*y*((1-y)/(3/2))^α) :
    ∀ᶠ k : ℕ in atTop, ∀ h : ℕ, (h:ℝ) ≤ α*k → 0 < diff u h k := by
  have tends := (tendsto_pow_atTop_atTop_of_one_lt growth).const_mul_atTop hc
  filter_upwards [(tendsto_atTop.mp tends) (1/2:ℝ)] with k hk
  intro h hh
  exact uniform_finite hc.le hy hy1 err signal h k hh hk

/-- The integer ceiling of the unscaled count, normalized back to a density. -/
noncomputable def rounded (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  (⌈(2:ℝ)^k*v k⌉ : ℤ)*(1/2:ℝ)^k

theorem rounded_error (v : ℕ → ℝ) (k : ℕ) :
    0 ≤ rounded v k-v k ∧ rounded v k-v k ≤ (1/2:ℝ)^k := by
  have id : (2:ℝ)^k*(1/2:ℝ)^k = 1 := by rw [←mul_pow]; norm_num
  have e : rounded v k-v k =
      ((⌈(2:ℝ)^k*v k⌉ : ℤ)-(2:ℝ)^k*v k)*(1/2:ℝ)^k := by
    unfold rounded
    rw [sub_mul, mul_right_comm ((2:ℝ)^k), id, one_mul]
  rw [e]
  have lo := Int.le_ceil ((2:ℝ)^k*v k)
  have hi := Int.ceil_lt_add_one ((2:ℝ)^k*v k)
  constructor
  · exact mul_nonneg (sub_nonneg.mpr lo) (by positivity)
  · simpa using mul_le_mul_of_nonneg_right
      (show ((⌈(2:ℝ)^k*v k⌉:ℤ):ℝ)-(2:ℝ)^k*v k ≤ 1 by linarith) (by positivity : 0 ≤ (1/2:ℝ)^k)

/-- If the remaining mixture has nonnegative differences, the atom gives the
required signal, including for mixtures whose remaining measure is not atomic. -/
theorem signal_of_remainder (v : ℕ → ℝ) (c y : ℝ)
    (rest : ∀ h k, 0 ≤ diff (fun n => v n-c*y^n) h k) (h k : ℕ) :
    c*y^k*(1-y)^h ≤ diff v h k := by
  have hs := rest h k
  rw [diff_sub,atom] at hs
  linarith

/-- The atom location 1/(1+α) maximizes y(1-y)^α. -/
theorem maximizer {α y : ℝ} (hα : 0 < α) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    y*(1-y)^α ≤ (1/(1+α))*(1-1/(1+α))^α := by
  let z := 1/(1+α)
  let w := α/(1+α)
  have hp : 0 < 1+α := by linarith
  have hz : 0 < z := by dsimp [z]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have split : z+w=1 := by dsimp [z,w]; field_simp
  have vpos : 0 ≤ 1-y := by linarith
  have yp := div_nonneg hy hz.le
  have vp := div_nonneg vpos hw.le
  have gm := Real.geom_mean_le_arith_mean2_weighted hz.le hw.le yp vp split
  have unit : z*(y/z)+w*((1-y)/w)=1 := by field_simp; ring
  rw [unit] at gm
  have power := Real.rpow_le_rpow (mul_nonneg (Real.rpow_nonneg yp _) (Real.rpow_nonneg vp _))
    gm hp.le
  rw [Real.one_rpow,Real.mul_rpow (Real.rpow_nonneg yp _) (Real.rpow_nonneg vp _),
    ←Real.rpow_mul yp,←Real.rpow_mul vp,show z*(1+α)=1 by dsimp [z];field_simp,
    show w*(1+α)=α by dsimp [w];field_simp,Real.rpow_one,Real.div_rpow vpos hw.le] at power
  have clear := (div_le_one (mul_pos hz (Real.rpow_pos_of_pos hw α))).mp
    (show y*(1-y)^α / (z*w^α) ≤ 1 by simpa only [div_mul_div_comm] using power)
  change y*(1-y)^α ≤ z*(1-z)^α
  rwa [show 1-z=w by linarith]

/-- Substitution of y=1/(1+α) in the signal-to-error base. -/
theorem optimized_base {α : ℝ} (hα : 0 < α) :
    2*(1/(1+α))*((1-1/(1+α))/(3/2))^α =
      2*α^α/((1+α)^(1+α)*(3/2)^α) := by
  have pos : 0 < 1+α := by linarith
  rw [show (1-1/(1+α))/(3/2)=α/((1+α)*(3/2)) by field_simp; ring,
    Real.div_rpow hα.le (by positivity) α,Real.mul_rpow pos.le (by norm_num),
    Real.rpow_add pos 1 α,Real.rpow_one]
  field_simp

/-- Strictly below the entropy threshold one positive atom suffices at all
large k for every order h≤αk. No distribution assumption on ceiling errors
is required. -/
theorem optimized_positive (v : ℕ → ℝ) {α c : ℝ} (hα : 0 < α) (hc : 0 < c)
    (threshold : (1+α)^(1+α)*(3/2)^α < 2*α^α)
    (rest : ∀ h k, 0 ≤ diff (fun n => v n-c*(1/(1+α))^n) h k) :
    ∀ᶠ k : ℕ in atTop, ∀ h : ℕ, (h:ℝ) ≤ α*k → 0 < diff (rounded v) h k := by
  have pos : 0 < 1+α := by linarith
  apply eventually_positive hc (by positivity : 0 < 1/(1+α))
    ((div_lt_one pos).mpr (by linarith)) (rounded_error v) (signal_of_remainder _ _ _ rest)
  rw [optimized_base hα]
  exact (one_lt_div (by positivity)).mpr threshold

/-- At equality the one-sided bound gives strict positivity even at the
critical slope when the atom has mass at least one half. -/
theorem critical_positive (v : ℕ → ℝ) {α c : ℝ} (hα : 0 < α) (hc : 1/2 ≤ c)
    (threshold : (1+α)^(1+α)*(3/2)^α = 2*α^α)
    (rest : ∀ h k, 0 ≤ diff (fun n => v n-c*(1/(1+α))^n) h k)
    (h k : ℕ) (order : (h:ℝ) ≤ α*k) : 0 < diff (rounded v) h k := by
  have pos : 0 < 1+α := by linarith
  apply uniform_finite (by linarith : 0 ≤ c) (by positivity : 0 < 1/(1+α))
    ((div_lt_one pos).mpr (by linarith)) (rounded_error v) (signal_of_remainder _ _ _ rest)
    h k order
  rw [optimized_base hα,←threshold,div_self (by positivity)]
  simpa using hc

#print axioms maximizer
#print axioms optimized_positive
#print axioms critical_positive
#print axioms error_bound
#print axioms ceiling_error
#print axioms uniform_finite
#print axioms eventually_positive
end Erdos142Mixture
