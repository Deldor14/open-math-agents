import OMAStatements.S_oeis_a020964
import Mathlib

open OMA.S_oeis_a020964 PowerSeries
namespace Deldor14.Silver

private noncomputable abbrev u : ℝ := 1+Real.sqrt 2
private noncomputable abbrev v : ℝ := 1-Real.sqrt 2
private theorem sq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
private theorem low : (7:ℝ)/5 < Real.sqrt 2 := by nlinarith [sq,Real.sqrt_nonneg 2]
private theorem high : Real.sqrt 2 < (3:ℝ)/2 := by nlinarith [sq,Real.sqrt_nonneg 2]
private theorem upos : 0 < u := by dsimp [u]; positivity
private theorem uone : 1 ≤ u := by dsimp [u]; linarith [low]
private noncomputable def term (n k : ℕ) : ℤ := ⌊3*u^((n:ℤ)-((k:ℤ)+1))⌋
private noncomputable def g (n : ℕ) : ℤ := ⌊3*u^n⌋
private def trace : ℕ → ℤ
  | 0 => 6
  | 1 => 6
  | n+2 => 2*trace (n+1)+trace n

private theorem vanishes (n k : ℕ) (h : n<k) : term n k=0 := by
  obtain ⟨d,rfl⟩ : ∃ d,k=n+1+d := ⟨k-(n+1),by omega⟩
  have hp : 3 < u^(d+2) := by
    have e : 3 < u^2 := by dsimp [u]; nlinarith [sq,low]
    exact e.trans_le (pow_le_pow_right₀ uone (by omega))
  unfold term
  rw [show (n:ℤ)-(((n+1+d:ℕ):ℤ)+1) = -((d+2:ℕ):ℤ) by omega,zpow_neg,zpow_natCast]
  apply Int.floor_eq_iff.mpr
  push_cast
  rw [← div_eq_mul_inv]
  constructor
  · positivity
  · exact (div_lt_iff₀ (by positivity : 0 < u^(d+2))).mpr (by linarith)

private theorem initial : a 0=1 := by
  change (∑' k,term 0 k)=1
  rw [tsum_eq_single 0 (fun k hk => vanishes 0 k (by omega))]
  unfold term
  norm_num only [Nat.cast_zero,zero_add,zero_sub,zpow_neg_one]
  rw [← div_eq_mul_inv,Int.floor_eq_iff]
  norm_num only [Int.cast_one]
  constructor
  · apply (le_div_iff₀ upos).mpr; dsimp [u]; linarith [high]
  · apply (div_lt_iff₀ upos).mpr; dsimp [u]; linarith [low]

private theorem next (n : ℕ) : a (n+1)=a n+g n := by
  have s : Summable (term (n+1)) := summable_of_ne_finset_zero (s := Finset.range (n+2))
    (fun k hk => vanishes _ _ (by simp only [Finset.mem_range,not_lt] at hk; omega))
  change (∑' k,term (n+1) k) = (∑' k,term n k) + g n
  rw [s.tsum_eq_zero_add,add_comm]
  congr 1
  · apply tsum_congr
    intro k
    unfold term
    congr 2
    push_cast <;> ring
  · unfold term g
    simp

private theorem trace_formula (n : ℕ) : (trace n:ℝ)=3*(u^n+v^n) := by
  have qu : u^2=2*u+1 := by dsimp [u]; nlinarith [sq]
  have qv : v^2=2*v+1 := by dsimp [v]; nlinarith [sq]
  induction n using Nat.twoStepInduction with
  | zero => norm_num [trace]
  | one => norm_num [trace,u,v] <;> ring
  | more n e f =>
    simp only [trace,Int.cast_add,Int.cast_mul,Int.cast_ofNat,e,f,pow_add,pow_one,qu,qv] <;> ring

private theorem small (n : ℕ) (h : 2≤n) : 3*(Real.sqrt 2-1)^n < 1 := by
  have lo : 0≤Real.sqrt 2-1 := by linarith [low]
  have hi : Real.sqrt 2-1≤1 := by linarith [high]
  have hpow := pow_le_pow_of_le_one lo hi h
  nlinarith [sq,hpow,low]

private theorem floor_formula (n : ℕ) (h : 2≤n) :
    g n=trace n-(if n%2=0 then 1 else 0) := by
  have pos : 0 < (Real.sqrt 2-1)^n := pow_pos (by linarith [low]) _
  have bound := small n h
  have e := trace_formula n
  have neg : v = -(Real.sqrt 2-1) := by dsimp [v]; ring
  unfold g
  rw [Int.floor_eq_iff]
  by_cases even : n%2=0
  · have he : Even n := Nat.even_iff.mpr even
    rw [neg,he.neg_pow] at e
    simp [even]
    constructor <;> linarith
  · have ho : Odd n := Nat.odd_iff.mpr (by omega)
    rw [neg,ho.neg_pow] at e
    simp [even]
    constructor <;> linarith

private theorem recurrence (n : ℕ) (hn : 6<n) :
    a n=3*a (n-1)-4*a (n-3)+a (n-4)+a (n-5) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+7 := ⟨n-7,by omega⟩
  change a (k+7)=3*a (k+6)-4*a (k+4)+a (k+3)+a (k+2)
  have ef (j : ℕ) : g (k+2+j)=trace (k+2+j)-(if (k+2+j)%2=0 then 1 else 0) :=
    floor_formula _ (by omega)
  have h0 := ef 0
  have h1 := ef 1
  have h2 := ef 2
  have h3 := ef 3
  have h4 := ef 4
  have t0 : trace (k+4)=2*trace (k+3)+trace (k+2) := rfl
  have t1 : trace (k+5)=2*trace (k+4)+trace (k+3) := rfl
  have t2 : trace (k+6)=2*trace (k+5)+trace (k+4) := rfl
  have p := next (k+2)
  have q := next (k+3)
  have r := next (k+4)
  have s := next (k+5)
  have t := next (k+6)
  change a (k+3)=a (k+2)+g (k+2) at p
  change a (k+4)=a (k+3)+g (k+3) at q
  change a (k+5)=a (k+4)+g (k+4) at r
  change a (k+6)=a (k+5)+g (k+5) at s
  change a (k+7)=a (k+6)+g (k+6) at t
  by_cases parity : k%2=0
  · simp only [if_pos (by omega : (k+2+0)%2=0),
      if_neg (by omega : (k+2+1)%2≠0),
      if_pos (by omega : (k+2+2)%2=0),
      if_neg (by omega : (k+2+3)%2≠0),
      if_pos (by omega : (k+2+4)%2=0)] at h0 h1 h2 h3 h4
    change g (k+2)=trace (k+2)-_ at h0
    change g (k+3)=trace (k+3)-_ at h1
    change g (k+4)=trace (k+4)-_ at h2
    change g (k+5)=trace (k+5)-_ at h3
    change g (k+6)=trace (k+6)-_ at h4
    linarith only [h0,h1,h2,h3,h4,t0,t1,t2,p,q,r,s,t]
  · simp only [if_neg (by omega : (k+2+0)%2≠0),
      if_pos (by omega : (k+2+1)%2=0),
      if_neg (by omega : (k+2+2)%2≠0),
      if_pos (by omega : (k+2+3)%2=0),
      if_neg (by omega : (k+2+4)%2≠0)] at h0 h1 h2 h3 h4
    change g (k+2)=trace (k+2)-_ at h0
    change g (k+3)=trace (k+3)-_ at h1
    change g (k+4)=trace (k+4)-_ at h2
    change g (k+5)=trace (k+5)-_ at h3
    change g (k+6)=trace (k+6)-_ at h4
    linarith only [h0,h1,h2,h3,h4,t0,t1,t2,p,q,r,s,t]

private theorem bases : a 0=1 ∧ a 1=4 ∧ a 2=11 ∧ a 3=28 ∧ a 4=70 ∧ a 5=171 ∧ a 6=417 := by
  have g0 : g 0=3 := by norm_num [g]
  have g1 : g 1=7 := by
    rw [g,Int.floor_eq_iff]; norm_num; dsimp [u]; constructor <;> linarith [low,high]
  have g2 := floor_formula 2 (by decide)
  have g3 := floor_formula 3 (by decide)
  have g4 := floor_formula 4 (by decide)
  have g5 := floor_formula 5 (by decide)
  norm_num [trace] at g2 g3 g4 g5
  have t0 := next 0
  have t1 := next 1
  have t2 := next 2
  have t3 := next 3
  have t4 := next 4
  have t5 := next 5
  have a0 := initial
  norm_num at t0 t1 t2 t3 t4 t5
  exact ⟨a0,by omega,by omega,by omega,by omega,by omega,by omega⟩

private theorem generating : mk a =
    invOfUnit (1-C 3*X+C 4*X^3-X^4-X^5) 1 * (1+X-X^2-X^3+X^4+X^6) := by
  let den : PowerSeries ℤ := 1-C 3*X+C 4*X^3-X^4-X^5
  let num : PowerSeries ℤ := 1+X-X^2-X^3+X^4+X^6
  have mul : den*mk a=num := by
    have factor : den*mk a=mk a-(C 3*mk a)*X+(C 4*mk a)*X^3-mk a*X^4-mk a*X^5 := by
      dsimp [den]; ring
    rw [factor]
    apply PowerSeries.ext
    intro n
    have shift (f : PowerSeries ℤ) : coeff n (f*X) = if 1≤n then coeff (n-1) f else 0 := by
      simpa only [pow_one] using coeff_mul_X_pow' f 1 n
    simp only [num,map_add,map_sub,shift,coeff_mul_X_pow',coeff_C_mul,coeff_mk,
      coeff_one,coeff_X,coeff_X_pow]
    by_cases h : n≤6
    · obtain ⟨h0,h1,h2,h3,h4,h5,h6⟩ := bases
      interval_cases n <;> norm_num [h0,h1,h2,h3,h4,h5,h6]
    · simp only [if_pos (by omega : 1≤n),if_pos (by omega : 3≤n),if_pos (by omega : 4≤n),
        if_pos (by omega : 5≤n),if_neg (by omega : n≠0),if_neg (by omega : n≠1),
        if_neg (by omega : n≠2),if_neg (by omega : n≠3),if_neg (by omega : n≠4),
        if_neg (by omega : n≠6)]
      linarith [recurrence n (by omega)]
  change mk a = invOfUnit den 1 * num
  rw [← mul,← mul_assoc,invOfUnit_mul den 1 (by simp [den]) ,one_mul]

end Deldor14.Silver
theorem OMA.solution : type_of% @OMA.S_oeis_a020964.main :=
  ⟨Deldor14.Silver.recurrence,Deldor14.Silver.generating⟩
