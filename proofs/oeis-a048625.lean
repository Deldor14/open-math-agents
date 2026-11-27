import OMAStatements.S_oeis_a048625
import Mathlib

namespace Deldor14.PisotTails
open PowerSeries OMA.S_oeis_a048625

private def b : ℕ → ℤ
  | 0 => 4
  | 1 => 6
  | 2 => 9
  | n+3 => b (n+2)+b n
private theorem br (n : ℕ) : b (n+3)=b (n+2)+b n := rfl
private theorem growth (n : ℕ) : 0 < b n ∧ b n < b (n+1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n<3
    · interval_cases n <;> decide
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      have hp : 0 < b (k+1) := (ih (k+1) (by omega)).1
      have hs : 0 < b (k+3) := lt_trans (ih (k+2) (by omega)).1 (ih (k+2) (by omega)).2
      exact ⟨hs,show b (k+3) < b (k+3)+b (k+1) by omega⟩

private def det (n : ℕ) := b (n+1)^2-b n*b (n+2)
private theorem detRec (n : ℕ) : det (n+3)=det n-det (n+1) := by
  unfold det
  rw [show n+3+2=n+2+3 by omega, br (n+2),show n+3+1=n+1+3 by omega,br (n+1)]
  change (b (n+3)+b (n+1))^2-b (n+3)*((b (n+3)+b (n+1))+b (n+2))=_
  rw [br n]
  ring
private theorem estimate (n : ℕ) : -b n < 2*det n ∧ 2*det n ≤ b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h : n<3
    · interval_cases n <;> decide
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      have h₁ := ih k (by omega)
      have h₂ := ih (k+1) (by omega)
      have h₃ : b (k+1)<b (k+2) := (growth (k+1)).2
      rw [detRec,br]
      omega

private theorem identify (n : ℕ) : a n=b n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 | 1 => rfl
    | k+2 =>
      rw [a,ih (k+1) (by omega),ih k (by omega),Int.ceil_eq_iff]
      have h := estimate k
      unfold det at h
      have lo : -(b k : ℚ) < 2 * ((b (k+1):ℚ)^2 - (b k:ℚ)*b (k+2)) := by exact_mod_cast h.1
      have hi : 2 * ((b (k+1):ℚ)^2 - (b k:ℚ)*b (k+2)) ≤ b k := by exact_mod_cast h.2
      have hp : 0 < (b k : ℚ) := by exact_mod_cast (growth k).1
      constructor
      · apply (lt_sub_iff_add_lt).2
        apply (lt_div_iff₀ hp).2
        linarith only [lo]
      · apply (sub_le_iff_le_add).2
        apply (div_le_iff₀ hp).2
        linarith only [hi]

private abbrev PS := PowerSeries ℚ
private noncomputable def den (k : ℕ) : PS := 1-(2*(k:PS)+1)*X-X^3
private theorem denConst (k : ℕ) : constantCoeff (den k)=1 := by simp [den]
private theorem denUnit (k : ℕ) : IsUnit (den k) := isUnit_iff_constantCoeff.mpr (by simp [denConst])
private noncomputable def q (k : ℕ) : PS := 1+2*X*invOfUnit (den k) 1
private theorem qDen (k : ℕ) : q k*den k=den k+2*X := by
  unfold q
  rw [add_mul,one_mul,mul_assoc,invOfUnit_mul _ 1 (by simp [denConst]),mul_one]
private theorem shiftDen (k : ℕ) : q (k+1)*den (k+1)=den k := by
  rw [qDen]; simp [den]; ring
private theorem qFamily : TailFamily q := by
  intro k
  refine ⟨by simp [q],?_⟩
  apply mul_right_cancel₀ (denUnit (k+1)).ne_zero
  rw [mul_assoc,shiftDen,sub_mul,mul_assoc,shiftDen,qDen]
  simp [den,map_ofNat]
  ring

private theorem unique (r : ℕ → PS) (hr : TailFamily r) : r=q := by
  have divs (n : ℕ) : ∀ k, (X:PS)^n ∣ r k-q k := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro k
      have ru : IsUnit (r (k+1)) := isUnit_iff_constantCoeff.mpr (by rw [(hr _).1]; exact isUnit_one)
      have qu : IsUnit (q (k+1)) := isUnit_iff_constantCoeff.mpr (by rw [(qFamily _).1]; exact isUnit_one)
      apply ru.dvd_mul_right.mp
      apply qu.dvd_mul_right.mp
      have eq : (r k-q k)*r (k+1)*q (k+1)=X*(C (2*(k:ℚ)+1)+X^2)*(r (k+1)-q (k+1)) := by
        linear_combination q (k+1)*(hr k).2 - r (k+1)*(qFamily k).2
      obtain ⟨c,hc⟩ := ih (k+1)
      rw [eq,hc,pow_succ]
      exact ⟨(C (2*(k:ℚ)+1)+X^2)*c,by ring⟩
  funext k
  apply PowerSeries.ext
  intro n
  have h := (X_pow_dvd_iff.mp (divs (n+1) k)) n (by omega)
  simpa using sub_eq_zero.mp (show coeff n (r k)-coeff n (q k)=0 by simpa using h)

private noncomputable def gen : PS := mk (fun n => (b n:ℚ))
private theorem genDen : gen*den 0=4+2*X+3*X^2 := by
  have lhs : gen*den 0=gen-gen*X-gen*X^3 := by simp [den]; ring
  rw [lhs]
  apply PowerSeries.ext
  intro n
  have sh : coeff n (gen*X)=if 1≤n then coeff (n-1) gen else 0 := by
    simpa using coeff_mul_X_pow' gen 1 n
  have rhs : (4+2*X+3*X^2 : PS)= C 4+C 2*X+C 3*X^2 := by simp only [map_ofNat]
  rw [rhs]
  simp only [map_sub,map_add,sh,coeff_mul_X_pow',coeff_C_mul,coeff_C,coeff_X,coeff_X_pow,
    gen,coeff_mk]
  by_cases small : n<3
  · interval_cases n <;> norm_num [b]
  · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
    simp [br]

private theorem genQ : X^6*mk (fun n => (a n:ℚ))=
    (1/2:ℚ) • (q 0-1) - (X+X^2+X^3+2*X^4+3*X^5) := by
  simp only [identify]
  change X^6*gen=_
  apply mul_right_cancel₀ (denUnit 0).ne_zero
  rw [mul_assoc,genDen,sub_mul,Algebra.smul_mul_assoc,sub_mul,qDen,one_mul]
  have half : (1/2:ℚ) • (den 0+2*X-den 0) = (X:PS) := by
    rw [show den 0+2*X-den 0=2*X by ring]
    rw [show (2*X:PS)=(2:ℚ) • (X:PS) by rw [Algebra.smul_def]; simp [map_ofNat],smul_smul]
    norm_num
  rw [half]
  simp [den,map_ofNat]
  ring

theorem result : type_of% @OMA.S_oeis_a048625.main := by
  refine ⟨fun n hn => ?_,q,qFamily,unique,genQ⟩
  obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  simp [identify,br]

end Deldor14.PisotTails
theorem OMA.solution : type_of% @OMA.S_oeis_a048625.main := Deldor14.PisotTails.result
