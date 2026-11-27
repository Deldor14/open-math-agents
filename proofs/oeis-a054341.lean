import OMAStatements.S_oeis_a054341
import Mathlib

namespace Deldor14.CentralConvolution
open OMA.S_oeis_a054341 PowerSeries

private theorem relation : doubleCatalan=1+X^2*doubleCatalan^2 := by
  have h := congrArg (fun f : PowerSeries ℕ => expand 2 (by decide) (map (Nat.castRingHom ℚ) f))
    (catalanSeries_sq_mul_X_add_one).symm
  change doubleCatalan = _ at h
  simpa only [map_add,map_one,map_mul,map_pow,map_X,expand_X,add_comm,mul_comm,doubleCatalan] using h
private theorem first (n : ℕ) : 2*a (n+1)-5*a n= -coeff n doubleCatalan := by
  let d := doubleCatalan
  let den : PowerSeries ℚ := 1-2*X*d
  have h : d*(2-5*X)=(2-X*d)*den := by
    have r : d=1+X^2*d^2 := relation
    dsimp [den]
    linear_combination 2*r
  have eq : C 2*series-(C 5*series)*X=C 2-d*X := by
    change C 2*(d*den⁻¹)-(C 5*(d*den⁻¹))*X=C 2-d*X
    calc
      _ = (d*(2-5*X))*den⁻¹ := by simp only [map_ofNat];ring
      _ = _ := by rw [h,mul_assoc,PowerSeries.mul_inv_cancel den (by simp [den]),mul_one];simp only [map_ofNat];ring
  have c := congrArg (coeff (n+1)) eq
  simpa [coeff_succ_mul_X,coeff_C_mul,a,d] using c
private theorem cat (n : ℕ) : ((n:ℚ)+2)*catalan (n+1)=2*(2*n+1)*(catalan n:ℚ) := by
  have h := congrArg (fun z : ℕ => (z:ℚ)) (Nat.succ_mul_centralBinom_succ n)
  rw [← succ_mul_catalan_eq_centralBinom,← succ_mul_catalan_eq_centralBinom] at h
  push_cast at h
  apply mul_left_cancel₀ (show (n:ℚ)+1≠0 by positivity)
  linear_combination h
private theorem gap (t : ℕ) :
    ((t:ℚ)+4)*coeff (t+2) doubleCatalan=4*(t+1)*coeff t doubleCatalan := by
  rcases Nat.even_or_odd t with ⟨k,e⟩|⟨k,e⟩
  · rw [show t=2*k by omega,show 2*k+2=2*(k+1) by omega]
    simp only [doubleCatalan,coeff_expand_mul,coeff_map,catalanSeries_coeff]
    push_cast
    linear_combination 2*cat k
  · have h₁ : ¬2 ∣ t := by omega
    have h₂ : ¬2 ∣ t+2 := by omega
    simp [doubleCatalan,coeff_expand,h₁,h₂]
theorem result : type_of% @OMA.S_oeis_a054341.main := by
  intro t
  linear_combination ((t:ℚ)+4)*first (t+2) - 4*((t:ℚ)+1)*first t - gap t
end Deldor14.CentralConvolution
theorem OMA.solution : type_of% @OMA.S_oeis_a054341.main := Deldor14.CentralConvolution.result
