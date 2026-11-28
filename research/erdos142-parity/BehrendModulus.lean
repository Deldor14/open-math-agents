import LocalGrowth
import Mathlib.Combinatorics.Additive.AP.Three.Behrend

namespace ProgressionParity

open Set.IsAPOfLengthFree in
theorem roth_le_upstream (m : ℕ) : rothNumberNat m ≤ maxCard 3 m := by
  obtain ⟨T,ht,ct,ft⟩ := rothNumberNat_spec m
  let B := T.image (·+1)
  have hs : B ⊆ Finset.Icc 1 m := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have := Finset.mem_range.mp (ht hx)
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hf : Free (· ∈ B) 3 := by
    intro a d hd run
    have H := (run_iff_forall _ _ _ _).mp run
    have h0 : a∈B := by simpa using H 0 (by decide)
    have h1 : a+d∈B := by simpa using H 1 (by decide)
    have h2 : a+2*d∈B := H 2 (by decide)
    obtain ⟨x,hx,ex⟩ := Finset.mem_image.mp h0
    obtain ⟨y,hy,ey⟩ := Finset.mem_image.mp h1
    obtain ⟨z,hz,ez⟩ := Finset.mem_image.mp h2
    change x+1=a at ex
    change y+1=a+d at ey
    change z+1=a+2*d at ez
    have eq := ft hx hy hz (show x+z=y+y by omega)
    omega
  have bnd := bound_witness (by decide : 1<3) B hs hf
  have size : B.card=T.card := Finset.card_image_of_injective _ (fun a b h => by change a+1=b+1 at h;omega)
  rwa [size,ct] at bnd

open Set.IsAPOfLengthFree in
theorem explicit_increment {k m N H : ℕ} (hk : 3≤k) (hm : 0<m)
    (fits : (2*m-1)*H≤N) :
    ((m : ℝ)*Real.exp (-4*Real.sqrt (Real.log m)))*
      ((maxCard k (N+H) : ℝ)-maxCard k N) ≤ maxCard k N := by
  have mono := interval_mono (by omega : 1<k) (show N≤N+H by omega)
  have inc := relative_increment hk hm fits
  have lower : ((m : ℝ)*Real.exp (-4*Real.sqrt (Real.log m))) ≤ (maxCard 3 m : ℝ) :=
    (Behrend.roth_lower_bound (N := m)).trans (by exact_mod_cast roth_le_upstream m)
  have casted : (maxCard 3 m : ℝ)*(↑(maxCard k (N+H)-maxCard k N) : ℝ) ≤ (maxCard k N : ℝ) := by
    exact_mod_cast inc
  rw [Nat.cast_sub mono] at casted
  exact (mul_le_mul_of_nonneg_right lower (sub_nonneg.mpr (by exact_mod_cast mono))).trans casted

open Set.IsAPOfLengthFree in
theorem explicit_ratio {k m N H : ℕ} (hk : 3≤k) (hm : 0<m) (hN : 0<N)
    (fits : (2*m-1)*H≤N) :
    (maxCard k (N+H) : ℝ)/maxCard k N ≤ 1+Real.exp (4*Real.sqrt (Real.log m))/m := by
  have one := (initial_values (by omega : 1<k)).1 1 (by omega)
  have posN := interval_mono (by omega : 1<k) (show 1≤N from hN)
  rw [one] at posN
  have pos : 0<(maxCard k N : ℝ) := by exact_mod_cast (show 0<maxCard k N by omega)
  have mb : 0<(m : ℝ) := by exact_mod_cast hm
  have ev := explicit_increment hk hm fits
  let E := Real.exp (4*Real.sqrt (Real.log m))
  have ep : 0<E := Real.exp_pos _
  have inv : Real.exp (-4*Real.sqrt (Real.log m))=E⁻¹ := by
    rw [← Real.exp_neg];congr 1;ring
  rw [inv] at ev
  change (maxCard k (N+H) : ℝ)/maxCard k N ≤ 1+E/m
  rw [div_le_iff₀ pos]
  have key : (m : ℝ)*((maxCard k (N+H) : ℝ)-maxCard k N) ≤ (maxCard k N : ℝ)*E := by
    apply (div_le_iff₀ ep).mp
    simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using ev
  rw [add_mul,one_mul,div_mul_eq_mul_div]
  have diff : (maxCard k (N+H) : ℝ)-maxCard k N ≤ E*maxCard k N/m := by
    apply (le_div_iff₀ mb).mpr
    linarith only [key]
  linarith only [diff]

#print axioms explicit_ratio
end ProgressionParity
