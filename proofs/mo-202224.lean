import OMAStatements.S_mo_202224
import Mathlib

/-! Apply Kronecker's theorem in the number field ℚ(α). Each complex
embedding takes its distinguished generator to a root of its minimal polynomial. -/
open Polynomial IntermediateField
open scoped IntermediateField

theorem OMA.solution : type_of% @OMA.S_mo_202224.main := by
  intro a ha roots
  let K:=ℚ⟮a⟯
  let x : K := AdjoinSimple.gen ℚ a
  letI : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional (ha.tower_top (A:=ℚ))
  letI : NumberField K := {}
  have hx : IsIntegral ℤ x := (isIntegral_algebraMap_iff (algebraMap K ℂ).injective).mp (show IsIntegral ℤ (algebraMap K ℂ x) from ha)
  have norm (φ : K →+* ℂ) : ‖φ x‖=1 := by
    apply roots
    let f : K →ₐ[ℚ] ℂ := (RingHom.equivRatAlgHom K ℂ) φ
    change aeval (f x) (minpoly ℚ a) = 0
    rw [aeval_algHom_apply,show aeval x (minpoly ℚ a)=0 from IntermediateField.aeval_gen_minpoly ℚ a,map_zero]
  obtain ⟨n,hn,e⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one K ℂ hx norm
  refine ⟨n,hn,?_⟩
  have eq := congrArg (algebraMap K ℂ) e
  change (algebraMap K ℂ x) ^ n = 1
  simpa only [map_pow,map_one] using eq
