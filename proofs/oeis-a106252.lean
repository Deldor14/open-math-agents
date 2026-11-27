import OMAStatements.S_oeis_a106252
import Mathlib

open OMA.S_oeis_a106252
namespace Deldor14.Triples

private theorem short {d s : ℕ} (hd : 0 < d) (hs : 0 < s) (cap : s ≤ d*2) (dv : d ∣ s) :
    s=d ∨ s=2*d := by
  obtain ⟨u,rfl⟩ := dv
  have hu : u ≤ 2 := Nat.le_of_mul_le_mul_left cap hd
  interval_cases u <;> simp_all [Nat.mul_comm]

private theorem classify {x y z : ℕ} (hx : 0<x) (hxy : x ≤ y) (hyz : y ≤ z)
    (dy : y ∣ x+z) (dz : z ∣ x+y) :
    (y=x ∧ z=x) ∨ (y=x ∧ z=2*x) ∨ (y=2*x ∧ z=3*x) := by
  rcases short (by omega : 0<z) (by omega) (by omega) dz with eq | eq
  · have d : y ∣ 2*x := by
      have h : y ∣ 2*x+y := by convert dy using 1 <;> omega
      simpa using h
    rcases short (by omega : 0<y) (by omega) (by omega) d with e | e <;> omega
  · omega

private def first (x : ℕ) := (x,x,x)
private def second (x : ℕ) := (x,x,2*x)
private def third (x : ℕ) := (x,2*x,3*x)

private theorem count (n : ℕ) : a n=n+n/2+n/3 := by
  let A := (Finset.Icc 1 n).image first
  let B := (Finset.Icc 1 (n/2)).image second
  let C := (Finset.Icc 1 (n/3)).image third
  have eq : triples n=A ∪ B ∪ C := by
    ext ⟨x,y,z⟩
    simp only [triples,A,B,C,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc,
      Finset.mem_union,Finset.mem_image,first,second,third,Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hx,hxn⟩,⟨hy,hyn⟩,hz,hzn⟩,hxy,hyz,_,dy,dz⟩
      rcases classify hx hxy hyz dy dz with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact Or.inl (Or.inl ⟨_,⟨hx,hxn⟩,rfl,rfl,rfl⟩)
      · exact Or.inl (Or.inr ⟨_,⟨hx,by omega⟩,rfl,rfl,rfl⟩)
      · exact Or.inr ⟨_,⟨hx,by omega⟩,rfl,rfl,rfl⟩
    · rintro ((⟨u,⟨hu,cap⟩,rfl,rfl,rfl⟩ | ⟨u,⟨hu,cap⟩,rfl,rfl,rfl⟩) | ⟨u,⟨hu,cap⟩,rfl,rfl,rfl⟩)
      all_goals refine ⟨by omega,by omega,by omega,?_,?_,?_⟩
      all_goals first | exact ⟨2,by omega⟩ | exact ⟨1,by omega⟩ | exact ⟨3,by omega⟩ | exact ⟨5,by omega⟩
  have distinctAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    rintro _ hA hB
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j,hj,e⟩ := Finset.mem_image.mp hB
    simp [first,second] at e
    simp at hi hj
    omega
  have distinctC : Disjoint (A ∪ B) C := by
    apply Finset.disjoint_left.mpr
    rintro _ hab hc
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
    have pos := (Finset.mem_Icc.mp hi).1
    rcases Finset.mem_union.mp hab with h | h
    all_goals obtain ⟨j,_,e⟩ := Finset.mem_image.mp h
    all_goals simp [first,second,third] at e <;> omega
  have one : Function.Injective first := fun _ _ e => congrArg Prod.fst e
  have two : Function.Injective second := fun _ _ e => congrArg Prod.fst e
  have three : Function.Injective third := fun _ _ e => congrArg Prod.fst e
  rw [a,eq,Finset.card_union_of_disjoint distinctC,Finset.card_union_of_disjoint distinctAB]
  simp [A,B,C,Finset.card_image_of_injective _ one,Finset.card_image_of_injective _ two,
    Finset.card_image_of_injective _ three,Nat.card_Icc]

end Deldor14.Triples

theorem OMA.solution : type_of% @OMA.S_oeis_a106252.main := by
  intro n
  simp only [Deldor14.Triples.count]
  omega
