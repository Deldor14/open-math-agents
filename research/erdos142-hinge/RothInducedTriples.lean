import RothClusterCovers

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters

private theorem two_roots {A : Finset ℕ} {t a b : ℕ} (ht : 0<t) (weak : Weak t A)
    (ha : a ∈ pairs t A) (hb : b ∈ pairs t A) (ab : a≠b) :
    (a+t≠b ∧ b+t≠a) ∧
    (∀ k : ℤ, -4≤k → k≤4 → (a:ℤ)-b ≠ k*t ∧ 2*((a:ℤ)-b) ≠ k*t) := by
  obtain ⟨aa,at'⟩ := mem_filter.mp ha
  obtain ⟨bb,bt⟩ := mem_filter.mp hb
  have w₁ := weak a aa (a+t) at' b bb
  have w₂ := weak b bb (b+t) bt a aa
  have w₃ := weak a aa b bb (a+t) at'
  have w₄ := weak b bb a aa (b+t) bt
  have w₅ := weak a aa (a+t) at' (b+t) bt
  have w₆ := weak b bb (b+t) bt (a+t) at'
  constructor
  · omega
  · intro k lo hi
    interval_cases k <;> norm_num <;> omega

/-- Every midpoint defect of paired roots which is a multiple of t of
    absolute value at most 4t comes from a single root. Repetitions are allowed. -/
theorem strong_roots {A : Finset ℕ} {t : ℕ} (ht : 0<t) (weak : Weak t A)
    {x y z : ℕ} (hx : x ∈ pairs t A) (hy : y ∈ pairs t A) (hz : z ∈ pairs t A)
    (j : ℤ) (lo : -4≤j) (hi : j≤4) (eq : (x:ℤ)+z-2*y=j*t) : x=y ∧ y=z := by
  by_cases xy : x=y
  · subst y
    refine ⟨rfl,?_⟩
    by_contra bad
    have h := ((two_roots ht weak hz hx (Ne.symm bad)).2 j lo hi).1
    omega
  by_cases yz : y=z
  · subst z
    have h := ((two_roots ht weak hx hy xy).2 j lo hi).1
    omega
  by_cases xz : x=z
  · subst z
    have h := ((two_roots ht weak hx hy xy).2 j lo hi).2
    omega
  have hxy := (two_roots ht weak hx hy xy).1
  have hyz := (two_roots ht weak hy hz yz).1
  obtain ⟨xa,xt⟩ := mem_filter.mp hx
  obtain ⟨ya,yt⟩ := mem_filter.mp hy
  obtain ⟨za,zt⟩ := mem_filter.mp hz
  have orig := weak x xa y ya z za
  have plus := weak x xa (y+t) yt z za
  have minus := weak (x+t) xt y ya (z+t) zt
  interval_cases j <;> norm_num at eq <;> omega

/-- Exact rigidity of the three-digit extension. Every ordinary progression
    lies in one fiber, where its digit indices themselves form a progression. -/
theorem ternary_projection {A : Finset ℕ} {t : ℕ} (ht : 0<t) (weak : Weak t A)
    {x y z : ℕ} (hx : x ∈ pairs t A) (hy : y ∈ pairs t A) (hz : z ∈ pairs t A)
    (i j k : Fin 3) (eq : (x+i.val*t)+(z+k.val*t)=(y+j.val*t)+(y+j.val*t)) :
    x=y ∧ y=z ∧ i.val+k.val=j.val+j.val := by
  have e : ((x:ℤ)+(i.val:ℤ)*t)+(z+(k.val:ℤ)*t)=(y+(j.val:ℤ)*t)+(y+(j.val:ℤ)*t) := by exact_mod_cast eq
  have h := strong_roots ht weak hx hy hz (2*(j.val:ℤ)-i.val-k.val)
    (by have := i.isLt; have := k.isLt; omega) (by have := j.isLt; omega) (by linear_combination e)
  obtain ⟨rfl,rfl⟩ := h
  refine ⟨rfl,rfl,Nat.eq_of_mul_eq_mul_right ht ?_⟩
  simp only [Nat.add_mul]
  omega

def expand (t : ℕ) (p : ℕ × Fin 3) := p.1+p.2.val*t

theorem ternary_faithful {A : Finset ℕ} {t : ℕ} (ht : 0<t) (weak : Weak t A) :
    Set.InjOn (expand t) (↑(pairs t A ×ˢ (univ : Finset (Fin 3))) : Set (ℕ × Fin 3)) := by
  rintro ⟨x,i⟩ hx ⟨y,j⟩ hy eq
  change x+i.val*t=y+j.val*t at eq
  have h := ternary_projection ht weak (mem_product.mp hx).1 (mem_product.mp hy).1
    (mem_product.mp hy).1 i j j (by omega)
  obtain ⟨rfl,_,ij⟩ := h
  have : i=j := Fin.ext (by omega)
  simp [this]

#print axioms strong_roots
#print axioms ternary_projection
#print axioms ternary_faithful
end Erdos142InducedTriples
