import RothInducedTriples

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters

/-- Each residue class of the ternary extension is free when the modulus
    does not divide the prescribed step. The bound uses ceiling division. -/
theorem residue_bound {A : Finset ℕ} {n t b : ℕ} (ht : 0<t) (hb : 0<b)
    (miss : ¬ b ∣ t) (fit : A ⊆ range n) (weak : Weak t A) :
    3*(pairs t A).card ≤ b*rothNumberNat ((n+t+b-1)/b) := by
  classical
  let U := (pairs t A ×ˢ (univ : Finset (Fin 3))).image (expand t)
  have count : U.card = (pairs t A).card*3 := by
    dsimp only [U]
    rw [card_image_of_injOn (ternary_faithful ht weak),card_product]
    simp
  let F (r : ℕ) := U.filter (fun x => x%b=r)
  have rsum : ∑ r ∈ range b, (F r).card = U.card := by
    dsimp only [F]
    simp_rw [card_filter]
    rw [sum_comm]
    simp [Nat.mod_lt _ hb]
  have each (r : ℕ) : (F r).card ≤ rothNumberNat ((n+t+b-1)/b) := by
    let Q := (F r).image (fun x => x/b)
    have rep {x} (hx : x ∈ F r) : r+b*(x/b)=x := by
      rw [← (mem_filter.mp hx).2]
      exact Nat.mod_add_div x b
    have inj : Set.InjOn (fun x => x/b) (↑(F r) : Set ℕ) := by
      intro x hx y hy e
      change x/b=y/b at e
      have := rep hx
      rw [e,rep hy] at this
      exact this.symm
    have freeQ : ThreeAPFree (↑Q : Set ℕ) := by
      apply threeAPFree_iff_eq_right.mpr
      intro X hX Y hY Z hZ e
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hX
      obtain ⟨y,hy,rfl⟩ := mem_image.mp hY
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hZ
      have eq : x+z=y+y := by
        have q := congrArg (fun v => b*v) e
        simp only [Nat.mul_add] at q
        have := rep hx
        have := rep hy
        have := rep hz
        omega
      obtain ⟨⟨a,i⟩,ai,ex⟩ := mem_image.mp (mem_filter.mp hx).1
      obtain ⟨⟨c,j⟩,cj,ey⟩ := mem_image.mp (mem_filter.mp hy).1
      obtain ⟨⟨f,k⟩,fk,ez⟩ := mem_image.mp (mem_filter.mp hz).1
      obtain ⟨rfl,rfl,ij⟩ := ternary_projection ht weak (mem_product.mp ai).1
        (mem_product.mp cj).1 (mem_product.mp fk).1 i j k (by simpa [← ex,← ey,← ez,expand] using eq)
      change a+i.val*t=x at ex
      change a+j.val*t=y at ey
      change a+k.val*t=z at ez
      by_cases same : i=k
      · rw [same] at ex
        rw [← ex,← ez]
      exfalso
      have one : i.val+1=j.val ∨ j.val+1=i.val := by
        have ine : i.val≠k.val := fun e => same (Fin.ext e)
        have := i.isLt
        have := j.isLt
        have := k.isLt
        omega
      apply miss
      rcases one with inc|dec
      · rw [← inc,Nat.add_mul,one_mul] at ey
        refine ⟨y/b-x/b,?_⟩
        rw [Nat.mul_sub]
        have := rep hx
        have := rep hy
        omega
      · rw [← dec,Nat.add_mul,one_mul] at ex
        refine ⟨x/b-y/b,?_⟩
        rw [Nat.mul_sub]
        have := rep hx
        have := rep hy
        omega
    rw [← card_image_of_injOn inj]
    apply freeQ.le_rothNumberNat _ _ rfl
    intro q hq
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hq
    obtain ⟨⟨a,i⟩,p,ex⟩ := mem_image.mp (mem_filter.mp hx).1
    have xa := mem_range.mp (fit (mem_filter.mp (mem_product.mp p).1).2)
    change a+i.val*t=x at ex
    have sm := Nat.mul_le_mul_right t (show i.val≤2 by have := i.isLt; omega)
    have xn : x<n+t := by omega
    have br := Nat.mod_lt x hb
    have rr := Nat.mod_add_div x b
    apply Nat.lt_of_succ_le
    apply (Nat.le_div_iff_mul_le hb).mpr
    rw [Nat.succ_mul, Nat.mul_comm (x/b) b]
    omega
  have add := sum_le_sum (s:=range b) (fun r _ => each r)
  rw [rsum,count] at add
  simpa [Nat.mul_comm] using add

#print axioms residue_bound
end Erdos142InducedTriples
