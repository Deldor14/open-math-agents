import Mathlib.Tactic

open Finset
namespace Erdos142PairDirections

/-- All successes for every subsequence of the listed moves. Each move is a
    permutation even at unmatched vertices, where it fixes the point. -/
def starts {X ι : Type*} [DecidableEq X] (move : ι → X ≃ X) (G : Finset X) :
    List ι → Finset X
  | [] => G
  | i::l =>
    let H := starts move G l
    H ∩ H.map (move i).symm.toEmbedding

theorem starts_bound {X ι : Type*} [DecidableEq X] [Fintype X]
    (move : ι → X ≃ X) (G : Finset X) (l : List ι) :
    (univ \ starts move G l).card ≤ 2^l.length*(univ \ G).card := by
  induction l with
  | nil => simp [starts]
  | cons i l ih =>
    let H := starts move G l
    have cover : univ \ starts move G (i::l) ⊆ (univ \ H) ∪ (univ \ H).map (move i).symm.toEmbedding := by
      intro x hx
      have miss := (mem_sdiff.mp hx).2
      by_cases a : x ∈ H
      · apply mem_union_right _
        refine mem_map.mpr ⟨move i x,mem_sdiff.mpr ⟨mem_univ _,?_⟩,by simp⟩
        intro hm
        exact miss (mem_inter.mpr ⟨a,mem_map.mpr ⟨_,hm,by simp⟩⟩)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _,a⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [card_map] at c
    simp only [List.length_cons,pow_succ]
    change (univ \ H).card ≤ _ at ih
    nlinarith only [ih,c]

theorem exists_start {X ι : Type*} [DecidableEq X] [Fintype X]
    (move : ι → X ≃ X) (G : Finset X) (l : List ι)
    (h : 2^l.length*(univ \ G).card < Fintype.card X) :
    (starts move G l).Nonempty := by
  by_contra! missing
  have b := starts_bound move G l
  rw [missing] at b
  simpa using (show ¬ (univ \ (∅ : Finset X)).card ≤ 2^l.length*(univ \ G).card by simpa using h.not_ge) b

def follow {X ι : Type*} (move : ι → X ≃ X) (use : ι → Bool) : List ι → X → X
  | [], x => x
  | i::l, x => follow move use l (if use i then move i x else x)

theorem follow_good {X ι : Type*} [DecidableEq X] (move : ι → X ≃ X)
    (G : Finset X) (use : ι → Bool) (l : List ι) (x : X) (hx : x ∈ starts move G l) :
    follow move use l x ∈ G := by
  induction l generalizing x with
  | nil => exact hx
  | cons i l ih =>
    obtain ⟨a,b⟩ := mem_inter.mp hx
    obtain ⟨y,hy,e⟩ := mem_map.mp b
    simp only [follow]
    split
    · apply ih
      have eq : move i x=y := by simp [← e]
      simpa [eq] using hy
    · exact ih x a

private theorem at_start {X ι : Type*} [DecidableEq X] (move : ι → X ≃ X)
    (G : Finset X) (l : List ι) (x : X) (hx : x ∈ starts move G l) : x ∈ G := by
  induction l with
  | nil => exact hx
  | cons i l ih => exact ih (mem_inter.mp hx).1

private theorem after_move {X ι : Type*} [DecidableEq X] (move : ι → X ≃ X)
    (G : Finset X) {l : List ι} {i : ι} {x : X} (hx : x ∈ starts move G (i::l)) :
    move i x ∈ starts move G l := by
  obtain ⟨y,hy,eq⟩ := mem_map.mp (mem_inter.mp hx).2
  simpa [← eq] using hy

/-- Positions of every selected subsequence are the signed sums at the root. -/
theorem follow_position {X ι : Type*} [DecidableEq X] (move : ι → X ≃ X)
    (G : Finset X) (pos : X → ℤ) (sgn : ι → X → ℤ) (weight : ι → ℤ)
    (displace : ∀ x ∈ G, ∀ i, pos (move i x)=pos x+sgn i x*weight i)
    (stable : ∀ x ∈ G, ∀ i j, i ≠ j → sgn j (move i x)=sgn j x)
    (use : ι → Bool) (l : List ι) (distinct : l.Nodup) (x : X) (hx : x ∈ starts move G l) :
    pos (follow move use l x)=pos x+(l.map (fun i => if use i then sgn i x*weight i else 0)).sum := by
  induction l generalizing x with
  | nil => simp [follow]
  | cons i l ih =>
    obtain ⟨miss,nd⟩ := List.nodup_cons.mp distinct
    have gx := at_start move G _ x hx
    by_cases b : use i=true
    · have eq := ih nd (move i x) (after_move move G hx)
      have values : l.map (fun j => if use j then sgn j (move i x)*weight j else 0) =
          l.map (fun j => if use j then sgn j x*weight j else 0) := by
        apply List.map_congr_left
        intro j hj
        rw [stable x gx i j (by intro ij; exact miss (ij ▸ hj))]
      simp only [follow,b,ite_true,List.map_cons,List.sum_cons]
      rw [eq,values,displace x gx i]
      ring
    · simpa [follow,b] using ih nd x (mem_inter.mp hx).1

/-- Distinct subsequences have distinct final sign vectors when all signs are ±1. -/
theorem follow_sign {X ι : Type*} [DecidableEq X] [DecidableEq ι] (move : ι → X ≃ X)
    (G : Finset X) (sgn : ι → X → ℤ)
    (change : ∀ x ∈ G, ∀ i j, sgn j (move i x)=if j=i then -(sgn j x) else sgn j x)
    (use : ι → Bool) (l : List ι) (distinct : l.Nodup) (x : X) (hx : x ∈ starts move G l) (j : ι) :
    sgn j (follow move use l x)=if j ∈ l ∧ use j=true then -(sgn j x) else sgn j x := by
  induction l generalizing x with
  | nil => simp [follow]
  | cons i l ih =>
    obtain ⟨miss,nd⟩ := List.nodup_cons.mp distinct
    have gx := at_start move G _ x hx
    by_cases b : use i=true
    · simp only [follow,b,ite_true]
      rw [ih nd (move i x) (after_move move G hx), change x gx i j]
      by_cases ji : j=i
      · subst j
        simp [b,miss]
      · simp [ji]
    · rw [follow,if_neg b]
      rw [ih nd x (mem_inter.mp hx).1]
      by_cases ji : j=i
      · subst j
        simp [b,miss]
      · simp [ji]

private def leftDigit (a b : Fin 3) : Fin 2 := if a=b ∨ (a=0 ∧ b=2) then 0 else 1
private def midDigit (a b : Fin 3) : Fin 2 := if a<b then 1 else 0
private def rightDigit (a b : Fin 3) : Fin 2 := if a=2 ∧ b=0 then 1 else 0

private theorem digit_identity : ∀ a b : Fin 3,
    ((leftDigit a b).val:ℤ)+(rightDigit a b).val-2*(midDigit a b).val=(a.val:ℤ)-b.val := by decide

private theorem digit_detect : ∀ a b : Fin 3,
    leftDigit a b=midDigit a b → midDigit a b=rightDigit a b → a=b := by decide

/-- If a binary cube embeds faithfully with progression-free image, every
    ternary digit sum on the same weights is distinct. -/
theorem ternary_injective {ι : Type*} [Fintype ι] (w : ι → ℤ)
    (faithfulFree : ∀ X Y Z : ι → Fin 2,
      (∑ i, ((X i).val:ℤ)*w i)+(∑ i, ((Z i).val:ℤ)*w i)=2*(∑ i, ((Y i).val:ℤ)*w i) →
      X=Y ∧ Y=Z) :
    Function.Injective (fun T : ι → Fin 3 => ∑ i, ((T i).val:ℤ)*w i) := by
  intro a b eq
  let X (i : ι) := leftDigit (a i) (b i)
  let Y (i : ι) := midDigit (a i) (b i)
  let Z (i : ι) := rightDigit (a i) (b i)
  have localEq (i : ι) : ((X i).val:ℤ)*w i+((Z i).val:ℤ)*w i-2*(((Y i).val:ℤ)*w i) =
      ((a i).val:ℤ)*w i-((b i).val:ℤ)*w i := by
    have h := congrArg (fun v : ℤ => v*w i) (digit_identity (a i) (b i))
    dsimp only [X,Y,Z]
    linarith only [h]
  have total := Finset.sum_congr (s₁:=univ) rfl (fun i _ => localEq i)
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum] at total
  obtain ⟨ex,ez⟩ := faithfulFree X Y Z (by dsimp at eq; omega)
  funext i
  exact digit_detect _ _ (congrFun ex i) (congrFun ez i)

/-- Disjoint binary cubes in a progression-free set remain disjoint when all
    binary digit places are enlarged to three digit values. -/
theorem disjoint_ternary {ι β : Type*} [Fintype ι] (w : ι → ℤ) (base : β → ℤ)
    (faithfulFree : ∀ (b c : β) (X Y Z : ι → Fin 2),
      (base b + ∑ i, ((X i).val:ℤ)*w i)+(base c + ∑ i, ((Z i).val:ℤ)*w i) =
      2*(base c + ∑ i, ((Y i).val:ℤ)*w i) → b=c ∧ X=Y ∧ Y=Z) :
    Function.Injective (fun P : β × (ι → Fin 3) => base P.1+∑ i, ((P.2 i).val:ℤ)*w i) := by
  rintro ⟨b,a⟩ ⟨c,d⟩ eq
  change base b+(∑ i, ((a i).val:ℤ)*w i)=base c+(∑ i, ((d i).val:ℤ)*w i) at eq
  let X (i : ι) := leftDigit (a i) (d i)
  let Y (i : ι) := midDigit (a i) (d i)
  let Z (i : ι) := rightDigit (a i) (d i)
  have localEq (i : ι) : ((X i).val:ℤ)*w i+((Z i).val:ℤ)*w i-2*(((Y i).val:ℤ)*w i) =
      ((a i).val:ℤ)*w i-((d i).val:ℤ)*w i := by
    have h := congrArg (fun v : ℤ => v*w i) (digit_identity (a i) (d i))
    dsimp only [X,Y,Z]
    linarith only [h]
  have total := Finset.sum_congr (s₁:=univ) rfl (fun i _ => localEq i)
  simp only [sum_sub_distrib,sum_add_distrib,← mul_sum] at total
  obtain ⟨bc,ex,ez⟩ := faithfulFree b c X Y Z (by omega)
  apply Prod.ext bc
  funext i
  exact digit_detect _ _ (congrFun ex i) (congrFun ez i)

theorem ternary_volume {ι β : Type*} [Fintype ι] [Fintype β]
    (w : ι → ℤ) (base : β → ℤ) (N : ℕ)
    (faithfulFree : ∀ (b c : β) (X Y Z : ι → Fin 2),
      (base b + ∑ i, ((X i).val:ℤ)*w i)+(base c + ∑ i, ((Z i).val:ℤ)*w i) =
      2*(base c + ∑ i, ((Y i).val:ℤ)*w i) → b=c ∧ X=Y ∧ Y=Z)
    (rangeBound : ∀ (P : β × (ι → Fin 3)), base P.1+∑ i, ((P.2 i).val:ℤ)*w i ∈
      Ico (0:ℤ) (N:ℤ)) :
    Fintype.card β * 3^(Fintype.card ι) ≤ N := by
  classical
  let f (P : β × (ι → Fin 3)) := base P.1+∑ i, ((P.2 i).val:ℤ)*w i
  have inc : univ.image f ⊆ Ico (0:ℤ) (N:ℤ) := by
    intro y hy
    obtain ⟨p,_,rfl⟩ := mem_image.mp hy
    exact rangeBound p
  have bound := card_le_card inc
  rw [card_image_of_injective _ (disjoint_ternary w base faithfulFree)] at bound
  simpa using bound

#print axioms disjoint_ternary
#print axioms ternary_volume
#print axioms starts_bound
#print axioms exists_start
#print axioms follow_good
#print axioms follow_position
#print axioms follow_sign
#print axioms ternary_injective
end Erdos142PairDirections
