import OMAStatements.S_oeis_a080674
import Mathlib

namespace Deldor14.DecimalWords
open Finset

private def ok (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d ∉ ({0,1,2,3,4,5} : Finset ℕ)
private instance (m : ℕ) : Decidable (ok m) := inferInstanceAs (Decidable (∀ d ∈ Nat.digits 10 m, _))
private def good (n : ℕ) := (range (10^n)).filter (fun m => m≠0 ∧ ok m)
private def domain (n : ℕ) := (insert 0 (good n)) ×ˢ Icc 6 9
private def appendDigit (p : ℕ×ℕ) := p.2+10*p.1
private theorem memGood (n m : ℕ) : m∈good n ↔ m<10^n ∧ m≠0 ∧ ok m := by simp [good]
private theorem goodDigit (d : ℕ) : d ∉ ({0,1,2,3,4,5} : Finset ℕ) ↔ 6≤d := by simp; omega
private theorem product (n : ℕ) : good (n+1)=(domain n).image appendDigit := by
  ext m
  rw [memGood,mem_image]
  constructor
  · rintro ⟨hm,hpos,hgood⟩
    have eq := Nat.digits_eq_cons_digits_div (by decide : 1<10) hpos
    have h₁ : 6 ≤ m % 10 := (goodDigit _).mp (hgood _ (by simp [eq]))
    have h₂ : ok (m/10) := fun d hd => hgood d (by rw [eq]; exact List.mem_cons_of_mem _ hd)
    have bound : m/10 < 10^n := by rw [pow_succ] at hm; omega
    refine ⟨(m/10,m%10),?_,by exact Nat.mod_add_div m 10⟩
    simp only [domain,mem_product,mem_insert,memGood,mem_Icc]
    exact ⟨by by_cases hz : m/10=0; exact Or.inl hz; exact Or.inr ⟨bound,hz,h₂⟩,
      h₁,by omega⟩
  · rintro ⟨⟨u,d⟩,hp,rfl⟩
    simp only [domain,mem_product,mem_insert,memGood,mem_Icc] at hp
    obtain ⟨hu,hd,he⟩ := hp
    have hv : u<10^n ∧ ok u := by
      rcases hu with rfl | ⟨h,_,j⟩
      · exact ⟨by positivity,by simp [ok]⟩
      · exact ⟨h,j⟩
    change d+10*u < 10^(n+1) ∧ d+10*u ≠ 0 ∧ ok (d+10*u)
    refine ⟨by rw [pow_succ]; omega,by omega,?_⟩
    unfold ok
    rw [Nat.digits_add 10 (by decide) d u (by omega) (Or.inl (by omega))]
    simpa only [List.forall_mem_cons,ok] using And.intro ((goodDigit d).mpr hd) hv.2

private theorem cardRec (n : ℕ) : (good (n+1)).card=((good n).card+1)*4 := by
  rw [product,card_image_of_injOn]
  · have hz : 0 ∉ good n := by simp [memGood]
    simp [domain,card_insert_of_notMem hz,Nat.card_Icc]
  · intro u hu v hv he
    have a := (mem_product.mp hu).2
    have b := (mem_product.mp hv).2
    simp only [mem_Icc] at a b
    unfold appendDigit at he
    exact Prod.ext (by omega) (by omega)

theorem result : type_of% @OMA.S_oeis_a080674.main := by
  have eq (n : ℕ) : 3*(good n).card+4=4*4^n := by
    induction n with
    | zero => decide
    | succ n ih => rw [cardRec,pow_succ]; omega
  intro n
  change (good n).card=_
  have h := eq n
  have pos : 0<4^n := by positivity
  omega

end Deldor14.DecimalWords
theorem OMA.solution : type_of% @OMA.S_oeis_a080674.main := Deldor14.DecimalWords.result
