import OMAStatements.S_oeis_a362559
import Mathlib

namespace Deldor14.PartitionWeights
open OMA.S_oeis_a362559

private theorem cons (a : ℕ) (l : List ℕ) :
    weightedSum (a::l)=a+l.sum+weightedSum l := by
  unfold weightedSum
  change (∑ i : Fin (l.length+1), (i.val+1)*(a::l)[i]) = _
  rw [Fin.sum_univ_succ]
  have e : ∑ i : Fin l.length, l[i] = l.sum := by
    simp only [Fin.getElem_fin]
    rw [← List.sum_ofFn,List.ofFn_getElem]
  simp only [Fin.getElem_fin,Fin.val_zero,Nat.zero_add,one_mul,List.getElem_cons_zero,Fin.val_succ,
    List.getElem_cons_succ]
  have f (i : Fin l.length) : (i.val+1+1)*l[i.val] = (i.val+1)*l[i.val]+l[i.val] := by ring
  simp_rw [f]
  rw [Finset.sum_add_distrib]
  simp only [Fin.getElem_fin] at e
  omega

private theorem append (l : List ℕ) (a : ℕ) :
    weightedSum (l++[a])=weightedSum l+(l.length+1)*a := by
  induction l with
  | nil => simp [weightedSum]
  | cons b l ih =>
    rw [List.cons_append,cons,cons,ih]
    simp
    ring

private theorem mirror (l : List ℕ) :
    weightedSum l + weightedSum l.reverse = (l.length+1)*l.sum := by
  induction l with
  | nil => simp [weightedSum]
  | cons a l ih =>
    rw [cons,List.reverse_cons,append]
    simp only [List.length_reverse,List.length_cons,List.sum_cons]
    linear_combination ih

theorem result : type_of% @OMA.S_oeis_a362559.main := by
  intro n y _ h
  have both : n ∣ weightedSum y + weightedSum y.reverse := by
    rw [mirror,h.2.2]
    exact dvd_mul_left _ _
  constructor
  · intro h
    exact (Nat.dvd_add_right h).mp both
  · intro h
    exact (Nat.dvd_add_left h).mp both

end Deldor14.PartitionWeights
theorem OMA.solution : type_of% @OMA.S_oeis_a362559.main := Deldor14.PartitionWeights.result
