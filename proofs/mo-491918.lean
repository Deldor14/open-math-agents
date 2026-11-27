import OMAStatements.S_mo_491918
import Mathlib

open OMA.S_mo_491918
namespace Deldor14.Picking

abbrev H := List (Fin 5)
private def profile (_ : Fin 3) (h : H) : Fin 5 :=
  if h=[] then 3 else if h=[3,0] then 4 else
    if 0∉h then 0 else if 1∉h then 1 else if 2∉h then 2 else if 3∉h then 3 else 4
private def points (i : Fin 3) (j : Fin 5) : ℕ := if i=0 ∧ j.val<3 then 1 else 0
private def gain (i : Fin 3) (h : H) : ℕ := ∑ j ∈ bundle h i,points i j
private noncomputable def P (i : Fin 3) (j : Fin 5) : ℝ := points i j
private theorem cast_gain (i : Fin 3) (h : H) : (gain i h:ℝ)=value P i (bundle h i) := by
  simp [gain,value,P]

/-- Check all legal continuations after an individual deviation. -/
private def bounded (i : Fin 3) (maximum : ℕ) : ℕ → H → Bool
  | 0,h => decide (gain i h ≤ maximum)
  | k+1,h => if mover (by decide : 0<3) h=i
    then decide (∀ j : Fin 5,j∉h → bounded i maximum k (h++[j])=true)
    else bounded i maximum k (h++[profile (mover (by decide) h) h])

private def localCheck (h : H) : Bool := decide
  ((h.length<5 → ∀ i,profile i h∉h) ∧ ∀ i : Fin 3,
    bounded i (gain i (finish (by decide) profile h)) (5-h.length) h=true)

/-- Traverse the finite tree of legal histories, including each internal node. -/
private def tree : ℕ → H → Bool
  | 0,h => localCheck h
  | n+1,h => localCheck h && decide (∀ j : Fin 5,j∉h → tree n (h++[j])=true)

private theorem visit (h tail : H) (n : ℕ) (ht : tree n h=true)
    (hs : (h++tail).Nodup) (hlen : tail.length≤n) : localCheck (h++tail)=true := by
  induction tail generalizing h n with
  | nil =>
    cases n with
    | zero => simpa [tree] using ht
    | succ n => simpa using (Bool.and_eq_true_iff.mp ht).1
  | cons j tail ih =>
    cases n with
    | zero => simp at hlen
    | succ n =>
      have child := of_decide_eq_true (Bool.and_eq_true_iff.mp ht).2
      have fresh : j∉h := by
        have dis := (List.nodup_append.mp hs).2.2
        exact fun hj => dis j hj j (by simp) rfl
      have hs' : ((h++[j])++tail).Nodup := by simpa using hs
      simpa using ih (h++[j]) n (child j fresh) hs' (by simpa using hlen)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
private theorem checked : tree 5 []=true := by decide +kernel

private theorem everywhere (h : H) (hd : h.Nodup) (hl : h.length≤5) :
    (h.length<5 → ∀ i,profile i h∉h) ∧ ∀ i : Fin 3,
      bounded i (gain i (finish (by decide) profile h)) (5-h.length) h=true := by
  apply of_decide_eq_true
  exact visit [] h 5 checked (by simpa using hd) hl

private theorem legalP (i : Fin 3) : Legal (profile i) :=
  fun h hd hl => (everywhere h hd hl.le).1 hl i

private theorem boundSound (i : Fin 3) (s : Strategy 5) (legalS : Legal s) (v k : ℕ) (h : H)
    (hd : h.Nodup) (hl : k+h.length≤5) (b : bounded i v k h=true) :
    gain i (play (by decide) (Function.update profile i s) k h) ≤ v := by
  induction k generalizing h with
  | zero => exact of_decide_eq_true b
  | succ k ih =>
    by_cases turn : mover (by decide : 0<3) h=i
    · have all := of_decide_eq_true (by simpa [bounded,turn] using b :
          decide (∀ j : Fin 5,j∉h → bounded i v k (h++[j])=true)=true)
      have f := legalS h hd (by omega)
      simp only [play,turn,Function.update_self]
      exact ih (h++[s h]) (by simpa only [List.concat_eq_append] using (List.nodup_concat ..).mpr ⟨f,hd⟩) (by simp; omega) (all _ f)
    · have f := legalP (mover (by decide) h) h hd (by omega)
      simp only [play,Function.update_of_ne turn]
      apply ih (h++[profile (mover (by decide) h) h]) (by simpa only [List.concat_eq_append] using (List.nodup_concat ..).mpr ⟨f,hd⟩) (by simp; omega)
      simpa [bounded,turn] using b

private theorem equilibrium : IsSPNE (by decide) P profile := by
  refine ⟨legalP,?_⟩
  intro h hd hl i s legalS
  rw [← cast_gain,← cast_gain]
  exact_mod_cast boundSound i s legalS _ (5-h.length) h hd (by omega) ((everywhere h hd hl).2 i)

theorem result : ¬ (type_of% @OMA.S_mo_491918.main) := by
  intro hypoth
  have e := hypoth 3 5 (by decide) P (fun i j => Nat.cast_nonneg _) profile equilibrium 1 (by decide)
  have their : (∑ j ∈ bundle (finish (by decide) profile []) (1 : Fin 3),points 0 j)=2 := by decide +kernel
  have own : gain 0 (finish (by decide) profile [])=1 := by decide +kernel
  have theirReal : value P 0 (bundle (finish (by decide) profile []) (1 : Fin 3))=2 := by
    unfold value P
    exact_mod_cast their
  change value P 0 _ ≤ value P 0 _ at e
  rw [theirReal] at e
  change 2 ≤ value P (0 : Fin 3) (bundle (finish (by decide) profile []) (0 : Fin 3)) at e
  rw [← cast_gain (0 : Fin 3) (finish (by decide) profile []),own] at e
  norm_num at e

end Deldor14.Picking
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_491918.main) := Deldor14.Picking.result
