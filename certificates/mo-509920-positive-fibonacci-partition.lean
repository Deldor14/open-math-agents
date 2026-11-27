import Mathlib

/-! A decomposition into distinct positive Fibonacci numbers has a subcollection
of weight equal to its greatest Zeckendorf summand. Removing it and repeating
partitions the original collection. Indices use F₂ = 1.
The positive-n source question is MathOverflow 509920 (Brindel); Peter Taylor
published a different proof by merging adjacent Fibonacci numbers at
https://mathoverflow.net/a/509921. -/
namespace Deldor14.FibonacciPartition
open Nat Finset
private def Good (S : Finset ℕ) := ∀ x ∈ S, ∃ j, 2 ≤ j ∧ x = fib j
private lemma image_bound (m : ℕ) :
    ∑ x ∈ (range m).image fib, x ≤ ∑ i ∈ range m, fib i := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ,range_add_one,image_insert]
    by_cases h : fib m ∈ (range m).image fib
    · rw [insert_eq_of_mem h]; omega
    · rw [sum_insert h]; omega
private lemma extract (k : ℕ) (S : Finset ℕ) (hs : Good S)
    (cap : ∀ x ∈ S, x ≤ fib k) (total : fib k ≤ ∑ x ∈ S, x) :
    ∃ T ⊆ S, ∑ x ∈ T, x = fib k := by
  induction k using Nat.strong_induction_on generalizing S with
  | h k ih =>
    by_cases hit : fib k ∈ S
    · exact ⟨{fib k},singleton_subset_iff.mpr hit,by simp⟩
    match k with
    | 0 => exact ⟨∅,empty_subset _,by simp⟩
    | 1 =>
      have z (x) (hx : x ∈ S) : x=0 := by
        have u := cap x hx
        have ne : x ≠ fib 1 := fun e => hit (e ▸ hx)
        simp only [fib_one] at u ne; omega
      have : ∑ x ∈ S, x = 0 := sum_eq_zero z
      simp_all
    | k+2 =>
      have low (x) (hx : x ∈ S) (ne : x ≠ fib (k+1)) :
          ∃ j < k+1, fib j=x := by
        obtain ⟨j,_,rfl⟩ := hs x hx
        have strict := lt_of_le_of_ne (cap _ hx) (fun e => hit (e ▸ hx))
        have bound : j < k+2 := lt_of_not_ge (fun h => strict.not_ge (fib_mono h))
        have : j ≠ k+1 := fun e => ne (congrArg fib e)
        exact ⟨j,by omega,rfl⟩
      have prev : fib (k+1) ∈ S := by
        by_contra hp
        have sub : S ⊆ (range (k+1)).image fib := by
          intro x hx
          obtain ⟨j,hj,eq⟩ := low x hx (fun e => hp (e ▸ hx))
          exact mem_image.mpr ⟨j,mem_range.mpr hj,eq⟩
        have bd := (sum_le_sum_of_subset (f:=id) sub).trans (image_bound (k+1))
        have closed := fib_succ_eq_succ_sum (k+1)
        change (∑ x ∈ S, x) ≤ _ at bd
        change fib (k+2) = _ at closed
        omega
      let R := S.erase (fib (k+1))
      have rem (x) (hx : x ∈ R) := mem_erase.mp hx
      have goodR : Good R := fun x hx => hs x (rem x hx).2
      have capR : ∀ x ∈ R, x ≤ fib k := by
        intro x hx
        obtain ⟨j,hj,rfl⟩ := low x (rem _ hx).2 (rem _ hx).1
        exact fib_mono (by omega)
      have split := sum_erase_add (f:=id) S prev
      change (∑ x ∈ R, x) + fib (k+1) = ∑ x ∈ S, x at split
      have recur := fib_add_two (n:=k)
      obtain ⟨T,sub,eq⟩ := ih k (by omega) R goodR capR (by omega)
      have nt : fib (k+1) ∉ T := fun e => (rem _ (sub e)).1 rfl
      refine ⟨insert (fib (k+1)) T,insert_subset prev (fun x hx => (rem _ (sub hx)).2),?_⟩
      rw [sum_insert nt,eq]; omega
private lemma grouping (n : ℕ) (S : Finset ℕ) (hs : Good S) (sumS : ∑ x ∈ S, x = n) :
    ∃ p : ℕ → ℕ, (∀ x ∈ S, p x < n.zeckendorf.length) ∧
    ∀ i : Fin n.zeckendorf.length, ∑ x ∈ S.filter (fun x => p x=i.val), x = fib (n.zeckendorf.get i) := by
  classical
  induction n using Nat.strong_induction_on generalizing S with
  | h n ih =>
    by_cases hn : n=0
    · have sumZero : (∑ x ∈ S, x) = 0 := sumS.trans hn
      rw [hn]
      have empty : S=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨j,hj,rfl⟩ := hs x hx
        have hp := fib_pos.mpr (show 0<j by omega)
        have bd := single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) hx
        change fib j ≤ ∑ x ∈ S, x at bd
        exact (Nat.not_lt_zero _) (hp.trans_le (bd.trans_eq sumZero))
      subst S
      exact ⟨fun _ => 0,by simp,fun i => Fin.elim0 (by simpa only [zeckendorf_zero,List.length_nil] using i)⟩
    let k := greatestFib n
    let m := n-fib k
    have bound := fib_greatestFib_le n
    have pos : 0<fib k := fib_pos.mpr (greatestFib_pos.mpr (by omega))
    have mlt : m<n := by dsimp [m,k] at *;omega
    have z := zeckendorf_of_pos (show 0<n by omega)
    change n.zeckendorf = k :: m.zeckendorf at z
    have cap (x) (hx : x∈S) : x≤fib k := by
      obtain ⟨j,hj,rfl⟩ := hs x hx
      apply fib_mono
      apply le_greatestFib.mpr
      rw [←sumS]
      exact single_le_sum (f:=id) (fun _ _ => Nat.zero_le _) hx
    obtain ⟨T,sub,eq⟩ := extract k S hs cap (sumS ▸ bound)
    let R := S \ T
    have sumR : ∑ x ∈ R, x=m := by
      have both := sum_sdiff (f:=id) sub
      change (∑ x ∈ R, x)+(∑ x ∈ T, x)=∑ x ∈ S, x at both
      dsimp [m];omega
    obtain ⟨p,hp,parts⟩ := ih m mlt R (fun x hx => hs _ (mem_sdiff.mp hx).1) sumR
    let g (x:ℕ) := if x∈T then 0 else p x+1
    rw [z]
    refine ⟨g,?_,?_⟩
    · intro x hx
      by_cases hT : x∈T
      · simp [g,hT]
      · simpa [g,hT] using hp x (mem_sdiff.mpr ⟨hx,hT⟩)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · have he : S.filter (fun x => g x=0) = T := by
          ext x
          by_cases hx : x∈T
          · simp [g,hx,sub hx]
          · simp [g,hx]
        change (∑ x ∈ S.filter (fun x => g x=0), x) = fib k
        rw [he];exact eq
      · have he : S.filter (fun x => g x=j.val+1) = R.filter (fun x => p x=j.val) := by
          ext x
          by_cases hx : x∈T <;> simp [R,g,hx]
        change (∑ x ∈ S.filter (fun x => g x=j.val+1), x) = fib (m.zeckendorf.get j)
        rw [he];exact parts j

theorem positive (n : ℕ) (hn : 0<n) (S : Finset ℕ)
    (hs : ∀ x ∈ S, ∃ j, 2≤j ∧ x=fib j) (sumS : ∑ x ∈ S, x=n) :
    ∃ g : ℕ → Fin n.zeckendorf.length, ∀ i : Fin n.zeckendorf.length,
      ∑ x ∈ S.filter (fun x => g x=i), x = fib (n.zeckendorf.get i) := by
  classical
  obtain ⟨p,bound,parts⟩ := grouping n S hs sumS
  have len : 0<n.zeckendorf.length := by rw [zeckendorf_of_pos hn];simp
  let g (x:ℕ) : Fin n.zeckendorf.length := if hx : x∈S then ⟨p x,bound x hx⟩ else ⟨0,len⟩
  refine ⟨g,fun i => ?_⟩
  have eq : S.filter (fun x => g x=i) = S.filter (fun x => p x=i.val) := by
    ext x
    by_cases hx : x∈S <;> simp [hx,g,Fin.ext_iff]
  rw [eq];exact parts i

end Deldor14.FibonacciPartition
#print axioms Deldor14.FibonacciPartition.positive
