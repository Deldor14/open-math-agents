import OMAStatements.S_oeis_a222945
import Mathlib

namespace Deldor14.DistinctSums
open OMA.S_oeis_a222945 Finset

private theorem bound (x y z N : ℤ) (hn : 2≤N) (hx : |x|≤N) (hy : |y|≤N) (hz : |z|≤N)
    (hp : |x*y*z|≤N) : |x+y+z|≤2*N := by
  apply (abs_add_le ..).trans
  apply (add_le_add_left (abs_add_le x y) |z|).trans
  by_cases a : x=0
  · simp [a];omega
  by_cases b : y=0
  · simp [b];omega
  by_cases c : z=0
  · simp [c];omega
  have X : 1≤|x| := by have := abs_pos.mpr a;omega
  have Y : 1≤|y| := by have := abs_pos.mpr b;omega
  have Z : 1≤|z| := by have := abs_pos.mpr c;omega
  rw [abs_mul,abs_mul] at hp
  have xy : 1≤|x| * |y| := by nlinarith [mul_nonneg (sub_nonneg.mpr X) (sub_nonneg.mpr Y)]
  nlinarith [mul_nonneg (sub_nonneg.mpr X) (sub_nonneg.mpr Y),
    mul_nonneg (sub_nonneg.mpr xy) (sub_nonneg.mpr Z)]

private theorem interval (n : ℕ) (hn : 2≤n) : sums n=Icc (-2*(n:ℤ)) (2*(n:ℤ)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨⟨x,y,z⟩,mem,rfl⟩ := mem_image.mp ht
    simp only [mem_filter,mem_product,mem_Icc] at mem
    obtain ⟨⟨hx,hy,hz⟩,hp⟩ := mem
    have h := abs_le.mp (bound x y z n (by exact_mod_cast hn) (abs_le.mpr hx) (abs_le.mpr hy) (abs_le.mpr hz) hp)
    exact mem_Icc.mpr ⟨by dsimp;linarith [h.1],h.2⟩
  · intro h
    obtain ⟨l,u⟩ := mem_Icc.mp h
    apply mem_image.mpr
    refine ⟨(t/2,t-t/2,0),?_,by dsimp;ring⟩
    simp only [mem_filter,mem_product,mem_Icc,mul_zero,abs_zero]
    omega

private def f (k : ℕ) := 4*k+5
private theorem ending (n : ℕ) : endsIn01 n ↔ n ∈ Set.range f := by
  by_cases sm : n<4
  · have hn : ¬ endsIn01 n := by unfold endsIn01; interval_cases n <;> decide
    have hf : n ∉ Set.range f := by
      rintro ⟨k,hk⟩
      dsimp [f] at hk
      omega
    simp [hn,hf]
  have pos : 0<n := by omega
  have half : 0<n/2 := by omega
  simp only [endsIn01,Nat.digits_def' (by decide : 1<2) pos,Nat.digits_def' (by decide : 1<2) half,
    List.take_succ_cons,List.take_zero,List.cons.injEq,and_true]
  constructor
  · intro h
    exact ⟨n/4-1,by dsimp [f];omega⟩
  · rintro ⟨k,rfl⟩
    dsimp [f]
    omega
private theorem nth (k : ℕ) : Nat.nth endsIn01 k=f k := by
  have mono : StrictMono f := by intro a b hab;dsimp [f];omega
  have eq : Set.ofPred endsIn01=Set.range f := Set.ext ending
  have inf : (Set.ofPred endsIn01).Infinite := eq ▸ Set.infinite_range_of_injective mono.injective
  apply Eq.symm
  apply Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn f
  · intro x hx
    obtain ⟨t,rfl⟩ := (ending x).mp hx
    exact ⟨t,fun h => (inf h).elim,rfl⟩
  · exact fun t _ => (ending _).mpr ⟨t,rfl⟩
  · exact mono.strictMonoOn _
  · exact fun h => (inf h).elim
theorem result : type_of% @OMA.S_oeis_a222945.main := by
  intro n hn
  rw [a,interval n hn,Int.card_Icc,A004766,nth,f]
  omega
end Deldor14.DistinctSums
theorem OMA.solution : type_of% @OMA.S_oeis_a222945.main := Deldor14.DistinctSums.result
