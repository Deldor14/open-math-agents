import OMAStatements.S_oeis_a102309
import Mathlib

namespace Deldor14.MobiusTriples
open OMA.S_oeis_a102309 Finset ArithmeticFunction

private def tri (n : ℕ) : Finset (ℕ × ℕ) :=
  ((range n) ×ˢ (range n)).filter (fun p => 0<p.1 ∧ p.1≤p.2)
private theorem mt {n i j : ℕ} : (i,j) ∈ tri n ↔ 0 < i ∧ i≤j ∧ j<n := by
  simp [tri]; omega
private theorem tc (n : ℕ) : (tri n).card=n.choose 2 := by
  induction n with
  | zero => simp [tri]
  | succ n ih =>
    let row := ((Icc 1 n) ×ˢ ({n}:Finset ℕ))
    have eq : tri (n+1)=tri n ∪ row := by
      ext ⟨i,j⟩
      simp only [mt,mem_union,row,mem_product,mem_Icc,mem_singleton]
      omega
    have dis : Disjoint (tri n) row := by
      rw [Finset.disjoint_left]
      rintro ⟨i,j⟩ h k
      have m := mt.mp h
      simp only [row,mem_product,mem_singleton] at k
      omega
    rw [eq,card_union_of_disjoint dis,ih,Nat.choose_succ_succ,Nat.choose_one_right]
    simp [row,Nat.add_comm]

private def gg (n : ℕ) (p : ℕ × ℕ) := p.1.gcd (p.2.gcd n)
private def slice (n : ℕ) := (tri n).filter (fun p => gg n p=1)
private def triple (n : ℕ) :=
  ((Icc 1 n ×ˢ Icc 1 n ×ˢ Icc 1 n).filter
    (fun t : ℕ × ℕ × ℕ => t.1≤t.2.1 ∧ t.2.1<t.2.2 ∧ gg t.2.2 (t.1,t.2.1)=1))
private theorem mtri {n i j k : ℕ} : (i,j,k) ∈ triple n ↔
    0 < i ∧ i≤j ∧ j<k ∧ k≤n ∧ gg k (i,j)=1 := by
  simp [triple]; omega
private theorem step (n : ℕ) : A100448 (n+1)=A100448 n+(slice (n+1)).card := by
  let lift (p : ℕ × ℕ) := (p.1,p.2,n+1)
  have inj : Function.Injective lift := by
    rintro ⟨a,b⟩ ⟨c,d⟩ h
    simpa [lift] using h
  have newrow (i j k : ℕ) : (i,j,k) ∈ (slice (n+1)).image lift ↔
      0 < i ∧ i≤j ∧ j<n+1 ∧ gg (n+1) (i,j)=1 ∧ k=n+1 := by
    constructor
    · intro h
      obtain ⟨⟨x,y⟩,hxy,e⟩ := mem_image.mp h
      have xy := mem_filter.mp hxy
      have t := mt.mp xy.1
      cases e
      exact ⟨t.1,t.2.1,t.2.2,xy.2,rfl⟩
    · rintro ⟨h1,h2,h3,h4,rfl⟩
      exact mem_image.mpr ⟨(i,j),mem_filter.mpr ⟨mt.mpr ⟨h1,h2,h3⟩,h4⟩,rfl⟩
  have eq : triple (n+1)=triple n ∪ (slice (n+1)).image lift := by
    ext ⟨i,j,k⟩
    simp only [mtri,mem_union,newrow]
    by_cases e : k=n+1
    · subst k; simp_all
    · constructor
      · intro h; exact Or.inl ⟨h.1,h.2.1,h.2.2.1,by omega,h.2.2.2.2⟩
      · rintro (h|h)
        · exact ⟨h.1,h.2.1,h.2.2.1,by omega,h.2.2.2.2⟩
        · omega
  have dis : Disjoint (triple n) ((slice (n+1)).image lift) := by
    rw [Finset.disjoint_left]
    rintro ⟨i,j,k⟩ h h'
    have t := mtri.mp h
    have t' := (newrow i j k).mp h'
    omega
  change (triple (n+1)).card = (triple n).card+_
  rw [eq,card_union_of_disjoint dis,card_image_of_injective _ inj]

private theorem scaled (n d : ℕ) (hd : d ∈ n.divisors) :
    ((tri n).filter (fun p => d ∣ p.1 ∧ d ∣ p.2)).card=(n/d).choose 2 := by
  have dp : 0<d := Nat.pos_of_mem_divisors hd
  obtain ⟨m,hm⟩ := (Nat.mem_divisors.mp hd).1
  subst n
  rw [Nat.mul_div_cancel_left m dp,← tc]
  apply card_nbij' (fun p => (p.1/d,p.2/d)) (fun p => (d*p.1,d*p.2))
  · rintro ⟨i,j⟩ h
    obtain ⟨ht,⟨x,rfl⟩,⟨y,rfl⟩⟩ := mem_filter.mp h
    have ht' := mt.mp ht
    simp [Nat.mul_div_cancel_left _ dp,mt]
    exact ⟨Nat.pos_of_mul_pos_left ht'.1, Nat.le_of_mul_le_mul_left ht'.2.1 dp,
      Nat.lt_of_mul_lt_mul_left ht'.2.2⟩
  · rintro ⟨i,j⟩ h
    have t := mt.mp h
    exact mem_filter.mpr ⟨mt.mpr ⟨Nat.mul_pos dp t.1,Nat.mul_le_mul_left _ t.2.1,
      Nat.mul_lt_mul_of_pos_left t.2.2 dp⟩,dvd_mul_right _ _,dvd_mul_right _ _⟩
  · rintro ⟨i,j⟩ h
    obtain ⟨_,⟨x,rfl⟩,⟨y,rfl⟩⟩ := mem_filter.mp h
    simp [Nat.mul_div_cancel_left _ dp]
  · rintro ⟨i,j⟩ h
    simp [Nat.mul_div_cancel_left _ dp]

private theorem delta (n : ℕ) (hn : n≠0) (p : ℕ × ℕ) :
    (∑ d ∈ n.divisors, if d ∣ p.1 ∧ d ∣ p.2 then moebius d else 0) =
      if gg n p=1 then (1:ℤ) else 0 := by
  have dg : gg n p ∣ n := (Nat.gcd_dvd_right ..).trans (Nat.gcd_dvd_right ..)
  have gn : gg n p≠0 := fun h => hn (by simpa [h] using dg)
  have eq : n.divisors.filter (fun d => d ∣ p.1 ∧ d ∣ p.2)=(gg n p).divisors := by
    ext d
    simp only [mem_filter,Nat.mem_divisors,hn,gn,ne_eq,not_false_eq_true,and_true,gg,Nat.dvd_gcd_iff]
    tauto
  rw [← sum_filter,eq,← coe_mul_zeta_apply,moebius_mul_coe_zeta,one_apply]

private theorem count (n : ℕ) (hn : n≠0) : a n=((slice n).card:ℤ) := by
  unfold a
  calc
    _ = ∑ d ∈ n.divisors, ∑ p ∈ tri n, if d ∣ p.1 ∧ d ∣ p.2 then moebius d else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [← sum_filter, sum_const,nsmul_eq_mul,scaled n d hd,mul_comm]
    _ = ∑ p ∈ tri n, if gg n p=1 then (1:ℤ) else 0 := by
      rw [sum_comm]
      exact sum_congr rfl (fun p _ => delta n hn p)
    _ = _ := by simp [slice]

end Deldor14.MobiusTriples
open Deldor14.MobiusTriples in
theorem OMA.solution : type_of% @OMA.S_oeis_a102309.main := by
  rintro (_|n) hn
  · omega
  · rw [count _ (by omega),step]
    push_cast
    simp
