import Doubling
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

namespace ProgressionParity

private lemma hits_residue {m d : ℕ} (hm : 0 < m) (co : m.Coprime d)
    (a r : ℕ) (hr : r < m) : ∃ i < m, (a+i*d)%m=r := by
  let f : Fin m → Fin m := fun i => ⟨(a+i.val*d)%m, Nat.mod_lt _ hm⟩
  have inj : Function.Injective f := by
    intro i j he
    have he' : a+i.val*d ≡ a+j.val*d [MOD m] := congrArg Fin.val he
    exact Fin.ext ((Nat.ModEq.cancel_right_of_coprime co (he'.add_left_cancel' a)).eq_of_lt_of_lt i.isLt j.isLt)
  obtain ⟨i,hi⟩ := (Finite.injective_iff_surjective.mp inj) ⟨r,hr⟩
  exact ⟨i.val,i.isLt,congrArg Fin.val hi⟩

def block (p : ℕ) (u : ℕ × ℕ) := p*(u.1-1)+u.2+1

lemma block_decode {p x j : ℕ} (hp : 0<p) (hx : 0<x) (hj : j<p) :
    (block p (x,j)-1)/p+1=x ∧ (block p (x,j)-1)%p=j := by
  dsimp [block]
  rw [Nat.mul_add_div hp, Nat.div_eq_of_lt hj, Nat.mul_comm p (x-1), Nat.mul_add_mod_of_lt hj]
  omega

private lemma inflate {p k N : ℕ} (hp : Nat.Prime p) (h : ℕ)
    (hk : p^h ≤ k) (hk' : 1<k) (A : Finset ℕ) (ha : A ⊆ Finset.Icc 1 N)
    (free : Free (· ∈ A) k) :
    p*A.card-(p*A.card)/(p^h) ≤ Set.IsAPOfLengthFree.maxCard k (p*N) := by
  let m := p^h
  have pp := hp.pos
  have mp : 0<m := pow_pos pp h
  let X := (A ×ˢ Finset.range p).image (block p)
  have blockInfo {z : ℕ} (hz : z ∈ X) :
      z ∈ Finset.Icc 1 (p*N) ∧ (z-1)/p+1 ∈ A := by
    obtain ⟨⟨x,j⟩,hx,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hx
    have hr := Finset.mem_range.mp hj
    obtain ⟨xlo,xhi⟩ := Finset.mem_Icc.mp (ha hx)
    have dec := (block_decode pp xlo hr).1
    have le : p*(x-1)+p ≤ p*N := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    exact ⟨Finset.mem_Icc.mpr ⟨by simp [block],by dsimp [block]; omega⟩,dec ▸ hx⟩
  have xc : X.card=p*A.card := by
    dsimp only [X]
    rw [Finset.card_image_of_injOn,Finset.card_product,Finset.card_range,Nat.mul_comm]
    intro u hu v hv eq
    obtain ⟨ux,uj⟩ := Finset.mem_product.mp hu
    obtain ⟨vx,vj⟩ := Finset.mem_product.mp hv
    have du := block_decode pp (Finset.mem_Icc.mp (ha ux)).1 (Finset.mem_range.mp uj)
    have dv := block_decode pp (Finset.mem_Icc.mp (ha vx)).1 (Finset.mem_range.mp vj)
    apply Prod.ext
    · exact du.1.symm.trans ((congrArg (fun z => (z-1)/p+1) eq).trans dv.1)
    · exact du.2.symm.trans ((congrArg (fun z => (z-1)%p) eq).trans dv.2)
  have count : X.card < (Finset.range m).card*(X.card/m+1) := by
    simpa using Nat.lt_mul_div_succ X.card mp
  obtain ⟨r,hr,few⟩ := Finset.exists_card_fiber_lt_of_card_lt_mul (f := fun z : ℕ => z%m) count
  let C := X.filter (fun z => ¬ z%m=r)
  have card := @Finset.card_filter_add_card_filter_not ℕ X (fun z => z%m=r) _ _
  have good : Free (· ∈ C) k := by
    intro a d hd run
    have allp := (run_iff_forall _ _ _ _).mp run
    by_cases hdv : p ∣ d
    · obtain ⟨e,rfl⟩ := hdv
      have first : a ∈ C := by simpa using allp 0 (by omega)
      have a₀ := (Finset.mem_Icc.mp (blockInfo (Finset.mem_filter.mp first).1).1).1
      apply free ((a-1)/p+1) e (by by_contra! he; simp [show e=0 by omega] at hd)
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      have hA := (blockInfo (Finset.mem_filter.mp (allp i hi)).1).2
      have id : a+i*(p*e)-1 = a-1+p*(i*e) := by
        rw [Nat.mul_left_comm i p e]
        omega
      rw [id,Nat.add_mul_div_left _ _ pp] at hA
      rwa [show (a-1)/p+1+i*e=(a-1)/p+i*e+1 by omega]
    · have co : m.Coprime d := (hp.coprime_iff_not_dvd.mpr hdv).pow_left h
      obtain ⟨i,hi,eq⟩ := hits_residue mp co a r (Finset.mem_range.mp hr)
      exact (Finset.mem_filter.mp (allp i (lt_of_lt_of_le hi hk))).2 eq
  have bnd := bound_witness hk' C (fun _ hz => (blockInfo (Finset.mem_filter.mp hz).1).1) good
  change (X.filter (fun z => ¬z%m=r)).card ≤ _ at bnd
  change (X.filter (fun z => z%m=r)).card < X.card/m+1 at few
  change p*A.card-(p*A.card)/m ≤ _
  rw [← xc]
  omega

open Set.IsAPOfLengthFree in
theorem prime_power_dilation {p k : ℕ} (hp : Nat.Prime p) (h : ℕ)
    (hk : p^(h+1) ≤ k) (N : ℕ) :
    p*maxCard k N - maxCard k N / p^h ≤ maxCard k (p*N) := by
  have hp1 : 1 < p^(h+1) := Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨A,ha,hf,he⟩ := attained (by omega : 1<k) N
  have hbound := inflate hp (h+1) hk (by omega) A ha hf
  rwa [he,pow_succ,Nat.mul_comm (p^h) p,Nat.mul_div_mul_left _ _ hp.pos] at hbound

private lemma initial_free {k n : ℕ} (hn : n<k) : Free (· ∈ Finset.Icc 1 n) k := by
  intro a d hd run
  have H := (run_iff_forall _ _ _ _).mp run
  have first : a ∈ Finset.Icc 1 n := by simpa using H 0 (by omega)
  have last := (Finset.mem_Icc.mp (H (k-1) (by omega))).2
  have step : (k-1)*1 ≤ (k-1)*d := Nat.mul_le_mul_left _ hd
  have start := (Finset.mem_Icc.mp first).1
  omega

open Set.IsAPOfLengthFree in
theorem initial_values {k : ℕ} (hk : 1<k) :
    (∀ n < k, maxCard k n=n) ∧ maxCard k k=k-1 := by
  constructor
  · intro n hn
    obtain ⟨A,ha,_,he⟩ := attained hk n
    have upper := Finset.card_le_card ha
    have lower := bound_witness hk (Finset.Icc 1 n) (Finset.Subset.refl _) (initial_free hn)
    simp only [Nat.card_Icc] at lower upper
    omega
  · obtain ⟨A,ha,hf,he⟩ := attained hk k
    have ne : A ≠ Finset.Icc 1 k := by
      intro eq
      apply hf 1 1 (by decide)
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      rw [eq,Finset.mem_Icc]
      omega
    have upper := Finset.card_lt_card (ssubset_of_subset_of_ne ha ne)
    have lower := bound_witness hk (Finset.Icc 1 (k-1))
      (Finset.Icc_subset_Icc_right (by omega : k-1≤k)) (initial_free (by omega))
    simp only [Nat.card_Icc] at upper lower
    omega

open Set.IsAPOfLengthFree in
theorem prime_power_sharp {p : ℕ} (hp : Nat.Prime p) (h : ℕ) :
    let k := p^(h+1)
    let N := p^h
    maxCard k N=N ∧ maxCard k (p*N)=p*N-1 := by
  dsimp
  have one : 1<p^(h+1) := Nat.one_lt_pow (by omega) hp.one_lt
  have smaller : p^h<p^(h+1) := by
    rw [pow_succ]
    simpa using Nat.mul_lt_mul_of_pos_left hp.one_lt (pow_pos hp.pos h)
  have sides := initial_values one
  exact ⟨sides.1 _ smaller,by simpa only [pow_succ,Nat.mul_comm p (p^h)] using sides.2⟩

#print axioms prime_power_dilation
#print axioms prime_power_sharp
end ProgressionParity
