import Distribution

namespace ProgressionParity
open Set.IsAPOfLengthFree
open scoped BigOperators

def hits (A : Finset ℕ) (s d L : ℕ) : ℕ :=
  ((Finset.range L).filter (fun i => s+i*d ∈ A)).card

theorem hits_upper {k : ℕ} (hk : 3≤k) (A:Finset ℕ) (fa : Free (· ∈ A) k)
    (s L : ℕ) {d : ℕ} (hd : 0<d) : hits A s d L≤maxCard k L := by
  let S := (Finset.range L).filter (fun i => s+i*d∈A)
  let T := S.image (·+1)
  have eq : T.card=S.card := Finset.card_image_of_injective _ (fun x y h => by change x+1=y+1 at h;omega)
  have sub : T ⊆ Finset.Icc 1 L := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    have lt := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have free : Free (· ∈ T) k := by
    intro a e he run
    have H := (run_iff_forall _ _ _ _).mp run
    have first : a∈T := by simpa using H 0 (by omega)
    have lo := (Finset.mem_Icc.mp (sub first)).1
    apply fa (s+(a-1)*d) (e*d) (Nat.mul_pos he hd)
    apply (run_iff_forall _ _ _ _).mpr
    intro i hi
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp (H i hi)
    have member := (Finset.mem_filter.mp hj).2
    change j+1=a+i*e at ej
    have jEq : j=a-1+i*e := by omega
    rw [jEq,Nat.add_mul] at member
    simpa only [Nat.add_assoc,Nat.mul_assoc] using member
  have b := bound_witness (by omega : 1<k) T sub free
  rwa [eq] at b

private lemma interval_card (A:Finset ℕ) {a b:ℕ} (ab : a≤b) :
    (A.filter (·≤a)).card+(A.filter (fun x => a<x ∧ x≤b)).card=(A.filter (·≤b)).card := by
  let D := A.filter (·≤b)
  have p := @Finset.card_filter_add_card_filter_not ℕ D (·≤a) _ _
  have lo : D.filter (·≤a)=A.filter (·≤a) := by
    ext x
    simp only [D,Finset.mem_filter]
    constructor
    · grind
    · grind
  have hi : D.filter (fun z => ¬z≤a)=A.filter (fun x => a<x ∧ x≤b) := by
    ext x
    simp only [D,Finset.mem_filter]
    constructor
    · grind
    · grind
  rwa [lo,hi] at p

theorem interval_discrepancy {k N : ℕ} (hk : 3≤k) (hn : 0<N) {ε:ℝ} (good : ¬badEndpoint k N ε)
    (A:Finset ℕ) (sub : A⊆Finset.Icc 1 N) (fa : Free (· ∈ A) k) (extreme : A.card=maxCard k N)
    {a b:ℕ} (ab : a≤b) (bN : b≤N) :
    |((A.filter (fun x => a<x ∧ x≤b)).card:ℝ)/maxCard k N-((b-a:ℕ):ℝ)/N| ≤ 2*ε := by
  have lo := prefix_discrepancy hk hn good A sub fa (ab.trans bN)
  have hi := prefix_discrepancy hk hn good A sub fa bN
  have q := interval_mono (by omega : 1<k) (show 1≤N from hn)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at q
  have nz : (maxCard k N:ℝ)≠0 := by exact_mod_cast (show maxCard k N≠0 by omega)
  rw [extreme,div_self nz,sub_self,add_zero] at lo hi
  have card := congrArg (fun t:ℕ => (t:ℝ)) (interval_card A ab)
  simp only [Nat.cast_add] at card
  have quot := congrArg (·/(maxCard k N:ℝ)) card
  simp only [add_div] at quot
  rw [Nat.cast_sub ab,sub_div]
  have ll := abs_le.mp lo
  have hh := abs_le.mp hi
  apply abs_le.mpr
  constructor <;> linarith

private lemma tile_count (A:Finset ℕ) (s g : ℕ) {d:ℕ} (hd : 0<d) :
    (A.filter (fun z => s≤z ∧ z<s+g*d)).card =
      ∑ r ∈ Finset.range d, hits A (s+r) d g := by
  let Q := A.filter (fun z => s≤z ∧ z<s+g*d)
  let f := fun z:ℕ => (z-s)%d
  have split : Q.card = ∑ r ∈ Finset.range d, (Q.filter (fun z => f z=r)).card :=
    Finset.card_eq_sum_card_fiberwise (fun z _ => Finset.mem_range.mpr (Nat.mod_lt (z-s) hd))
  apply split.trans
  apply Finset.sum_congr rfl
  intro r hr
  have lr := Finset.mem_range.mp hr
  let S := (Finset.range g).filter (fun i => s+r+i*d∈A)
  have eq : Q.filter (fun z => f z=r) = S.image (fun i => s+r+i*d) := by
    ext z
    constructor
    · intro hz
      obtain ⟨zQ,rem⟩ := Finset.mem_filter.mp hz
      obtain ⟨zA,lo,hi⟩ := Finset.mem_filter.mp zQ
      change (z-s)%d=r at rem
      have div := Nat.mod_add_div (z-s) d
      rw [rem,Nat.mul_comm d _] at div
      have iL : (z-s)/d < g := (Nat.div_lt_iff_lt_mul hd).mpr (by omega)
      have id : s+r+((z-s)/d)*d=z := by omega
      exact Finset.mem_image.mpr ⟨(z-s)/d,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr iL,by simpa only [id] using zA⟩,id⟩
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨irange,imem⟩ := Finset.mem_filter.mp hi
      have ig := Finset.mem_range.mp irange
      have mul : i*d+d≤g*d := by rw [← Nat.succ_mul];exact Nat.mul_le_mul_right d ig
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨imem,by omega,by omega⟩,?_⟩
      change (s+r+i*d-s)%d=r
      rw [show s+r+i*d-s=i*d+r by omega,Nat.mul_add_mod_of_lt lr]
  rw [eq,Finset.card_image_of_injective]
  · rfl
  · intro i j h
    change s+r+i*d=s+r+j*d at h
    exact Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel h)

private lemma hits_mono (A:Finset ℕ) (s d : ℕ) {u v : ℕ} (h : u≤v) :
    hits A s d u ≤ hits A s d v := by
  apply Finset.card_le_card
  exact Finset.filter_subset_filter _ (Finset.range_mono h)

private lemma tile_majorant {k:ℕ} (hk : 3≤k) (A:Finset ℕ) (fa : Free (· ∈ A) k)
    (s g e:ℕ) :
    (A.filter (fun z => s≤z ∧ z<s+g*(e+1))).card ≤
      hits A s (e+1) (g+1) + e*maxCard k g := by
  rw [tile_count A s g (by omega : 0<e+1),Finset.sum_range_succ']
  have upper : ∑ j ∈ Finset.range e, hits A (s+(j+1)) (e+1) g ≤ ∑ _j ∈ Finset.range e, maxCard k g :=
    Finset.sum_le_sum fun j _ => hits_upper hk A fa _ _ (by omega)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.add_zero] at upper ⊢
  have other := hits_mono A s (e+1) (by omega : g≤g+1)
  omega

theorem progression_discrepancy {k N:ℕ} (hk : 3≤k) (hn : 0<N) {ε:ℝ} (good : ¬badEndpoint k N ε)
    (A:Finset ℕ) (ha : A⊆Finset.Icc 1 N) (fa : Free (· ∈ A) k) (extreme : A.card=maxCard k N)
    {s d g:ℕ} (start : 1≤s) (step : 0<d) (fits : s+g*d≤N) :
    |(hits A s d (g+1):ℝ)/maxCard k N-((g+1:ℕ):ℝ)/N| ≤ ((d:ℝ)+1)*ε+1/(N:ℝ) := by
  obtain ⟨e,rfl⟩ := Nat.exists_eq_succ_of_ne_zero step.ne'
  change s+g*(e+1)≤N at fits
  let R := (maxCard k N:ℝ)
  have q := interval_mono (by omega : 1<k) (show 1≤N from hn)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at q
  have rp : 0<R := by dsimp [R];exact_mod_cast (show 0<maxCard k N by omega)
  have np : 0<(N:ℝ) := by exact_mod_cast hn
  have mul : g≤g*(e+1) := by rw [Nat.mul_succ];omega
  have rates {v:ℕ} (hN : v≤N) : (maxCard k v:ℝ)/R-(v:ℝ)/N≤ε :=
    (abs_le.mp (le_of_not_gt (fun h => good ⟨v,hN,h⟩))).2
  have nonneg : 0≤ε := by
    have ok : |(maxCard k N:ℝ)/R-(N:ℝ)/N|≤ε := le_of_not_gt (fun h => good ⟨N,le_rfl,h⟩)
    exact (abs_nonneg _).trans ok
  have fullrate := rates (show g+1≤N by omega)
  have fullupper := div_le_div_of_nonneg_right (show (hits A s (e+1) (g+1):ℝ) ≤ maxCard k (g+1) by
    exact_mod_cast hits_upper hk A fa s (g+1) (by omega : 0<e+1)) rp.le
  have interval := interval_discrepancy hk hn good A ha fa extreme
    (a :=s-1) (b:=s+g*(e+1)-1) (by omega) (by omega)
  have ident : A.filter (fun z => s-1<z ∧ z≤s+g*(e+1)-1)=A.filter (fun z => s≤z ∧ z<s+g*(e+1)) := by
    ext z
    simp only [Finset.mem_filter]
    constructor <;> grind
  rw [ident,show s+g*(e+1)-1-(s-1)=g*(e+1) by omega,Nat.cast_mul,Nat.cast_add_one] at interval
  have lo := (abs_le.mp interval).1
  have major := tile_majorant hk A fa s g e
  have scaled : ((A.filter (fun z => s≤z ∧ z<s+g*(e+1))).card:ℝ)/R ≤
      ((hits A s (e+1) (g+1):ℝ)+(e:ℝ)*maxCard k g)/R :=
    div_le_div_of_nonneg_right (by exact_mod_cast major) rp.le
  rw [add_div,mul_div_assoc] at scaled
  have grate := rates (show g≤N by omega)
  have extra := mul_le_mul_of_nonneg_left grate (Nat.cast_nonneg e (α := ℝ))
  change |(hits A s (e+1) (g+1):ℝ)/R-((g+1:ℕ):ℝ)/N| ≤ _
  change -(2*ε) ≤ ((A.filter (fun z => s≤z ∧ z<s+g*(e+1))).card:ℝ)/R-
      (g:ℝ)*((e:ℝ)+1)/N at lo
  simp only [Nat.cast_add_one] at fullrate ⊢
  apply abs_le.mpr
  constructor
  · simp only [div_eq_mul_inv] at lo scaled extra ⊢
    linarith only [lo,scaled,extra]
  · have z := mul_nonneg (Nat.cast_nonneg e (α := ℝ)) nonneg
    have o : 0≤1/(N:ℝ) := by positivity
    linarith only [fullrate,fullupper,z,nonneg,o]

theorem all_steps_discrepancy {k N:ℕ} (hk : 3≤k) (hn : 0<N) {ε:ℝ} (good : ¬badEndpoint k N ε)
    (A:Finset ℕ) (ha : A⊆Finset.Icc 1 N) (fa : Free (· ∈ A) k) (extreme : A.card=maxCard k N)
    {s d g D:ℕ} (start : 1≤s) (step : 0<d) (fits : s+g*d≤N) (cutoff : 0<D) :
    |(hits A s d (g+1):ℝ)/maxCard k N-((g+1:ℕ):ℝ)/N| ≤
      ((D:ℝ)+1)*ε+1/(D:ℝ)+1/(N:ℝ) := by
  have np : 0<(N:ℝ) := by exact_mod_cast hn
  have dp : 0<(D:ℝ) := by exact_mod_cast cutoff
  have nonneg : 0≤ε := (abs_nonneg _).trans (le_of_not_gt (fun h => good ⟨N,le_rfl,h⟩))
  have zeroD : 0≤1/(D:ℝ) := by positivity
  by_cases small : d≤D
  · have cmp := mul_le_mul_of_nonneg_right (show (d:ℝ)+1≤D+1 by exact_mod_cast Nat.succ_le_succ small) nonneg
    exact (progression_discrepancy hk hn good A ha fa extreme start step fits).trans (by linarith)
  · have bin : g≤g*d := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left g step
    have hN : g+1≤N := by omega
    have upper := hits_upper hk A fa s (g+1) step
    have emp := div_le_div_of_nonneg_right (show (hits A s d (g+1):ℝ)≤maxCard k (g+1) by exact_mod_cast upper)
      (Nat.cast_nonneg (maxCard k N) (α := ℝ))
    have p : |(maxCard k (g+1):ℝ)/maxCard k N-((g+1:ℕ):ℝ)/N|≤ε :=
      le_of_not_gt (fun h => good ⟨g+1,hN,h⟩)
    have gD := (Nat.mul_le_mul_left g (show D≤d by omega)).trans (show g*d≤N by omega)
    have ratio : (g:ℝ)/N≤1/(D:ℝ) := (div_le_div_iff₀ np dp).mpr (by simpa only [one_mul] using
      (show (g:ℝ)*D≤N by exact_mod_cast gD))
    have en : 0≤(D:ℝ)*ε := mul_nonneg dp.le nonneg
    have nn : 0≤(hits A s d (g+1):ℝ)/maxCard k N := by positivity
    have un : 0≤1/(N:ℝ) := by positivity
    apply abs_le.mpr
    constructor
    · rw [Nat.cast_add_one,add_div]
      linarith only [nn,ratio,en,nonneg]
    · linarith only [(abs_le.mp p).2,emp,en,zeroD,un]

def badAPDistribution (k N : ℕ) (ε:ℝ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ (A:Set ℕ).IsAPOfLengthFree k ∧
    A.card=maxCard k N ∧ ∃ s d g : ℕ, 1≤s ∧ 0<d ∧ s+g*d≤N ∧
      ε < |(hits A s d (g+1):ℝ)/A.card-((g+1:ℕ):ℝ)/N|

theorem AP_exceptional_subset {ε:ℝ} (he : 0<ε) :
    ∃ D:ℕ, 0<D ∧ ∃ δ:ℝ, 0<δ ∧ ∀ k:ℕ, 3≤k → ∀ N:ℕ, D≤N →
      badAPDistribution k N ε → badEndpoint k N δ := by
  obtain ⟨D,hD⟩ := exists_nat_gt (4/ε)
  have pos : 0<(D:ℝ) := (by positivity : 0<4/ε).trans hD
  have dp : 0<D := by exact_mod_cast pos
  let δ := ε/(4*((D:ℝ)+1))
  have pd : 0<δ := by dsimp [δ];positivity
  refine ⟨D,dp,δ,pd,?_⟩
  intro k hk N hN old
  obtain ⟨A,ha,fa,eq,s,d,g,hs,hd,fits,bad⟩ := old
  by_contra good
  have npos : 0<N := by omega
  have bnd := all_steps_discrepancy hk npos good A ha ((upstream_iff_free _ (by omega)).mp fa) eq hs hd fits dp
  have frac : 1/(N:ℝ)≤1/(D:ℝ) := by apply one_div_le_one_div_of_le pos;exact_mod_cast hN
  have four := (div_lt_iff₀ he).mp hD
  have third : 1/(D:ℝ)<ε/4 := by apply (div_lt_iff₀ pos).mpr;linarith only [four]
  have exactD : ((D:ℝ)+1)*δ=ε/4 := by dsimp [δ];field_simp
  rw [exactD] at bnd
  rw [eq] at bad
  linarith only [bnd,frac,third,bad,he]

#print axioms progression_discrepancy
#print axioms all_steps_discrepancy
#print axioms AP_exceptional_subset
end ProgressionParity
