import SparseSampling
import Doubling

/-! Counting positive-step index progressions of arbitrary length, and
deletion for finite samples with arbitrary joint law. The deletion of
one representative per present edge uses Erdos142SparseSampling.delete_edges. -/

namespace Erdos142AffineSample
open Finset ProgressionParity Set.IsAPOfLengthFree

abbrev Code := Σ _ : ℕ, ℕ

/-- The first coordinate is the remaining distance from the initial index
to b. The second is the positive stride. -/
def keys (k b : ℕ) : Finset Code :=
  (range b).sigma fun t => Icc 1 (t/(k-1))

def edge (k b : ℕ) (c : Code) : Finset ℕ :=
  (range k).image fun i => b-c.1+i*c.2

theorem keys_card (k b : ℕ) : (keys k b).card=∑ t∈range b, t/(k-1) := by
  simp [keys,card_sigma,Nat.card_Icc]

theorem count_bound (k b : ℕ) : 2*(k-1)*(keys k b).card ≤ b*(b-1) := by
  have bound (n : ℕ) : 2*(k-1)*(∑ t∈range n,t/(k-1))+n ≤ n^2 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ]
      nlinarith only [ih,Nat.mul_div_le n (k-1)]
  rw [keys_card]
  cases b with
  | zero => simp
  | succ b =>
    have h := bound (b+1)
    simp only [Nat.add_sub_cancel]
    nlinarith only [h]

private theorem endpoints (k b : ℕ) (c : Code) (hk : 0<k) :
    b-c.1∈edge k b c ∧ b-c.1+(k-1)*c.2∈edge k b c ∧
    ∀ v∈edge k b c, b-c.1≤v ∧ v≤b-c.1+(k-1)*c.2 := by
  refine ⟨mem_image.mpr ⟨0,mem_range.mpr hk,by simp⟩,
    mem_image.mpr ⟨k-1,mem_range.mpr (by omega),rfl⟩,?_⟩
  intro v hv
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
  have i' := mem_range.mp hi
  exact ⟨Nat.le_add_right _ _,Nat.add_le_add_left (Nat.mul_le_mul_right c.2 (by omega)) _⟩

theorem edge_injective {k b : ℕ} (hk : 1<k) :
    (keys k b : Set Code).InjOn (edge k b) := by
  rintro ⟨t,d⟩ hc ⟨u,e⟩ hc' eq
  obtain ⟨l,r,bounds⟩ := endpoints k b ⟨t,d⟩ (by omega)
  obtain ⟨l',r',bounds'⟩ := endpoints k b ⟨u,e⟩ (by omega)
  have start := le_antisymm (bounds _ (eq.symm ▸ l')).1 (bounds' _ (eq ▸ l)).1
  have last := le_antisymm (bounds' _ (eq ▸ r)).2 (bounds _ (eq.symm ▸ r')).2
  have hstart : b-t=b-u := start
  have hlast : b-t+(k-1)*d=b-u+(k-1)*e := last
  rw [hstart] at hlast
  have de := Nat.eq_of_mul_eq_mul_left (by omega : 0<k-1) (Nat.add_left_cancel hlast)
  obtain ⟨ht,_⟩ := mem_sigma.mp hc
  obtain ⟨hu,_⟩ := mem_sigma.mp hc'
  have bt : t<b := mem_range.mp ht
  have bu : u<b := mem_range.mp hu
  have tu : t=u := by omega
  subst u; subst e; rfl

/-- Every code gives exactly k distinct points of [1,b]. -/
theorem valid_key {k b : ℕ} (hk : 1<k) {c : Code} (hc : c∈keys k b) :
    (edge k b c).card=k ∧ edge k b c⊆Icc 1 b := by
  obtain ⟨t,d⟩ := c
  obtain ⟨lo,dd⟩ := mem_sigma.mp hc
  have bt : t<b := mem_range.mp lo
  obtain ⟨dp,cap⟩ := mem_Icc.mp dd
  have dp' : 0<d := dp
  have last : (k-1)*d≤t := by
    rw [Nat.mul_comm]; exact (Nat.le_div_iff_mul_le (by omega : 0<k-1)).mp cap
  constructor
  · rw [edge,card_image_of_injective,card_range]
    intro i j eq
    exact Nat.eq_of_mul_eq_mul_right dp' (Nat.add_left_cancel eq)
  · intro i hi
    obtain ⟨l,r⟩ := (endpoints k b ⟨t,d⟩ (by omega)).2.2 i hi
    change b-t ≤ i at l
    change i≤b-t+(k-1)*d at r
    exact mem_Icc.mpr ⟨by omega,by omega⟩

/-- Exact number of distinct, nonconstant, unordered index progressions. -/
theorem number_of_edges {k b : ℕ} (hk : 1<k) :
    ((keys k b).image (edge k b)).card=∑ t∈range b, t/(k-1) := by
  rw [card_image_of_injOn (edge_injective hk),keys_card]

/-- Removing one sampled index per present edge leaves a genuinely
k-progression-free subset in the one-based interval used by maxCard. -/
theorem sample_size {k b : ℕ} (hk : 1<k) (A : Finset ℕ) (inside : A⊆Icc 1 b) :
    A.card ≤ maxCard k b+((keys k b).filter fun c => edge k b c⊆A).card := by
  classical
  let C := (keys k b).filter fun c => edge k b c⊆A
  let E := C.image (edge k b)
  obtain ⟨T,sub,cost,avoid⟩ := Erdos142SparseSampling.delete_edges A E (by
    intro f hf
    obtain ⟨c,_,rfl⟩ := mem_image.mp hf
    exact ⟨_,(endpoints k b c (by omega)).1⟩)
  have free : Free (·∈T) k := by
    intro a d pos run
    have terms := (run_iff_forall _ _ _ _).mp run
    have base : a∈T := by simpa using terms 0 (by omega)
    have ⟨alo,ahi⟩ := mem_Icc.mp (inside (sub base))
    have last := (mem_Icc.mp (inside (sub (terms (k-1) (by omega))))).2
    let c : Code := ⟨b-a,d⟩
    have key : c∈keys k b := by
      apply mem_sigma.mpr
      refine ⟨mem_range.mpr (by change b-a<b; omega),mem_Icc.mpr ⟨pos,?_⟩⟩
      apply (Nat.le_div_iff_mul_le (by omega : 0<k-1)).mpr
      change d*(k-1)≤b-a
      rw [Nat.mul_comm]; omega
    have covered : edge k b c⊆T := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
      change b-(b-a)+i*d∈T
      rw [show b-(b-a)=a by omega]
      exact terms i (mem_range.mp hi)
    apply avoid (edge k b c) _ covered
    exact mem_image.mpr ⟨c,mem_filter.mpr ⟨key,covered.trans sub⟩,rfl⟩
  exact cost.trans (Nat.add_le_add (bound_witness hk T (sub.trans inside) free) card_image_le)

/-- Probability of an event under a finitely supported joint law. -/
noncomputable def prob {Ω : Type*} (W : Finset Ω) (μ : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E] : ℝ := ∑ w∈W, if E w then μ w else 0

/-- Finite deletion in expectation. Dependence between sites, including
dependence from a random choice of affine embedding, is allowed. -/
theorem weighted_deletion {Ω : Type*} {k b : ℕ} (hk : 1<k)
    (W : Finset Ω) (μ : Ω → ℝ) (weights : ∀ w∈W, 0≤μ w) (total : ∑ w∈W, μ w=1)
    (sample : Ω → Finset ℕ) (inside : ∀ w∈W, sample w⊆Icc 1 b) :
    ∑ i∈Icc 1 b, prob W μ (fun w => i∈sample w) ≤ (maxCard k b:ℝ)+
      ∑ c∈keys k b, prob W μ (fun w => edge k b c⊆sample w) := by
  classical
  let marked (w : Ω) := (keys k b).filter fun c => edge k b c⊆sample w
  have expectS (w) (hw : w∈W) :
      (∑ i∈Icc 1 b, if i∈sample w then μ w else 0)=(sample w).card*μ w := by
    rw [←sum_filter]
    have eq : (Icc 1 b).filter (fun i => i∈sample w) = sample w := by
      ext i
      simp only [mem_filter]
      exact and_iff_right_of_imp fun hi => inside w hw hi
    simp [eq]
  have expectE (w) : (∑ c∈keys k b, if edge k b c⊆sample w then μ w else 0) =
      (marked w).card*μ w := by rw [←sum_filter]; simp [marked]
  have h := sum_le_sum (fun w hw => mul_le_mul_of_nonneg_right
    (show ((sample w).card:ℝ) ≤ (maxCard k b:ℝ)+(marked w).card by
      exact_mod_cast sample_size hk _ (inside w hw)) (weights w hw))
  simp only [prob]
  rw [sum_comm, sum_congr rfl expectS]
  conv_rhs => arg 2; rw [sum_comm]
  simp_rw [expectE]
  simp only [add_mul,sum_add_distrib,←mul_sum,total,mul_one] at h
  exact h

/-- Application to a sampling law with constant one-site marginal and a
uniform bound for the inclusion probability of each index progression. -/
theorem homogeneous {Ω : Type*} {k b : ℕ} (hk : 1<k)
    (W : Finset Ω) (μ : Ω → ℝ) (weights : ∀ w∈W, 0≤μ w) (total : ∑ w∈W, μ w=1)
    (sample : Ω → Finset ℕ) (inside : ∀ w∈W, sample w⊆Icc 1 b)
    (p rate : ℝ) (hrate : 0≤rate)
    (site : ∀ i∈Icc 1 b, prob W μ (fun w => i∈sample w)=p)
    (each : ∀ c∈keys k b, prob W μ (fun w => edge k b c⊆sample w)≤rate) :
    2*(k-1:ℕ)*((b:ℝ)*p-maxCard k b) ≤ (b:ℝ)*(b-1:ℕ)*rate := by
  have h := weighted_deletion hk W μ weights total sample inside
  rw [sum_congr rfl site] at h
  have he := sum_le_sum each
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at h he
  have count : 2*((k-1:ℕ):ℝ)*(keys k b).card ≤ (b:ℝ)*(b-1:ℕ) := by exact_mod_cast count_bound k b
  have s := mul_le_mul_of_nonneg_right count hrate
  have comb := mul_le_mul_of_nonneg_left (h.trans (add_le_add le_rfl he))
    (show 0≤2*((k-1:ℕ):ℝ) by positivity)
  linarith only [s,comb]

/-- Finite affine-sampling conclusion at the survival observable, once
the one-site marginal and the AM–GM bound for each edge are supplied. -/
theorem survival_bound {Ω : Type*} {k b : ℕ} (hk : 1<k)
    (W : Finset Ω) (μ : Ω → ℝ) (weights : ∀ w∈W, 0≤μ w) (total : ∑ w∈W, μ w=1)
    (sample : Ω → Finset ℕ) (inside : ∀ w∈W, sample w⊆Icc 1 b)
    (S d : ℝ) (hs : 0≤S) (hd : 0<d) (window : ((b-1:ℕ):ℝ)≤d)
    (site : ∀ i∈Icc 1 b, prob W μ (fun w => i∈sample w)=S/2)
    (each : ∀ c∈keys k b, prob W μ (fun w => edge k b c⊆sample w)≤
      S/(2*(k:ℝ)*(k-1:ℕ)*Real.exp 1*d)) :
    (b:ℝ)*S*(1-1/(2*(k:ℝ)*(k-1:ℕ)^2*Real.exp 1)) ≤ 2*maxCard k b := by
  have kk : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have km : (0:ℝ)<(k-1:ℕ) := by exact_mod_cast (show 0<k-1 by omega)
  let rate := S/(2*(k:ℝ)*(k-1:ℕ)*Real.exp 1*d)
  have pos : 0≤rate := by dsimp [rate]; positivity
  have h := homogeneous hk W μ weights total sample inside (S/2) rate pos site each
  have gain : (b:ℝ)*(b-1:ℕ)*rate ≤ (b:ℝ)*S/(2*(k:ℝ)*(k-1:ℕ)*Real.exp 1) := by
    calc _ ≤ (b:ℝ)*d*rate := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left window (by positivity)) pos
         _ = _ := by dsimp [rate]; field_simp
  have main := h.trans gain
  field_simp at main ⊢
  linarith only [main]

#print axioms valid_key
#print axioms survival_bound
#print axioms number_of_edges
#print axioms count_bound
#print axioms sample_size
#print axioms weighted_deletion
#print axioms homogeneous
end Erdos142AffineSample
