import Ordinary

namespace ProgressionParity
open Set.IsAPOfLengthFree
open scoped BigOperators
open Filter Topology

lemma portion_bounds {k N : ℕ} (hk : 1<k) (A : Finset ℕ)
    (sub : A ⊆ Finset.Icc 1 N) (fre : Free (· ∈ A) k) {x : ℕ} (hx : x≤N) :
    (A.filter (·≤x)).card ≤ maxCard k x ∧ A.card-(A.filter (·≤x)).card ≤ maxCard k (N-x) := by
  let L := A.filter (·≤x)
  let H := A.filter (fun z => ¬z≤x)
  let T := H.image (·-x)
  have lc : L.card ≤ maxCard k x := by
    apply bound_witness (by omega : 1<k)
    · intro z hz
      obtain ⟨az,high⟩ := Finset.mem_filter.mp hz
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (sub az)).1,high⟩
    · intro a d hd run
      apply fre a d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      exact (Finset.mem_filter.mp ((run_iff_forall _ _ _ _).mp run i hi)).1
  have tc : T.card=H.card := by
    apply Finset.card_image_of_injOn
    intro v hv w hw eq
    have vl := (Finset.mem_filter.mp hv).2
    have wl := (Finset.mem_filter.mp hw).2
    change v-x=w-x at eq
    omega
  have hc : T.card ≤ maxCard k (N-x) := by
    apply bound_witness (by omega : 1<k)
    · intro z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨ax,high⟩ := Finset.mem_filter.mp ha
      have upper := (Finset.mem_Icc.mp (sub ax)).2
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · intro a d hd run
      apply fre (a+x) d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      obtain ⟨z,hz,eq⟩ := Finset.mem_image.mp ((run_iff_forall _ _ _ _).mp run i hi)
      obtain ⟨az,high⟩ := Finset.mem_filter.mp hz
      change z-x=a+i*d at eq
      rwa [show a+x+i*d=z by omega]
  have sum : L.card+H.card=A.card := @Finset.card_filter_add_card_filter_not ℕ A (·≤x) _ _
  refine ⟨lc,?_⟩
  change A.card-L.card ≤ _
  omega

theorem prefix_discrepancy {k N : ℕ} (hk : 3≤k) (hn : 0<N) {ε:ℝ} (good : ¬badEndpoint k N ε)
    (A : Finset ℕ) (sub : A ⊆ Finset.Icc 1 N) (fre : Free (· ∈ A) k) {x : ℕ} (hx : x≤N) :
    |((A.filter (·≤x)).card:ℝ)/maxCard k N-(x:ℝ)/N| ≤
      ε+(1-(A.card:ℝ)/maxCard k N) := by
  let R := (maxCard k N:ℝ)
  have q := interval_mono (by omega : 1<k) (show 1≤N from hn)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at q
  have rp : 0<R := by dsimp [R];exact_mod_cast (show 0<maxCard k N by omega)
  have np : 0<(N:ℝ) := by exact_mod_cast hn
  have ok {y:ℕ} (hy : y≤N) : (maxCard k y:ℝ)/R-(y:ℝ)/N ≤ ε :=
    (abs_le.mp (le_of_not_gt (fun h => good ⟨y,hy,h⟩))).2
  obtain ⟨lc,hc⟩ := portion_bounds (by omega : 1<k) A sub fre hx
  have part := Finset.card_filter_le A (·≤x)
  have cap := bound_witness (by omega : 1<k) A sub fre
  have leR : (A.card:ℝ)/R≤1 := (div_le_one rp).mpr (by dsimp [R]; exact_mod_cast cap)
  have lower : ((A.filter (·≤x)).card:ℝ)/R ≤ (maxCard k x:ℝ)/R :=
    div_le_div_of_nonneg_right (by exact_mod_cast lc) rp.le
  have cc : (A.card:ℝ)-(A.filter (·≤x)).card ≤ (maxCard k (N-x):ℝ) := by
    rw [← Nat.cast_sub part]
    exact_mod_cast hc
  have upper := div_le_div_of_nonneg_right cc rp.le
  rw [sub_div] at upper
  have yl := ok (Nat.sub_le N x)
  rw [Nat.cast_sub hx,sub_div,div_self np.ne'] at yl
  have xl := ok hx
  change |((A.filter (·≤x)).card:ℝ)/R-(x:ℝ)/N| ≤ _
  apply abs_le.mpr
  constructor <;> linarith

def badDistribution (k N : ℕ) (ε:ℝ) : Prop :=
  ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ (A:Set ℕ).IsAPOfLengthFree k ∧
    A.card=maxCard k N ∧ ∃ x≤N, ε < |((A.filter (·≤x)).card:ℝ)/A.card-(x:ℝ)/N|

theorem exceptional_distribution_subset {k N:ℕ} (hk:3≤k) (hn:0<N) {ε:ℝ} :
    badDistribution k N ε → badEndpoint k N ε := by
  rintro ⟨A,ha,fa,eq,x,hx,err⟩
  by_contra good
  have bd := prefix_discrepancy hk hn good A ha ((upstream_iff_free _ (by omega)).mp fa) hx
  have q := interval_mono (by omega : 1<k) (show 1≤N from hn)
  rw [(initial_values (by omega : 1<k)).1 1 (by omega)] at q
  have nz : (maxCard k N:ℝ)≠0 := by exact_mod_cast (show maxCard k N≠0 by omega)
  rw [eq,div_self nz,sub_self,add_zero] at bd
  rw [eq] at err
  exact (not_lt_of_ge bd) err

#print axioms prefix_discrepancy
#print axioms exceptional_distribution_subset
end ProgressionParity
