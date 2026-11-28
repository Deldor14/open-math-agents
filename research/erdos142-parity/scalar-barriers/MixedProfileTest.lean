import Mathlib

/-! Finite-atom tests for heterogeneous scalar profile inequalities. The
inverse P is taken at the right endpoint of each level of G. The limiting
criterion uses convergence of binary sums and does not assume P continuous. -/

namespace Erdos142MixedProfile
open Finset Set Filter Topology

/-- Cost evaluated at the target coordinate t=Lx. -/
noncomputable def cost {ι : Type*} (I : Finset ι) (a b : ι → ℝ) (G : ℝ → ℝ)
    (L t : ℝ) : ℝ := ∑ i ∈ I, b i*G (a i*(t/L))

section Mixed
variable {ι : Type*} {I : Finset ι} {a b : ι → ℝ} {G P : ℝ → ℝ} {L : ℝ}

theorem cost_scale (hL : 0 < L) (x : ℝ) :
    cost I a b G L (L*x) = ∑ i ∈ I, b i*G (a i*x) := by
  unfold cost
  rw [show L*x/L=x by field_simp]

theorem cost_mono (hL : 0 < L) (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (mono : MonotoneOn G (Ici 0)) : MonotoneOn (cost I a b G L) (Ici 0) := by
  intro x hx y hy h
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hb i hi)
  exact mono (mul_nonneg (ha i hi) (div_nonneg hx hL.le))
    (mul_nonneg (ha i hi) (div_nonneg hy hL.le))
    (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h hL.le) (ha i hi))

theorem cost_sub (hL : 0 < L) (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, G (x+y) ≤ G x+G y) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cost I a b G L (x+y) ≤ cost I a b G L x+cost I a b G L y := by
  unfold cost
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro i hi
  rw [add_div, mul_add (a i), ← mul_add (b i)]
  exact mul_le_mul_of_nonneg_left (sub _ (mul_nonneg (ha i hi) (div_nonneg hx hL.le)) _
    (mul_nonneg (ha i hi) (div_nonneg hy hL.le))) (hb i hi)

theorem small_remainder (hL : 0 < L) (ha : ∀ i ∈ I, 0 ≤ a i)
    (hb : ∀ i ∈ I, 0 ≤ b i) (linear : ∀ x ≥ 0, G x ≤ x)
    (budget : (∑ i ∈ I, b i*a i) ≤ L) {v : ℝ} (hv : 0 ≤ v) :
    cost I a b G L v ≤ v := by
  have frac := div_nonneg hv hL.le
  calc cost I a b G L v ≤ ∑ i ∈ I, b i*(a i*(v/L)) :=
         sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (linear _ (mul_nonneg (ha i hi) frac)) (hb i hi))
       _ = (∑ i ∈ I, b i*a i)*(v/L) := by rw [sum_mul];simp only [mul_assoc]
       _ ≤ L*(v/L) := mul_le_mul_of_nonneg_right budget frac
       _ = v := by field_simp

end Mixed

/-- Summing any finite list of valid atoms, starting from a valid remainder. -/
theorem add_atoms {H P : ℝ → ℝ} {D : Set ℝ}
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, H (x+y) ≤ H x+H y)
    (pos : ∀ d ∈ D, 0 ≤ P d) (test : ∀ d ∈ D, H (P d) ≤ d)
    (word : List ℝ) (valid : ∀ d ∈ word, d ∈ D) {v : ℝ} (hv : 0 ≤ v) (rem : H v ≤ v) :
    H ((word.map P).sum+v) ≤ word.sum+v := by
  induction word with
  | nil => simpa using rem
  | cons d rest ih =>
    have hd := valid d (by simp)
    have tail (r) (hr : r ∈ rest) := valid r (List.mem_cons_of_mem _ hr)
    have spos : 0 ≤ (rest.map P).sum := List.sum_nonneg (fun y hy => by
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hy
      exact pos r (tail r hr))
    simp only [List.map_cons,List.sum_cons,add_assoc]
    exact (sub _ (pos d hd) _ (add_nonneg spos hv)).trans (add_le_add (test d hd) (ih tail))

section Finite
variable {ι : Type*} {I : Finset ι} {a b : ι → ℝ} {G P : ℝ → ℝ} {L : ℝ}

/-- Equivalence for a finite-atom expansion plus a remainder in [0,1).
D can in particular be the finite set of allowed powers of two. -/
theorem finite_test {D : Set ℝ} (hL : 0 < L)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (mono : MonotoneOn G (Ici 0)) (sub : ∀ x ≥ 0, ∀ y ≥ 0, G (x+y) ≤ G x+G y)
    (zero : G 0=0) (linear : ∀ x ≥ 0, G x ≤ x) (budget : (∑ i ∈ I, b i*a i) ≤ L)
    (right : ∀ x ≥ 0, x ≤ P (G x)) (inv : ∀ d ∈ D, 0 ≤ P d ∧ G (P d)=d)
    (unit : ∀ v ∈ Set.Ico (0:ℝ) 1, P v=v)
    (decomp : ∀ (t : ℝ), 0 ≤ t → ∃ (word : List ℝ) (v : ℝ),
      (∀ d ∈ word, d ∈ D) ∧ v ∈ Set.Ico 0 1 ∧ word.sum+v=t ∧ (word.map P).sum+P v=P t) :
    (∀ x ≥ 0, (∑ i ∈ I, b i*G (a i*x)) ≤ G (L*x)) ↔
      ∀ d ∈ D, cost I a b G L (P d) ≤ d := by
  constructor
  · intro all d hd
    have h := all (P d/L) (div_nonneg (inv d hd).1 hL.le)
    rwa [show L*(P d/L)=P d by field_simp,(inv d hd).2] at h
  · intro test x hx
    have xp := mul_nonneg hL.le hx
    have gp : 0 ≤ G (L*x) := by
      rw [←zero]
      exact mono (by simp) xp xp
    obtain ⟨word,v,valid,hv,total,upper⟩ := decomp (G (L*x)) gp
    rw [unit v hv] at upper
    have bound := add_atoms (fun _ h _ h' => cost_sub hL ha hb sub h h')
      (fun d hd => (inv d hd).1) test word valid hv.1 (small_remainder hL ha hb linear budget hv.1)
    rw [upper,total] at bound
    have ix := right _ xp
    rw [←cost_scale (I := I) (a := a) (b := b) (G := G) hL x]
    exact (cost_mono hL ha hb mono xp (xp.trans ix) ix).trans bound

end Finite

/-- Dyadic homogeneity transports the unit test to every integral power of two. -/
theorem golden_atom {ι : Type*} {I : Finset ι} {a b : ι → ℝ} {G P : ℝ → ℝ} {L q : ℝ}
    (hL : 0 < L) (ha : ∀ i ∈ I, 0 ≤ a i) (p1 : 0 ≤ P 1)
    (pdyad : ∀ k : ℤ, P ((2 : ℝ)^k) = q^k * P 1)
    (gdyad : ∀ (k : ℤ) (x : ℝ), 0 ≤ x → G (q^k*x) = (2:ℝ)^k * G x)
    (unit : cost I a b G L (P 1) ≤ 1) (k : ℤ) :
    cost I a b G L (P ((2:ℝ)^k)) ≤ (2:ℝ)^k := by
  have eq : cost I a b G L (P ((2:ℝ)^k)) = (2:ℝ)^k * cost I a b G L (P 1) := by
    unfold cost
    rw [pdyad, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show a i*(q^k*P 1/L) = q^k*(a i*(P 1/L)) by ring,
      gdyad k _ (mul_nonneg (ha i hi) (div_nonneg p1 hL.le))]
    ring
  rw [eq]
  simpa using mul_le_mul_of_nonneg_left unit (show 0 ≤ (2:ℝ)^k by positivity)

/-- Infinite expansions are handled by finite prefixes. Only the cost needs
continuity on the positive ray; the two convergence hypotheses concern the
partial sums themselves. -/
theorem atomic_limit {H P : ℝ → ℝ} {D : Set ℝ}
    (sub : ∀ x ≥ 0, ∀ y ≥ 0, H (x+y) ≤ H x+H y)
    (pos : ∀ d ∈ D, 0 ≤ P d) (test : ∀ d ∈ D, H (P d) ≤ d)
    (zero : H 0 = 0) (cont : ContinuousOn H (Ici 0)) {t : ℝ} (pt : 0 ≤ P t)
    (words : ℕ → List ℝ) (valid : ∀ n d, d ∈ words n → d ∈ D)
    (ht : Tendsto (fun n => (words n).sum) atTop (𝓝 t))
    (hp : Tendsto (fun n => ((words n).map P).sum) atTop (𝓝 (P t))) :
    H (P t) ≤ t := by
  have wpos (n : ℕ) : 0 ≤ ((words n).map P).sum := List.sum_nonneg (fun y hy => by
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hy
    exact pos d (valid n d hd))
  have hg := (cont _ pt).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hp, Eventually.of_forall wpos⟩)
  apply le_of_tendsto_of_tendsto' hg ht
  intro n
  simpa using add_atoms sub pos test (words n) (valid n) (v := 0) (by simp) zero.le

/-- On a dyadically homogeneous profile with convergent binary expansions, a
single evaluation of the mixed cost at the right endpoint of level one is
necessary and sufficient. Exponents are integral and may be negative. -/
theorem golden_test {ι : Type*} {I : Finset ι} {a b : ι → ℝ} {G P : ℝ → ℝ} {L q : ℝ}
    (hL : 0 < L) (hq : 0 < q) (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i)
    (mono : MonotoneOn G (Ici 0)) (sub : ∀ x ≥ 0, ∀ y ≥ 0, G (x+y) ≤ G x+G y)
    (cont : ContinuousOn G (Ici 0)) (zero : G 0 = 0)
    (right : ∀ x ≥ 0, x ≤ P (G x)) (p1 : 0 ≤ P 1) (one : G (P 1) = 1)
    (pdyad : ∀ k : ℤ, P ((2 : ℝ)^k) = q^k * P 1)
    (gdyad : ∀ (k : ℤ) (x : ℝ), 0 ≤ x → G (q^k*x) = (2:ℝ)^k * G x)
    (expansion : ∀ t : ℝ, 0 ≤ t → ∃ words : ℕ → List ℤ,
      Tendsto (fun n => ((words n).map (fun k => (2:ℝ)^k)).sum) atTop (𝓝 t) ∧
      Tendsto (fun n => ((words n).map (fun k => P ((2:ℝ)^k))).sum) atTop (𝓝 (P t))) :
    (∀ x ≥ 0, (∑ i ∈ I, b i*G (a i*x)) ≤ G (L*x)) ↔ cost I a b G L (P 1) ≤ 1 := by
  constructor
  · intro rule
    have h := rule (P 1/L) (div_nonneg p1 hL.le)
    rwa [show L*(P 1/L)=P 1 by field_simp,one] at h
  · intro unit x hx
    have xp := mul_nonneg hL.le hx
    have gp : 0 ≤ G (L*x) := by
      rw [←zero]
      exact mono (by simp) xp xp
    obtain ⟨words,ht,hp⟩ := expansion _ gp
    have ix := right _ xp
    rw [←cost_scale (I := I) (a := a) (b := b) (G := G) hL x]
    apply (cost_mono hL ha hb mono xp (xp.trans ix) ix).trans
    refine atomic_limit (D := Set.range (fun k : ℤ => (2:ℝ)^k))
      (fun _ h _ h' => cost_sub hL ha hb sub h h') ?_ ?_ ?_ ?_ (xp.trans ix)
      (fun n => (words n).map (fun k => (2:ℝ)^k)) ?_ ht ?_
    · rintro _ ⟨k,rfl⟩
      rw [pdyad]
      exact mul_nonneg (zpow_nonneg hq.le _) p1
    · rintro _ ⟨k,rfl⟩
      exact golden_atom hL ha p1 pdyad gdyad unit k
    · simp [cost,zero]
    · unfold cost
      refine continuousOn_finsetSum _ fun i hi => continuousOn_const.mul ?_
      exact cont.comp (continuousOn_const.mul (continuousOn_id.div_const L))
        (fun _ h => mul_nonneg (ha i hi) (div_nonneg h hL.le))
    · intro n d hd
      obtain ⟨k,_,rfl⟩ := List.mem_map.mp hd
      exact ⟨k,rfl⟩
    · simpa only [List.map_map,Function.comp_def] using hp

#print axioms finite_test
#print axioms golden_atom
#print axioms atomic_limit
#print axioms golden_test

end Erdos142MixedProfile
