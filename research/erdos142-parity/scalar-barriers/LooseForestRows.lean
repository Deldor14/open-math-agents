import Mathlib

/-! Private coordinates in a ternary loose forest. A new triple meets the
previous vertex set in at most one vertex. Subfamilies may be disconnected. -/

namespace Erdos142LooseForest
open Finset
variable {V : Type*} [DecidableEq V]

def vertices (E : Finset (Finset V)) := E.biUnion id

private theorem contains {E : Finset (Finset V)} {e} (he : e∈E) : e ⊆ vertices E :=
  fun _ hv => mem_biUnion.mpr ⟨e,he,hv⟩

private theorem vertices_mono {A E : Finset (Finset V)} (h : A⊆E) : vertices A⊆vertices E := by
  intro v hv
  obtain ⟨e,he,hv⟩ := mem_biUnion.mp hv
  exact contains (h he) hv

inductive Forest : Finset (Finset V) → Prop
  | empty : Forest ∅
  | attach {E : Finset (Finset V)} (tree : Forest E) (e : Finset V)
      (three : e.card=3) (meet : (e ∩ vertices E).card ≤ 1) : Forest (insert e E)

theorem Forest.arity {E : Finset (Finset V)} (tree : Forest E) : ∀ e∈E, e.card=3 := by
  induction tree with
  | empty => simp
  | attach _ e three _ ih =>
    intro f hf
    rcases mem_insert.mp hf with rfl | hi
    · exact three
    · exact ih f hi

/-- This applies to every nonempty collection of rows, even if other edges
of the original rooted tree have been removed. -/
theorem Forest.vertex_bound {E : Finset (Finset V)} (tree : Forest E)
    {S : Finset (Finset V)} (sub : S⊆E) (ne : S.Nonempty) : 2*S.card+1 ≤ (vertices S).card := by
  induction tree generalizing S with
  | empty => exact (ne.ne_empty (subset_empty.mp sub)).elim
  | @attach E tree e three meet ih =>
    by_cases he : e∈S
    · let T := S.erase e
      have small : T⊆E := by
        intro f hf
        obtain ⟨fe,fs⟩ := mem_erase.mp hf
        exact (mem_insert.mp (sub fs)).resolve_left fe
      have back : insert e T=S := insert_erase he
      have union : vertices S=e ∪ vertices T := by
        calc vertices S=vertices (insert e T) := congrArg vertices back.symm
             _ = _ := by simp [vertices]
      have part : (e∩vertices T).card≤1 := (card_le_card (fun _ hv =>
        mem_inter.mpr ⟨(mem_inter.mp hv).1, vertices_mono small (mem_inter.mp hv).2⟩)).trans meet
      have total := card_union_add_card_inter e (vertices T)
      have sizes : T.card+1=S.card := card_erase_add_one he
      rw [union]
      by_cases nt : T.Nonempty
      · have b := ih small nt
        omega
      · have eq := not_nonempty_iff_eq_empty.mp nt
        simp [eq,vertices] at total sizes ⊢
        omega
    · apply ih (fun f hf => (mem_insert.mp (sub hf)).resolve_left (by rintro rfl; exact he hf)) ne

def incident (E : Finset (Finset V)) (v : V) := E.filter (fun e => v∈e)
def privateVertices (E : Finset (Finset V)) := (vertices E).filter (fun v => (incident E v).card=1)

/-- If |V| ≥ 2|E|+c, at least |E|+2c vertices occur in just one edge. -/
theorem private_count (E : Finset (Finset V)) (c : ℕ) (arity : ∀ e∈E, e.card=3)
    (lower : 2*E.card+c≤(vertices E).card) : E.card+2*c≤(privateVertices E).card := by
  classical
  have sumDeg : ∑ v∈vertices E, (incident E v).card = 3*E.card := by
    have dbl := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s:=E) (t:=vertices E) (fun (e : Finset V) (v : V) => v∈e)
    change _ = ∑ v∈vertices E, (incident E v).card at dbl
    rw [←dbl]
    calc _ = ∑ _e∈E, 3 := by
            apply sum_congr rfl
            intro e he
            have filt : ((vertices E).bipartiteAbove (fun (e : Finset V) v => v∈e) e)=e := by
              ext v
              simpa only [mem_bipartiteAbove] using and_iff_right_of_imp (contains he (x:=v))
            rw [filt,arity e he]
         _ = _ := by simp [Nat.mul_comm]
  have inequality : ∑ v∈vertices E, 2 ≤ ∑ v∈vertices E,
      ((incident E v).card + if (incident E v).card=1 then 1 else 0) := by
    apply sum_le_sum
    intro v hv
    obtain ⟨e,he,ev⟩ := mem_biUnion.mp hv
    have pos : 0<(incident E v).card := card_pos.mpr ⟨e,mem_filter.mpr ⟨he,ev⟩⟩
    split <;> omega
  rw [sum_add_distrib, sumDeg] at inequality
  have count : ∑ v∈vertices E, (if (incident E v).card=1 then 1 else 0) =
      (privateVertices E).card := by simp [privateVertices]
  rw [count] at inequality
  simp only [sum_const,smul_eq_mul] at inequality
  omega

/-- Nonzero entries in private columns survive every linear combination
whose chosen row coefficients are all nonzero. -/
theorem support_bound {𝕜 : Type*} [Field 𝕜] [DecidableEq 𝕜] {E S : Finset (Finset V)} (tree : Forest E)
    (sub : S⊆E) (ne : S.Nonempty) (row : Finset V → V → 𝕜) (a : Finset V → 𝕜)
    (coeff : ∀ e∈S, a e≠0) (supp : ∀ e∈S, ∀ v, row e v≠0 ↔ v∈e) :
    S.card+2 ≤ ((vertices S).filter (fun v => ∑ e∈S, a e*row e v≠0)).card := by
  classical
  have num := private_count S 1 (fun e he => tree.arity e (sub he)) (tree.vertex_bound sub ne)
  refine num.trans (card_le_card ?_)
  intro v hv
  obtain ⟨vS,uniq⟩ := mem_filter.mp hv
  obtain ⟨e,onlyE⟩ := card_eq_one.mp uniq
  have mem (f : Finset V) : f∈incident S v ↔ f=e := by simp [onlyE]
  have he := mem_filter.mp ((mem e).mpr rfl)
  refine mem_filter.mpr ⟨vS,?_⟩
  rw [sum_eq_single e]
  · exact mul_ne_zero (coeff e he.1) ((supp e he.1 v).mpr he.2)
  · intro f hf fe
    have vf : v∉f := fun h => fe ((mem f).mp (mem_filter.mpr ⟨hf,h⟩))
    have zero := not_not.mp (fun hn => vf ((supp f hf v).mp hn))
    simp [zero]
  · exact fun h => (h he.1).elim

/-- In particular a collision or progression row involves at most one active
edge if it lies in the span. Coefficients may vanish on any other edges. -/
theorem sparse_combination {𝕜 : Type*} [Field 𝕜] [DecidableEq 𝕜]
    {E : Finset (Finset V)} (tree : Forest E) (row : Finset V → V → 𝕜)
    (a : Finset V → 𝕜) (supp : ∀ e∈E, ∀ v, row e v≠0 ↔ v∈e)
    (few : ((vertices E).filter (fun v => ∑ e∈E, a e*row e v≠0)).card ≤ 3) :
    (E.filter (fun e => a e≠0)).card ≤ 1 := by
  classical
  let S := E.filter (fun e => a e≠0)
  by_contra! gt
  have gt' : 1<S.card := gt
  have sub : S⊆E := filter_subset _ _
  have hb := support_bound tree sub (card_pos.mp (by omega)) row a
    (fun _ he => (mem_filter.mp he).2) (fun e he => supp e (sub he))
  have sums (v : V) : ∑ e∈S, a e*row e v = ∑ e∈E, a e*row e v := by
    apply sum_subset sub
    intro e he hne
    have z : a e=0 := by by_contra hn; exact hne (mem_filter.mpr ⟨he,hn⟩)
    simp [z]
  have up : ((vertices S).filter (fun v => ∑ e∈S, a e*row e v≠0)).card ≤
      ((vertices E).filter (fun v => ∑ e∈E, a e*row e v≠0)).card := by
    apply card_le_card
    intro v hv
    obtain ⟨vm,hn⟩ := mem_filter.mp hv
    exact mem_filter.mpr ⟨vertices_mono sub vm, (sums v) ▸ hn⟩
  omega

/-- Fixing the root leaves all translation-invariant row dependencies
unchanged: summing columns annihilates every row except the root coordinate. -/
theorem root_coefficient {𝕜 I : Type*} [Field 𝕜]
    (U : Finset V) (root : V) (member : root∈U) (S : Finset I)
    (rows : I → V → 𝕜) (a : I → 𝕜) (b : V → 𝕜) (t : 𝕜)
    (zero_rows : ∀ i∈S, ∑ v∈U, rows i v=0) (zero_target : ∑ v∈U, b v=0)
    (rel : ∀ v∈U, b v=(∑ i∈S, a i*rows i v)+(if v=root then t else 0)) : t=0 := by
  classical
  have h := sum_congr rfl rel
  rw [sum_add_distrib,sum_comm] at h
  simp only [←mul_sum] at h
  have z : ∑ i∈S, a i*(∑ v∈U, rows i v)=0 :=
    sum_eq_zero (fun i hi => by rw [zero_rows i hi,mul_zero])
  rw [z,zero_add,zero_target] at h
  simpa [member] using h.symm

#print axioms sparse_combination
#print axioms root_coefficient
#print axioms Forest.vertex_bound
#print axioms private_count
#print axioms support_bound
end Erdos142LooseForest
