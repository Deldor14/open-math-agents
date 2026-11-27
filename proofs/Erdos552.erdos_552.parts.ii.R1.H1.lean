import OMAReductions.R_Erdos552_erdos_552_parts_ii_R1
import Mathlib

/-!
# Quadrilateral–star Ramsey numbers at finite-field orders

The exact values at q² and q² + 1 are due to T. D. Parsons,
“Ramsey Graphs and Block Designs, I” (1975), https://doi.org/10.2307/1997368.
The formalization below combines finite polarity graphs with a spectral
argument for an excess-one graph and a signed quotient obstruction at degree six.
It also includes the characteristic-two interval and the prime-gap condition
for a witness to part (ii) of Erdős problem 552.
Formalization for Left to Solve by @Deldor14. Credits for the underlying
friendship theorem and Chen's inequality are retained in the corresponding sections.
-/
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller
-/

/-
# The Friendship Theorem

## Definitions and Statement
- A `Friendship` graph is one in which any two distinct vertices have exactly one neighbor in common
- A `Politician`, at least in the context of this problem, is a vertex in a graph which is adjacent
  to every other vertex.
- The friendship theorem (Erdős, Rényi, Sós 1966) states that every finite friendship graph has a
  politician.

## Proof outline
The proof revolves around the theory of adjacency matrices, although some steps could equivalently
be phrased in terms of counting walks.
- Assume `G` is a finite friendship graph.
- First we show that any two nonadjacent vertices have the same degree
- Assume for contradiction that `G` does not have a politician.
- Conclude from the last two points that `G` is `d`-regular for some `d : ℕ`.
- Show that `G` has `d ^ 2 - d + 1` vertices.
- By casework, show that if `d = 0, 1, 2`, then `G` has a politician.
- If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
- If `A` is the adjacency matrix of `G` with entries in `ℤ/pℤ`, we show that `A ^ p` has trace `1`.
- This gives a contradiction, as `A` has trace `0`, and thus `A ^ p` has trace `0`.

## References
- [P. Erdős, A. Rényi, V. Sós, *On A Problem of Graph Theory*][erdosrenyisos]
- [C. Huneke, *The Friendship Theorem*][huneke2002]

-/

namespace Deldor14.FriendshipProof

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

section FriendshipDef

variable (G : SimpleGraph V)

open scoped Classical in
/-- This property of a graph is the hypothesis of the friendship theorem:
every pair of nonadjacent vertices has exactly one common friend,
a vertex to which both are adjacent.
-/
def Friendship [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A politician is a vertex that is adjacent to all other vertices.
-/
def ExistsPolitician : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

end FriendshipDef

variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)

namespace Friendship

variable (R)

open scoped Classical in
include hG in
/-- One characterization of a friendship graph is that there is exactly one walk of length 2
  between distinct vertices. These walks are counted in off-diagonal entries of the square of
  the adjacency matrix, so for a friendship graph, those entries are all 1. -/
theorem adjMatrix_sq_of_ne {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw]
  simp only [mul_adjMatrix_apply, neighborFinset_eq_filter, adjMatrix_apply,
    sum_boole, filter_filter, and_comm]
  congr 1
  refine (Fintype.card_coe _).symm.trans (Fintype.card_congr ?_)
  exact Equiv.subtypeEquivRight (fun x => by simp [commonNeighbors, and_comm])

open scoped Classical in
include hG in
/-- This calculation amounts to counting the number of length 3 walks between nonadjacent vertices.
  We use it to show that nonadjacent vertices have equal degrees. -/
theorem adjMatrix_pow_three_of_not_adj {v w : V} (non_adj : ¬G.Adj v w) :
    (G.adjMatrix R ^ 3 : Matrix V V R) v w = degree G v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro x hx
  rw [adjMatrix_sq_of_ne _ hG, Nat.cast_one]
  rintro ⟨rfl⟩
  rw [mem_neighborFinset] at hx
  exact non_adj hx

variable {R}

open scoped Classical in
include hG in
/-- As `v` and `w` not being adjacent implies
  `degree G v = ((G.adjMatrix R) ^ 3) v w` and `degree G w = ((G.adjMatrix R) ^ 3) v w`,
  the degrees are equal if `((G.adjMatrix R) ^ 3) v w = ((G.adjMatrix R) ^ 3) w v`

  This is true as the adjacency matrix is symmetric. -/
theorem degree_eq_of_not_adj {v w : V} (hvw : ¬G.Adj v w) : degree G v = degree G w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_pow_three_of_not_adj ℕ hG hvw,
    ← adjMatrix_pow_three_of_not_adj ℕ hG fun h ↦ hvw h.symm]
  conv_lhs => rw [← transpose_adjMatrix]
  simp only [pow_succ _ 2, sq, ← transpose_mul, transpose_apply]
  simp only [mul_assoc]

open scoped Classical in
include hG in
/-- Let `A` be the adjacency matrix of a graph `G`.
  If `G` is a friendship graph, then all of the off-diagonal entries of `A^2` are 1.
  If `G` is `d`-regular, then all of the diagonal entries of `A^2` are `d`.
  Putting these together determines `A^2` exactly for a `d`-regular friendship graph. -/
theorem adjMatrix_sq_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R ^ 2 = of fun v w => if v = w then (d : R) else (1 : R) := by
  ext (v w); by_cases h : v = w
  · rw [h, sq, adjMatrix_mul_self_apply_self, hd]; simp
  · rw [adjMatrix_sq_of_ne R hG h, of_apply, if_neg h]

open scoped Classical in
include hG in
theorem adjMatrix_sq_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) : G.adjMatrix (ZMod p) ^ 2 = of fun _ _ => 1 := by
  simp [adjMatrix_sq_of_regular hG hd, dmod]

section Nonempty

variable [Nonempty V]

open scoped Classical in
include hG in
/-- If `G` is a friendship graph without a politician (a vertex adjacent to all others), then
  it is regular. We have shown that nonadjacent vertices of a friendship graph have the same degree,
  and if there isn't a politician, we can show this for adjacent vertices by finding a vertex
  neither is adjacent to, and then using transitivity. -/
theorem isRegularOf_not_existsPolitician (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.Adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Deldor14.FriendshipProof.ExistsPolitician] at hG'
  push Not at hG'
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases Finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    have h' : ⟨x, hx⟩ ∈ (univ : Finset (G.commonNeighbors v w)) := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h'
    injection h'
  apply hxy'
  rw [key ((mem_commonNeighbors G).mpr ⟨hvx, hxw.symm⟩),
    key ((mem_commonNeighbors G).mpr ⟨hvy, hcontra.symm⟩)]

open scoped Classical in
include hG in
/-- Let `A` be the adjacency matrix of a `d`-regular friendship graph, and let `v` be a vector
  all of whose components are `1`. Then `v` is an eigenvector of `A ^ 2`, and we can compute
  the eigenvalue to be `d * d`, or as `d + (Fintype.card V - 1)`, so those quantities must be equal.

  This essentially means that the graph has `d ^ 2 - d + 1` vertices. -/
theorem card_of_regular (hd : G.IsRegularOfDegree d) : d + (Fintype.card V - 1) = d * d := by
  have v := Classical.arbitrary V
  trans ((G.adjMatrix ℕ ^ 2) *ᵥ (fun _ => 1)) v
  · rw [adjMatrix_sq_of_regular hG hd, mulVec, dotProduct, ← insert_erase (mem_univ v)]
    simp only [sum_insert, mul_one, if_true, Nat.cast_id, mem_erase, not_true,
      Ne, not_false_iff, add_right_inj, false_and, of_apply]
    rw [Finset.sum_const_nat, card_erase_of_mem (mem_univ v), mul_one]; · rfl
    intro x hx; simp [(ne_of_mem_erase hx).symm]
  · rw [sq, ← mulVec_mulVec]
    simp only [adjMatrix_mulVec_const_apply_of_regular hd, neighborFinset,
      card_neighborSet_eq_degree, hd v, Function.const_def, adjMatrix_mulVec_apply _ _ (mulVec _ _),
      mul_one, sum_const, Set.toFinset_card, smul_eq_mul, Nat.cast_id]
    change (∑ _ ∈ (G.neighborSet v).toFinset, d) = d*d
    rw [Finset.sum_const,Set.toFinset_card,card_neighborSet_eq_degree,hd]
    simp

open scoped Classical in
include hG in
/-- The size of a `d`-regular friendship graph is `1 mod (d-1)`, and thus `1 mod p` for a
  factor `p ∣ d-1`. -/
theorem card_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1) (hd : G.IsRegularOfDegree d) :
    (Fintype.card V : ZMod p) = 1 := by
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  rw [← Nat.succ_pred_eq_of_pos hpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
  simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
  have h := congr_arg (fun n : ℕ => (n : ZMod p)) (card_of_regular hG hd)
  revert h; simp [dmod]

end Nonempty

open scoped Classical in
theorem adjMatrix_sq_mul_const_one_of_regular (hd : G.IsRegularOfDegree d) :
    G.adjMatrix R * of (fun _ _ => 1) = of (fun _ _ => (d : R)) := by
  ext x
  simp only [← hd x, degree, adjMatrix_mul_apply, sum_const, Nat.smul_one_eq_cast,
    of_apply]

open scoped Classical in
theorem adjMatrix_mul_const_one_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) :
    G.adjMatrix (ZMod p) * of (fun _ _ => 1) = of (fun _ _ => 1) := by
  rw [adjMatrix_sq_mul_const_one_of_regular hd, dmod]

open scoped Classical in
include hG in
/-- Modulo a factor of `d-1`, the square and all higher powers of the adjacency matrix
  of a `d`-regular friendship graph reduce to the matrix whose entries are all 1. -/
theorem adjMatrix_pow_mod_p_of_regular {p : ℕ} (dmod : (d : ZMod p) = 1)
    (hd : G.IsRegularOfDegree d) {k : ℕ} (hk : 2 ≤ k) :
    G.adjMatrix (ZMod p) ^ k = of (fun _ _ => 1) := by
  match k with
  | 0 | 1 => exfalso; linarith
  | k + 2 =>
    induction k with
    | zero => exact adjMatrix_sq_mod_p_of_regular hG dmod hd
    | succ k hind =>
      rw [pow_succ', hind (Nat.le_add_left 2 k)]
      exact adjMatrix_mul_const_one_mod_p_of_regular dmod hd

variable [Nonempty V]

open scoped Classical in
include hG in
/-- This is the main proof. Assuming that `3 ≤ d`, we take `p` to be a prime factor of `d-1`.
  Then the `p`th power of the adjacency matrix of a `d`-regular friendship graph must have trace 1
  mod `p`, but we can also show that the trace must be the `p`th power of the trace of the original
  adjacency matrix, which is 0, a contradiction.
-/
theorem false_of_three_le_degree (hd : G.IsRegularOfDegree d) (h : 3 ≤ d) : False := by
  -- get a prime factor of d - 1
  let p : ℕ := (d - 1).minFac
  have p_dvd_d_pred := (ZMod.natCast_eq_zero_iff _ _).mpr (d - 1).minFac_dvd
  have dpos : 1 ≤ d := by lia
  have d_cast : ↑(d - 1) = (d : ℤ) - 1 := by norm_cast
  have : Fact p.Prime := ⟨Nat.minFac_prime (by lia)⟩
  have hp2 : 2 ≤ p := (Fact.out (p := p.Prime)).two_le
  have dmod : (d : ZMod p) = 1 := by
    rw [← Nat.succ_pred_eq_of_pos dpos, Nat.succ_eq_add_one, Nat.pred_eq_sub_one]
    simp only [add_eq_right, Nat.cast_add, Nat.cast_one]
    exact p_dvd_d_pred
  have Vmod := card_mod_p_of_regular hG dmod hd
  -- now we reduce to a trace calculation
  have := ZMod.trace_pow_card (G.adjMatrix (ZMod p))
  contrapose! this; clear this
  -- the trace is 0 mod p when computed one way
  rw [trace_adjMatrix, zero_pow this.out.ne_zero]
  -- but the trace is 1 mod p when computed the other way
  rw [adjMatrix_pow_mod_p_of_regular hG dmod hd hp2]
  dsimp only [Fintype.card] at Vmod
  simp only [Matrix.trace, Matrix.diag, mul_one, nsmul_eq_mul, sum_const,
    of_apply, Ne]
  rw [Vmod, ← Nat.cast_one (R := ZMod (Nat.minFac (d - 1))), ZMod.natCast_eq_zero_iff,
    Nat.dvd_one, Nat.minFac_eq_one_iff]
  lia

open scoped Classical in
include hG in
/-- If `d ≤ 1`, a `d`-regular friendship graph has at most one vertex, which is
  trivially a politician. -/
theorem existsPolitician_of_degree_le_one (hd : G.IsRegularOfDegree d) (hd1 : d ≤ 1) :
    ExistsPolitician G := by
  have h := card_of_regular hG hd
  have : Fintype.card V ≤ 1 := by interval_cases d <;> lia
  exact ⟨Classical.arbitrary V, fun w h ↦ (h <| Fintype.card_le_one_iff.mp this ..).elim⟩

open scoped Classical in
include hG in
/-- If `d = 2`, a `d`-regular friendship graph has 3 vertices, so it must be complete graph,
  and all the vertices are politicians. -/
theorem neighborFinset_eq_of_degree_eq_two (hd : G.IsRegularOfDegree 2) (v : V) :
    G.neighborFinset v = Finset.univ.erase v := by
  apply Finset.eq_of_subset_of_card_le
  · rw [Finset.subset_iff]
    intro x
    rw [mem_neighborFinset, Finset.mem_erase]
    exact fun h => ⟨(G.ne_of_adj h).symm, Finset.mem_univ _⟩
  convert_to 2 ≤ _
  · convert_to _ = Fintype.card V - 1
    · have hfr := card_of_regular hG hd
      lia
    · exact Finset.card_erase_of_mem (Finset.mem_univ _)
  · dsimp only [IsRegularOfDegree, degree] at hd
    rw [hd]

open scoped Classical in
include hG in
theorem existsPolitician_of_degree_eq_two (hd : G.IsRegularOfDegree 2) : ExistsPolitician G := by
  have v := Classical.arbitrary V
  use v
  intro w hvw
  rw [← mem_neighborFinset, neighborFinset_eq_of_degree_eq_two hG hd v, Finset.mem_erase]
  exact ⟨hvw.symm, Finset.mem_univ _⟩

open scoped Classical in
include hG in
theorem existsPolitician_of_degree_le_two (hd : G.IsRegularOfDegree d) (h : d ≤ 2) :
    ExistsPolitician G := by
  interval_cases d
  iterate 2 apply existsPolitician_of_degree_le_one hG hd; norm_num
  exact existsPolitician_of_degree_eq_two hG hd

end Friendship

include hG in
/-- **Friendship theorem**: We wish to show that a friendship graph has a politician (a vertex
  adjacent to all others). We proceed by contradiction, and assume the graph has no politician.
  We have already proven that a friendship graph with no politician is `d`-regular for some `d`,
  and now we do casework on `d`.
  If the degree is at most 2, we observe by casework that it has a politician anyway.
  If the degree is at least 3, the graph cannot exist. -/
theorem friendship_theorem [Nonempty V] : ExistsPolitician G := by
  by_contra npG
  rcases hG.isRegularOf_not_existsPolitician npG with ⟨d, dreg⟩
  rcases lt_or_ge d 3 with dle2 | dge3
  · exact npG (hG.existsPolitician_of_degree_le_two dreg (Nat.lt_succ_iff.mp dle2))
  · exact hG.false_of_three_le_degree dreg dge3

end

end Deldor14.FriendshipProof


/-
Port to the pinned Formal Conjectures environment by @Deldor14. The mathematical
proof is Chen's (1997). The Lean proof is adapted from the Apache-2.0
formalization of agnt-gg/erdos-lean, commit 8e5972f4e6787049b168e5350b1a2badc9eb8bcd,
Erdos/Erdos552.lean.

# Erdős Problem 552: $R(C_4, K_{1,n+1}) \le R(C_4, K_{1,n}) + 2$

Burr, Erdős, Faudree, Rousseau and Schelp asked whether $f(n+1) \le f(n) + 2$ for all $n$, where
$f(n) = R(C_4, K_{1,n})$ (erdosproblems.com/552). Chen Guantao proved it
(*A result on $C_4$-star Ramsey numbers*, Discrete Math. 163 (1997), 243–246). This file gives a
formal proof for every $n \ge 1$, stated with `SimpleGraph.graphRamsey` of formal-conjectures.

Proof. Let $N = f(n)$ and let $H$ be a $C_4$-free graph on $N + 2$ vertices. Two distinct vertices
of $H$ have at most one common neighbour.
* If some pair $x \ne y$ has no common neighbour, delete it. The remaining $N$ vertices contain a
  vertex $w$ with at least $n$ non-neighbours. Since $w$ is not adjacent to both $x$ and $y$, it has
  at least $n + 1$ non-neighbours in $H$.
* Otherwise every pair has exactly one common neighbour, so $H$ has a vertex $p$ adjacent to all
  others (friendship theorem). Any other vertex $u$ is adjacent only to $p$ and to the common
  neighbour of $u$ and $p$, so it has at least $N - 1 \ge n + 1$ non-neighbours, as $N \ge n + 2$.
-/

open Finset SimpleGraph

namespace OMA.ChenStar

section Lemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- A vertex of degree at least `n` gives a copy of the star `K_{1,n}`. -/
lemma star_isContained_of_le_degree (D : SimpleGraph V) [DecidableRel D.Adj] {n : ℕ} {v : V}
    (hv : n ≤ D.degree v) : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained D := by
  rw [← card_neighborFinset_eq_degree] at hv
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hv
  let e : Fin n ≃ s := (s.equivFinOfCardEq hcard).symm
  have hmem : ∀ i, D.Adj v (e i) := fun i => (mem_neighborFinset _ _ _).mp (hs (e i).2)
  let g : Fin 1 ⊕ Fin n → V := Sum.elim (fun _ => v) (fun i => (e i : V))
  have hg : Function.Injective g := by
    intro a b hab
    rcases a with a | a <;> rcases b with b | b <;> simp only [g, Sum.elim_inl, Sum.elim_inr] at hab
    · exact congrArg Sum.inl (Subsingleton.elim a b)
    · have h := hmem b
      rw [← hab] at h
      exact (h.ne rfl).elim
    · have h := hmem a
      rw [hab] at h
      exact (h.ne rfl).elim
    · exact congrArg Sum.inr (e.injective (Subtype.ext hab))
  refine ⟨⟨⟨g, ?_⟩, hg⟩⟩
  intro a b hab
  rcases a with a | a <;> rcases b with b | b <;> simp [g, completeBipartiteGraph] at hab ⊢
  · exact hmem b
  · exact (hmem a).symm

omit [DecidableEq V] in
/-- A copy of the star `K_{1,n}` has a centre of degree at least `n`. -/
lemma exists_le_degree_of_star_isContained (D : SimpleGraph V) [DecidableRel D.Adj] {n : ℕ}
    (h : (completeBipartiteGraph (Fin 1) (Fin n)).IsContained D) : ∃ v, n ≤ D.degree v := by
  obtain ⟨f⟩ := h
  refine ⟨f (Sum.inl 0), ?_⟩
  rw [← card_neighborFinset_eq_degree]
  have key := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin n)))
    (t := D.neighborFinset (f (Sum.inl 0))) (fun i => f (Sum.inr i)) ?_ ?_
  · simpa using key
  · intro i _
    rw [Finset.mem_coe, mem_neighborFinset]
    exact f.toHom.map_adj (by simp [completeBipartiteGraph])
  · intro i _ j _ hij
    exact Sum.inr_injective (f.injective hij)

omit [Fintype V] [DecidableEq V] in
/-- Two distinct vertices with two distinct common neighbours span a 4-cycle. -/
lemma cycle_isContained_of_two_common (C : SimpleGraph V) {a b x y : V} (hab : a ≠ b)
    (hxy : x ≠ y) (hax : C.Adj a x) (hbx : C.Adj b x) (hay : C.Adj a y) (hby : C.Adj b y) :
    (cycleGraph 4).IsContained C := by
  let f : Fin 4 → V := ![a, x, b, y]
  refine ⟨⟨⟨f, ?_⟩, ?_⟩⟩
  · intro i j hij
    have hedge : ∀ i j : Fin 4, (cycleGraph 4).Adj i j →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨ (i = 3 ∧ j = 0) ∨ (i = 0 ∧ j = 3) := by
      intro i j h
      rw [cycleGraph_adj] at h
      revert h
      fin_cases i <;> fin_cases j <;> decide
    rcases hedge i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hax
    · exact hax.symm
    · exact hbx.symm
    · exact hbx
    · exact hby
    · exact hby.symm
    · exact hay.symm
    · exact hay
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp [f, hab, hab.symm, hxy, hxy.symm, hax.ne, hax.ne.symm, hbx.ne, hbx.ne.symm,
        hay.ne, hay.ne.symm, hby.ne, hby.ne.symm] at hij ⊢

end Lemmas

/-- The set whose infimum is `R(C₄, K_{1,n})`. -/
abbrev ramseySet (n : ℕ) : Set ℕ :=
  { m : ℕ | ∀ (C : SimpleGraph (Fin m)),
    (cycleGraph 4).IsContained C ∨ (completeBipartiteGraph (Fin 1) (Fin n)).IsContained Cᶜ }

/-- On `2n + 2` vertices there is a `C₄` or a `K_{1,n}` in the complement: if every vertex has
fewer than `n` non-neighbours, two vertices of degree at least `n + 2` share two neighbours. -/
lemma two_mul_add_two_mem (n : ℕ) : 2 * n + 2 ∈ ramseySet n := by
  intro C
  classical
  by_cases h : ∃ v, n ≤ Cᶜ.degree v
  · obtain ⟨v, hv⟩ := h
    exact Or.inr (star_isContained_of_le_degree _ hv)
  · push Not at h
    left
    have hdeg : ∀ v, n + 2 ≤ C.degree v := by
      intro v
      have hv := h v
      rw [degree_compl, Fintype.card_fin] at hv
      have := C.degree_lt_card_verts v
      rw [Fintype.card_fin] at this
      omega
    let a : Fin (2 * n + 2) := ⟨0, by omega⟩
    let b : Fin (2 * n + 2) := ⟨1, by omega⟩
    have hab : a ≠ b := Fin.ne_of_val_ne (by simp [a, b])
    have hu := Finset.card_union_add_card_inter (C.neighborFinset a) (C.neighborFinset b)
    have hle : (C.neighborFinset a ∪ C.neighborFinset b).card ≤ 2 * n + 2 := by
      simpa using Finset.card_le_univ (C.neighborFinset a ∪ C.neighborFinset b)
    rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hu
    have hI : 1 < (C.neighborFinset a ∩ C.neighborFinset b).card := by
      have := hdeg a
      have := hdeg b
      omega
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hI
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hx hy
    exact cycle_isContained_of_two_common C hab hxy hx.1 hx.2 hy.1 hy.2

lemma ramseySet_nonempty (n : ℕ) : (ramseySet n).Nonempty :=
  ⟨_, two_mul_add_two_mem n⟩

/-- The star centred at vertex `0` of `Fin m`. -/
def centreStar (m : ℕ) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel fun u _ => u.val = 0

/-- The star has no 4-cycle: each edge of a 4-cycle needs the centre, and two disjoint edges
cannot both use it. -/
lemma not_cycle_isContained_centreStar (m : ℕ) : ¬ (cycleGraph 4).IsContained (centreStar m) := by
  rintro ⟨f⟩
  have hadj : ∀ i j : Fin 4, (cycleGraph 4).Adj i j → (f i).val = 0 ∨ (f j).val = 0 := by
    intro i j hij
    have h := f.toHom.map_adj hij
    simp only [centreStar, fromRel_adj] at h
    rcases h.2 with h | h
    · exact Or.inl h
    · exact Or.inr h
  have h01 := hadj 0 1 (by simp [cycleGraph_adj'])
  have h23 := hadj 2 3 (by simp [cycleGraph_adj'])
  have hinj : ∀ i j : Fin 4, (f i).val = 0 → (f j).val = 0 → i = j := fun i j hi hj =>
    f.injective (Fin.ext (hi.trans hj.symm))
  rcases h01 with h0 | h1 <;> rcases h23 with h2 | h3
  · exact absurd (hinj 0 2 h0 h2) (by decide)
  · exact absurd (hinj 0 3 h0 h3) (by decide)
  · exact absurd (hinj 1 2 h1 h2) (by decide)
  · exact absurd (hinj 1 3 h1 h3) (by decide)

/-- `R(C₄, K_{1,n}) ≥ n + 2` for `n ≥ 1`: on `m ≤ n + 1` vertices the centred star has no `C₄`,
and in its complement every vertex has degree less than `n`. -/
lemma add_two_le_ramsey (n : ℕ) (hn : 1 ≤ n) :
    n + 2 ≤ graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) := by
  apply le_csInf (ramseySet_nonempty n)
  intro m hm
  by_contra hlt
  push Not at hlt
  classical
  rcases hm (centreStar m) with h4 | hs
  · exact not_cycle_isContained_centreStar m h4
  · obtain ⟨v, hv⟩ := exists_le_degree_of_star_isContained _ hs
    rw [degree_compl, Fintype.card_fin] at hv
    rcases Nat.lt_or_ge m (n + 1) with hsmall | hbig
    · omega
    · -- m = n + 1 ≥ 2, so every vertex of the star has a neighbour
      have hm2 : 2 ≤ m := by omega
      have hpos : 0 < (centreStar m).degree v := by
        rw [(centreStar m).degree_pos_iff_exists_adj]
        by_cases hv0 : v.val = 0
        · refine ⟨⟨1, by omega⟩, ?_⟩
          simp only [centreStar, fromRel_adj]
          exact ⟨Fin.ne_of_val_ne (by simp [hv0]), Or.inl hv0⟩
        · refine ⟨⟨0, by omega⟩, ?_⟩
          simp only [centreStar, fromRel_adj]
          exact ⟨Fin.ne_of_val_ne (by simpa using hv0), by simp⟩
      omega

/-- The main step: `R(C₄, K_{1,n}) + 2` vertices suffice for `K_{1,n+1}`. -/
lemma ramsey_add_two_mem (n : ℕ) (hn : 1 ≤ n) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) + 2 ∈ ramseySet (n + 1) := by
  set N := graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) with hN_def
  have hNmem : N ∈ ramseySet n := Nat.sInf_mem (ramseySet_nonempty n)
  have hNge : n + 2 ≤ N := add_two_le_ramsey n hn
  intro H
  classical
  by_cases hc : (cycleGraph 4).IsContained H
  · exact Or.inl hc
  right
  -- In a C₄-free graph two distinct vertices have at most one common neighbour.
  have hcommon : ∀ x y, x ≠ y → ∀ a b, H.Adj x a → H.Adj y a → H.Adj x b → H.Adj y b →
      a = b := by
    intro x y hxy a b hxa hya hxb hyb
    by_contra hab
    exact hc (cycle_isContained_of_two_common H hxy hab hxa hya hxb hyb)
  by_cases hpair : ∃ x y, x ≠ y ∧ ∀ v, ¬ (H.Adj x v ∧ H.Adj y v)
  · obtain ⟨x, y, hxy, hno⟩ := hpair
    have hT : Fintype.card {v : Fin (N + 2) // v ≠ x ∧ v ≠ y} = N := by
      rw [Fintype.card_subtype]
      have hfilter : (univ.filter fun v : Fin (N + 2) => v ≠ x ∧ v ≠ y) =
          (univ.erase x).erase y := by
        ext v
        simp [and_comm]
      rw [hfilter, Finset.card_erase_of_mem (by simp [Ne.symm hxy]),
        Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, Fintype.card_fin]
      omega
    let e : Fin N ≃ {v : Fin (N + 2) // v ≠ x ∧ v ≠ y} := (Fintype.equivFinOfCardEq hT).symm
    let ι : Fin N → Fin (N + 2) := fun i => (e i).1
    have hι : Function.Injective ι := fun i j h => e.injective (Subtype.ext h)
    rcases hNmem (H.comap ι) with h4 | hs
    · exact absurd (h4.trans ⟨⟨⟨ι, fun h => h⟩, hι⟩⟩) hc
    · obtain ⟨w, hw⟩ := exists_le_degree_of_star_isContained _ hs
      apply star_isContained_of_le_degree Hᶜ (v := ι w)
      -- `ι w` misses `x` or `y`.
      obtain ⟨z, hz, hzxy⟩ : ∃ z, ¬ H.Adj (ι w) z ∧ (z = x ∨ z = y) := by
        by_cases hx : H.Adj (ι w) x
        · exact ⟨y, fun hy => hno (ι w) ⟨hx.symm, hy.symm⟩, Or.inr rfl⟩
        · exact ⟨x, hx, Or.inl rfl⟩
      have hzι : ∀ i, ι i ≠ z := by
        intro i hi
        rcases hzxy with rfl | rfl
        · exact (e i).2.1 hi
        · exact (e i).2.2 hi
      let A := ((H.comap ι)ᶜ.neighborFinset w).map ⟨ι, hι⟩
      have hA : A ⊆ Hᶜ.neighborFinset (ι w) := by
        intro u hu
        simp only [A, Finset.mem_map, mem_neighborFinset, compl_adj, comap_adj,
          Function.Embedding.coeFn_mk] at hu
        obtain ⟨u', ⟨hne, hnadj⟩, rfl⟩ := hu
        rw [mem_neighborFinset, compl_adj]
        exact ⟨fun h => hne (hι h), hnadj⟩
      have hzA : z ∉ A := by
        simp only [A, Finset.mem_map, Function.Embedding.coeFn_mk, not_exists, not_and]
        exact fun i _ => hzι i
      have hzN : z ∈ Hᶜ.neighborFinset (ι w) := by
        rw [mem_neighborFinset, compl_adj]
        exact ⟨fun h => hzι w h, hz⟩
      have hcard : (insert z A).card ≤ Hᶜ.degree (ι w) := by
        rw [← card_neighborFinset_eq_degree]
        exact Finset.card_le_card (Finset.insert_subset hzN hA)
      rw [Finset.card_insert_of_notMem hzA, Finset.card_map,
        card_neighborFinset_eq_degree] at hcard
      omega
  · push Not at hpair
    -- Every pair has exactly one common neighbour: a friendship graph.
    have hfr : Deldor14.FriendshipProof.Friendship H := by
      intro v w hvw
      rw [Fintype.card_eq_one_iff]
      obtain ⟨c, hvc, hwc⟩ := hpair v w hvw
      refine ⟨⟨c, H.mem_commonNeighbors.mpr ⟨hvc, hwc⟩⟩, ?_⟩
      rintro ⟨d, hd⟩
      rw [H.mem_commonNeighbors] at hd
      exact Subtype.ext (hcommon v w hvw d c hd.1 hd.2 hvc hwc)
    obtain ⟨p, hp⟩ := Deldor14.FriendshipProof.friendship_theorem hfr
    obtain ⟨u, hup⟩ := exists_ne p
    obtain ⟨c, huc, hpc⟩ := hpair u p hup
    have hdeg : H.degree u ≤ 2 := by
      rw [← card_neighborFinset_eq_degree]
      calc (H.neighborFinset u).card ≤ ({p, c} : Finset (Fin (N + 2))).card := by
            apply Finset.card_le_card
            intro t ht
            rw [mem_neighborFinset] at ht
            by_cases htp : t = p
            · simp [htp]
            · have hpt : H.Adj p t := hp t (fun h => htp h.symm)
              have htc : t = c := hcommon u p hup t c ht hpt huc hpc
              simp [htc]
        _ ≤ 2 := Finset.card_le_two
    apply star_isContained_of_le_degree Hᶜ (v := u)
    rw [degree_compl, Fintype.card_fin]
    omega

/-- **Chen (1997).** For every `n ≥ 1`, `R(C₄, K_{1,n+1}) ≤ R(C₄, K_{1,n}) + 2`. -/
theorem erdos_552.variants.succ_le_add_two (n : ℕ) (hn : 1 ≤ n) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin (n + 1))) ≤
      SimpleGraph.graphRamsey (SimpleGraph.cycleGraph 4)
        (completeBipartiteGraph (Fin 1) (Fin n)) + 2 :=
  Nat.sInf_le (ramsey_add_two_mem n hn)

end OMA.ChenStar


namespace Deldor14.Star.Packing
open Finset SimpleGraph OMA.ChenStar

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The endpoints of two-step walks from a fixed vertex, excluding that vertex.
In a four-cycle-free graph every endpoint has a unique intermediate vertex. -/
def endpoints (v : V) : Finset V :=
  (G.neighborFinset v).biUnion (fun u => (G.neighborFinset u).erase v)

theorem mem_endpoints {v z : V} :
    z ∈ endpoints G v ↔ z ≠ v ∧ ∃ u, G.Adj v u ∧ G.Adj z u := by
  simp only [endpoints,mem_biUnion,mem_erase,mem_neighborFinset]
  constructor
  · rintro ⟨u,vu,zv,uz⟩
    exact ⟨zv,u,vu,uz.symm⟩
  · rintro ⟨zv,u,vu,zu⟩
    exact ⟨u,vu,zv,zu.symm⟩

theorem card_endpoints (h : ¬(cycleGraph 4).IsContained G) (v : V) :
    (endpoints G v).card = ∑ u ∈ G.neighborFinset v, (G.degree u - 1) := by
  unfold endpoints
  rw [card_biUnion]
  · apply sum_congr rfl
    intro u hu
    rw [card_erase_of_mem,card_neighborFinset_eq_degree]
    exact (mem_neighborFinset _ _ _).mpr ((mem_neighborFinset _ _ _).mp hu).symm
  · intro a ha b hb ne
    apply Finset.disjoint_left.mpr
    intro z za zb
    rw [mem_erase,mem_neighborFinset] at za zb
    have va := (mem_neighborFinset _ _ _).mp ha
    have vb := (mem_neighborFinset _ _ _).mp hb
    exact h (cycle_isContained_of_two_common G ne za.1.symm va.symm vb.symm za.2 zb.2)

theorem local_bound (h : ¬(cycleGraph 4).IsContained G) (d : ℕ)
    (minimum : ∀ v, d ≤ G.degree v) (v : V) :
    G.degree v * (d-1) ≤ (endpoints G v).card := by
  rw [card_endpoints G h]
  calc
    G.degree v * (d-1) = ∑ _u ∈ G.neighborFinset v, (d-1) := by simp
    _ ≤ _ := by
      apply sum_le_sum
      intro u _
      exact Nat.sub_le_sub_right (minimum u) 1

theorem no_self (v : V) : v ∉ endpoints G v := by simp [mem_endpoints]

theorem improved_moore [Nonempty V] (h : ¬(cycleGraph 4).IsContained G) {d : ℕ}
    (large : 3 ≤ d) (minimum : ∀ v, d ≤ G.degree v) :
    d*(d-1)+2 ≤ Fintype.card V := by
  classical
  by_contra! contra
  have all (v w : V) (ne : v ≠ w) : ∃ u, G.Adj v u ∧ G.Adj w u := by
    by_contra none
    have exc : endpoints G v ⊆ ((univ.erase v).erase w) := by
      intro x hx
      have cond := (mem_endpoints G).mp hx
      refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨cond.1,mem_univ x⟩⟩
      rintro rfl
      exact none cond.2
    have ub := card_le_card exc
    rw [card_erase_of_mem (mem_erase.mpr ⟨ne.symm,mem_univ w⟩),
      card_erase_of_mem (mem_univ v),card_univ] at ub
    have lb := (Nat.mul_le_mul_right (d-1) (minimum v)).trans (local_bound G h d minimum v)
    have pos := Fintype.card_pos (α:=V)
    have nontriv : 2 ≤ Fintype.card V := by have := G.degree_lt_card_verts v; have := minimum v; omega
    omega
  have uniq {v w a b : V} (ne : v ≠ w) (va : G.Adj v a) (wa : G.Adj w a)
      (vb : G.Adj v b) (wb : G.Adj w b) : a=b := by
    by_contra ab
    exact h (cycle_isContained_of_two_common G ne ab va wa vb wb)
  have fr : Deldor14.FriendshipProof.Friendship G := by
    letI : DecidableRel G.Adj := fun _ _ => Classical.propDecidable _
    intro v w ne
    rw [Fintype.card_eq_one_iff]
    obtain ⟨c,vc,wc⟩ := all v w ne
    exact ⟨⟨c,G.mem_commonNeighbors.mpr ⟨vc,wc⟩⟩,fun ⟨z,hz⟩ =>
      Subtype.ext (uniq ne (G.mem_commonNeighbors.mp hz).1 (G.mem_commonNeighbors.mp hz).2 vc wc)⟩
  obtain ⟨p,univP⟩ := Deldor14.FriendshipProof.friendship_theorem fr
  obtain ⟨u,pu⟩ := (G.degree_pos_iff_exists_adj p).mp (show 0<G.degree p by have := minimum p; omega)
  obtain ⟨c,cu,cp⟩ := all u p pu.ne.symm
  have subset : G.neighborFinset u ⊆ {p,c} := by
    intro t ht
    by_cases eq : t=p
    · simp [eq]
    · have tc := uniq pu.ne.symm ((mem_neighborFinset _ _ _).mp ht) (univP t (Ne.symm eq)) cu cp
      simp [tc]
  have ub := (card_le_card subset).trans Finset.card_le_two
  rw [card_neighborFinset_eq_degree] at ub
  have := minimum u
  omega

end Deldor14.Star.Packing


namespace Deldor14.Star
open SimpleGraph Finset

inductive Point (F : Type*) where
  | pole
  | inf (x : F)
  | aff (x y : F)
deriving DecidableEq, Fintype

namespace Point
variable {F : Type*} [Field F]

def inc : Point F → Point F → Prop
  | .aff a b, .aff c d => b+d=a*c
  | .aff a _, .inf c => a=c
  | .inf a, .aff c _ => a=c
  | .pole, .inf _ | .inf _, .pole => True
  | _,_ => False

theorem inc_symm {u v : Point F} (h : inc u v) : inc v u := by
  cases u <;> cases v <;> simpa [inc,eq_comm,add_comm,mul_comm] using h

def graph : SimpleGraph (Point F) where
  Adj u v := u ≠ v ∧ inc u v
  symm := ⟨fun u v h => ⟨h.1.symm,inc_symm h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private theorem affine_lines {a b c d x y z w : F}
    (dif : a=c → b=d → False)
    (h1 : b+y=a*x) (h2 : d+y=c*x) (h3 : b+w=a*z) (h4 : d+w=c*z) :
    x=z ∧ y=w := by
  have h : (a-c)*(x-z)=0 := by linear_combination -h1+h2+h3-h4
  rcases mul_eq_zero.mp h with e | e
  · have ac := sub_eq_zero.mp e
    subst c
    exact (dif rfl (by linear_combination h1-h2)).elim
  · have xz := sub_eq_zero.mp e
    subst z
    exact ⟨rfl,by linear_combination h1-h3⟩

theorem common_unique {a b x y : Point F} (ab : a ≠ b)
    (ax : inc a x) (bx : inc b x) (ay : inc a y) (by' : inc b y) : x=y := by
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp only [inc] at ax bx ay by' <;>
    first
    | contradiction
    | rfl
    | (obtain ⟨e,f⟩ := affine_lines (fun h k => ab (by rw [h,k])) ax bx ay by'
       rw [e,f])
    | grind

variable [Fintype F] [DecidableEq F]

theorem card_points : Fintype.card (Point F) = (Fintype.card F)^2 + Fintype.card F + 1 := by
  let e : Point F ≃ Option (F × Option F) := {
    toFun := fun | .pole => none | .inf a => some (a,none) | .aff a b => some (a,some b)
    invFun := fun | none => .pole | some (a,none) => .inf a | some (a,some b) => .aff a b
    left_inv := by rintro (_|_|_); all_goals rfl
    right_inv := by rintro (_|⟨a,_|b⟩); all_goals rfl }
  rw [Fintype.card_congr e,Fintype.card_option,Fintype.card_prod,Fintype.card_option]
  ring

private def neighbors (v : Point F) (x : F) : Point F :=
  match v with
  | .pole => .inf x
  | .inf a => .aff a x
  | .aff a b => if x=a then .inf a else .aff x (a*x-b)

private theorem neighbors_adj (v : Point F) (x : F) : graph.Adj v (neighbors v x) := by
  cases v with
  | pole => simp [graph,neighbors,inc]
  | inf a => simp [graph,neighbors,inc]
  | aff a b =>
    by_cases h : x=a
    · simp [graph,neighbors,inc,h]
    · simp [graph,neighbors,inc,h,Ne.symm h]

private theorem neighbors_inj (v : Point F) : Function.Injective (neighbors v) := by
  intro x y h
  cases v with
  | pole => simpa [neighbors] using h
  | inf a => simpa [neighbors] using h
  | aff a b =>
    by_cases hx : x=a <;> by_cases hy : y=a <;> simp_all [neighbors]

theorem le_degree [DecidableRel (graph (F:=F)).Adj] (v : Point F) :
    Fintype.card F ≤ graph.degree v := by
  let f (i : F) : ↥(graph.neighborFinset v) :=
    ⟨neighbors v i, (mem_neighborFinset _ _ _).mpr (neighbors_adj v i)⟩
  have inj : Function.Injective f := fun _ _ h => neighbors_inj v (congrArg Subtype.val h)
  rw [← card_neighborFinset_eq_degree]
  exact (Fintype.card_le_of_injective f inj).trans_eq (Fintype.card_coe _)

theorem no_square : ¬(cycleGraph 4).IsContained (graph (F:=F)) := by
  rintro ⟨f⟩
  have e01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have e21 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide)
  have e03 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide)
  have e23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have dif : f 0 ≠ f 2 := f.injective.ne (by decide)
  have eq := common_unique dif e01.2 e21.2 e03.2 e23.2
  exact (by decide : (1 : Fin 4) ≠ 3) (f.injective eq)

end Point
end Deldor14.Star


namespace Deldor14.Star.Slices
open SimpleGraph Finset

abbrev Vertex (F : Type*) (k t : ℕ) := (Fin k × Option F) ⊕ Fin t

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {k t : ℕ}
variable (r : Fin k ↪ F) (z : F) (h : Fin t ↪ F)

def point : Vertex F k t → Point F
  | .inl (i,none) => .inf (r i)
  | .inl (i,some b) => .aff (r i) b
  | .inr x => .aff z (h x)

theorem point_injective (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) :
    Function.Injective (point r z h) := by
  rintro (⟨i, _|b⟩ | x) (⟨j, _|c⟩ | y) e <;>
    simp only [point,Point.inf.injEq,Point.aff.injEq,reduceCtorEq] at e
  · rw [r.injective e]
  · rcases e with ⟨ij,bc⟩
    rw [r.injective ij,bc]
  · exact (hz i y e.1).elim
  · exact (hz j x e.1.symm).elim
  · rw [h.injective e.2]


def host : SimpleGraph (Vertex F k t) := Point.graph.comap (point r z h)

theorem no_square (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) :
    ¬(cycleGraph 4).IsContained (host r z h) := by
  have emb : (host r z h).IsContained Point.graph :=
    ⟨⟨⟨point r z h, fun e => e⟩,point_injective r z h hz⟩⟩
  exact fun bad => Point.no_square (bad.trans emb)

def neighbor (v : Vertex F k t) (j : Fin k) : Vertex F k t :=
  match v with
  | .inl (i,none) => .inl (i,some (r j))
  | .inl (i,some b) =>
    if j=i then .inl (i,none) else .inl (j,some (r i*r j-b))
  | .inr x => .inl (j,some (z*r j-h x))

theorem neighbor_injective (v : Vertex F k t) : Function.Injective (neighbor r z h v) := by
  rintro a b e
  rcases v with ⟨i, _|y⟩ | x
  · exact r.injective (by simpa [neighbor] using e)
  · by_cases ai : a=i <;> by_cases bi : b=i <;> simp_all [neighbor]
  · exact (by simpa [neighbor] using e : a=b ∧ _) |>.1

theorem neighbor_adj (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) (v : Vertex F k t) (j : Fin k) :
    (host r z h).Adj v (neighbor r z h v j) := by
  rcases v with ⟨i, _|y⟩ | x
  · simp [host,Point.graph,Point.inc,point,neighbor]
  · by_cases eq : j=i
    · simp [host,Point.graph,Point.inc,point,neighbor,eq]
    · have dif := r.injective.ne (Ne.symm eq)
      simp [host,Point.graph,Point.inc,point,neighbor,eq,dif]
  · have dif := (hz j x).symm
    simp [host,Point.graph,Point.inc,point,neighbor,dif]

theorem le_degree (hz : ∀ i, ∀ _ : Fin t, r i ≠ z) [DecidableRel (host r z h).Adj]
    (v : Vertex F k t) : k ≤ (host r z h).degree v := by
  let G := host r z h
  let f (i : Fin k) : ↥(G.neighborFinset v) :=
    ⟨neighbor r z h v i,(mem_neighborFinset _ _ _).mpr (neighbor_adj r z h hz v i)⟩
  have inj : Function.Injective f := fun _ _ e => neighbor_injective r z h v (congrArg Subtype.val e)
  have count := (Fintype.card_le_of_injective f inj).trans_eq (Fintype.card_coe _)
  simpa only [Fintype.card_fin,card_neighborFinset_eq_degree] using count

end Deldor14.Star.Slices


namespace Deldor14.Star
open SimpleGraph Finset OMA.ChenStar

/-- A single host graph obstructs every Ramsey assertion on fewer vertices. -/
theorem lower_from_host {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {n : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
    (blue : ∀ v, Gᶜ.degree v < n) :
    Fintype.card V <
      graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) := by
  classical
  let m := graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))
  change Fintype.card V < m
  by_contra! small
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin m) ≤ Fintype.card V by simpa using small)
  let C : SimpleGraph (Fin m) := G.comap e
  have r : C.IsContained G := ⟨⟨⟨e,fun h => h⟩,e.injective⟩⟩
  have b : Cᶜ.IsContained Gᶜ := by
    refine ⟨⟨⟨e,?_⟩,e.injective⟩⟩
    intro i j h
    rw [compl_adj] at h ⊢
    exact ⟨e.injective.ne h.1,h.2⟩
  have mem : m ∈ ramseySet n := Nat.sInf_mem (ramseySet_nonempty n)
  rcases mem C with h | h
  · exact red (h.trans r)
  · obtain ⟨v,hv⟩ := exists_le_degree_of_star_isContained Gᶜ (h.trans b)
    exact (blue v).not_ge hv

end Deldor14.Star


namespace Deldor14.Star
open SimpleGraph Finset OMA.ChenStar

noncomputable abbrev number (n : ℕ) :=
  graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n))

/-- Field orders give a whole block of lower bounds, including the square order.
Each full row consists of all affine points of one slope and its point at infinity.
Additional affine points are taken from an extra row. -/
theorem lower_on_block (F : Type*) [Field F] [Fintype F] {k t : ℕ}
    (hk : k ≤ Fintype.card F) (ht : t < Fintype.card F)
    (room : 0<t → k<Fintype.card F) :
    k * Fintype.card F + t + k < number (k * Fintype.card F + t) := by
  classical
  let q := Fintype.card F
  have pos : 0<q := Fintype.card_pos
  let e : Fin q ≃ F := (Fintype.equivFin F).symm
  let r : Fin k ↪ F := (Fin.castLEEmb hk).trans e.toEmbedding
  let h : Fin t ↪ F := (Fin.castLEEmb ht.le).trans e.toEmbedding
  let z := e ⟨k%q,Nat.mod_lt k pos⟩
  have sep (i : Fin k) (j : Fin t) : r i ≠ z := by
    intro bad
    have lt := room (Nat.zero_lt_of_lt j.isLt)
    have eq : (i.val:ℕ)=k%q := congrArg Fin.val (e.injective bad)
    rw [Nat.mod_eq_of_lt lt] at eq
    have := i.isLt
    omega
  let G := Slices.host r z h
  have sz : Fintype.card (Slices.Vertex F k t) = k*q+t+k := by
    simp only [Slices.Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_option,Fintype.card_fin,q]
    ring
  obtain hk0 | hkpos := Nat.eq_zero_or_pos k
  · subst k
    simp only [Nat.zero_mul,Nat.zero_add,Nat.add_zero]
    by_cases ht0 : t=0
    · subst t
      change 0 < number 0
      by_contra! bad
      have eq : number 0 = 0 := by omega
      have hm : number 0 ∈ ramseySet 0 := Nat.sInf_mem (ramseySet_nonempty 0)
      rw [eq] at hm
      rcases hm (⊥ : SimpleGraph (Fin 0)) with ⟨f⟩ | ⟨f⟩
      · obtain ⟨g⟩ := f
        exact Fin.elim0 (g 0)
      · obtain ⟨g⟩ := f
        exact Fin.elim0 (g (.inl 0))
    · exact lt_of_lt_of_le (by omega : t < t+2) (add_two_le_ramsey t (by omega))
  · have positive : 0 < k*q+t := by have := Nat.mul_pos hkpos pos; omega
    have d (v) := Slices.le_degree r z h sep v
    have bound : ∀ v, Gᶜ.degree v < k*q+t := by
      intro v
      rw [degree_compl,sz]
      have := d v
      change k ≤ G.degree v at this
      omega
    simpa only [sz] using lower_from_host G (Slices.no_square r z h sep) bound

theorem field_lower (F : Type*) [Field F] [Fintype F] {n : ℕ}
    (hn : n ≤ Fintype.card F ^ 2) : n + n/Fintype.card F < number n := by
  let q := Fintype.card F
  have pos : 0<q := Fintype.card_pos
  have eq := Nat.div_add_mod n q
  have hsplit : n/q*q + n%q = n := by simpa [Nat.mul_comm] using eq
  have hk : n/q ≤ q := by
    by_contra! bad
    have := Nat.mul_le_mul_right q bad
    change n ≤ q^2 at hn
    rw [Nat.succ_mul] at this
    rw [pow_two] at hn
    omega
  have room (rem : 0 < n%q) : n/q < q := by
    by_contra! no
    have same : n/q=q := by omega
    rw [same] at hsplit
    change n ≤ q^2 at hn
    nlinarith only [hsplit,hn,rem]
  have g := lower_on_block F hk (Nat.mod_lt n pos) room
  change n/q*q+n%q + n/q < number (n/q*q+n%q) at g
  rwa [hsplit] at g

theorem field_plus_one (F : Type*) [Field F] [Fintype F] :
    Fintype.card F ^ 2 + Fintype.card F + 1 < number (Fintype.card F^2+1) := by
  classical
  let G := Point.graph (F:=F)
  have low := lower_from_host (n:=Fintype.card F^2+1) G Point.no_square (by
    intro v
    rw [degree_compl,Point.card_points]
    have h := Point.le_degree v
    change Fintype.card F ≤ G.degree v at h
    omega)
  simpa only [Point.card_points] using low

end Deldor14.Star


namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

/-- The friendship theorem rules out the one missing vertex in the elementary
two-step count. This is the sharp square-order side of Parsons' estimate. -/
theorem parsons_upper {n k : ℕ} (hk : 2 ≤ k) (hn : n ≤ k^2) :
    graphRamsey (cycleGraph 4) (completeBipartiteGraph (Fin 1) (Fin n)) ≤ n+k+1 := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra hs
  have minimum (v : Fin (n+k+1)) : k+1 ≤ G.degree v := by
    have small : Gᶜ.degree v < n := lt_of_not_ge (fun large => hs (star_isContained_of_le_degree Gᶜ large))
    rw [degree_compl,Fintype.card_fin] at small
    omega
  haveI : Nonempty (Fin (n+k+1)) := ⟨⟨0,by omega⟩⟩
  have bound := Packing.improved_moore G red (d:=k+1) (by omega) minimum
  simp only [Nat.add_sub_cancel,Fintype.card_fin] at bound
  nlinarith

end Deldor14.Star


namespace Deldor14.Star
open SimpleGraph

/-- Covers every finite field, including non-prime orders. -/
theorem field_square (F : Type*) [Field F] [Fintype F] :
    number (Fintype.card F ^ 2) = Fintype.card F ^ 2 + Fintype.card F + 1 := by
  let q := Fintype.card F
  have pos : 0<q := Fintype.card_pos
  have two : 2 ≤ q := Fintype.one_lt_card
  have lo := field_lower F (n:=q^2) (by rfl)
  have div : q^2/q=q := by rw [pow_two,Nat.mul_div_cancel _ pos]
  change q^2 + q^2/q < number (q^2) at lo
  rw [div] at lo
  exact Nat.le_antisymm (parsons_upper two le_rfl) lo

theorem prime_square {p : ℕ} (hp : p.Prime) : number (p^2)=p^2+p+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  simpa only [ZMod.card] using field_square (ZMod p)

/-- If a Ramsey value saves c below n+sqrt(n), the entire interval from
sqrt(n) through sqrt(n)+c is devoid of finite-field orders. -/
theorem field_gap (F : Type*) [Field F] [Fintype F] {n : ℕ} {c : ℝ}
    (hn : n ≤ Fintype.card F^2)
    (witness : (number n : ℝ) ≤ (n : ℝ) + Real.sqrt n - c) :
    Real.sqrt n + c < Fintype.card F := by
  let q := Fintype.card F
  have hq : 0<q := Fintype.card_pos
  have lo : n+n/q+1 ≤ number n := field_lower F hn
  have realLo : (n:ℝ)+(n/q:ℕ)+1 ≤ (number n:ℝ) := by exact_mod_cast lo
  have y : (n/q:ℕ)+1 ≤ Real.sqrt n - c := by linarith
  have divbound : n < (n/q+1)*q := by
    have eq := Nat.mod_add_div n q
    have rem := Nat.mod_lt n hq
    nlinarith only [eq,rem]
  have divbound' : (n:ℝ) < ((n/q:ℕ)+1 : ℝ)*q := by exact_mod_cast divbound
  have pos : (0:ℝ) ≤ q := by positivity
  have bound := lt_of_lt_of_le divbound' (mul_le_mul_of_nonneg_right y pos)
  have square := Real.sq_sqrt (show 0 ≤ (n:ℝ) by positivity)
  change Real.sqrt n + c < (q:ℝ)
  by_contra! contra
  have product := mul_nonneg (show 0 ≤ Real.sqrt n + c - (q:ℝ) by linarith) pos
  nlinarith [sq_nonneg ((q:ℝ)-Real.sqrt n)]

theorem prime_gap {p n : ℕ} (hp : p.Prime) (hn : n ≤ p^2) {c : ℝ}
    (witness : (number n : ℝ) ≤ n + Real.sqrt n - c) : Real.sqrt n + c < p := by
  letI : Fact p.Prime := ⟨hp⟩
  have h := field_gap (ZMod p) (n:=n) (c:=c) (by simpa only [ZMod.card] using hn) witness
  simpa only [ZMod.card] using h

end Deldor14.Star


namespace Deldor14.Star.EvenRows
open SimpleGraph Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {s : ℕ} (r : Fin s ↪ F) (zeroRow : Fin s)

abbrev Vertex (F : Type*) (s : ℕ) := (F × F) ⊕ Fin s

def point : Vertex F s → Point F
  | .inl (a,b) => .aff a b
  | .inr i => .inf (r i)

theorem point_injective : Function.Injective (point r) := by
  rintro (⟨a,b⟩|i) (⟨x,y⟩|j) e <;> simp_all [point]

def host := Point.graph.comap (point r)

theorem no_square : ¬(cycleGraph 4).IsContained (host r) := by
  have e : (host r).IsContained Point.graph :=
    ⟨⟨⟨point r, fun h => h⟩, point_injective r⟩⟩
  exact fun h => Point.no_square (h.trans e)

/-- A row of slope zero needs its point at infinity to replace a missing loop.
All other rows have a genuine neighbour at each affine slope. -/
def neighbor (v : Vertex F s) (x : F) : Vertex F s :=
  match v with
  | .inl (a,b) => if a=0 ∧ x=0 then .inr zeroRow else .inl (x,a*x-b)
  | .inr i => .inl (r i,x)

theorem neighbor_injective (v : Vertex F s) : Function.Injective (neighbor r zeroRow v) := by
  intro x y e
  rcases v with ⟨a,b⟩ | i
  · by_cases hx : a=0 ∧ x=0 <;> by_cases hy : a=0 ∧ y=0 <;> simp_all [neighbor]
  · simpa [neighbor] using e

theorem neighbor_adj (zero : r zeroRow=0) (v : Vertex F s) (x : F) :
    (host r).Adj v (neighbor r zeroRow v x) := by
  rcases v with ⟨a,b⟩ | i
  · by_cases hx : a=0 ∧ x=0
    · simp [host,neighbor,point,Point.graph,Point.inc,hx,zero,hx.1]
    · have ne : ¬(a=x ∧ b=a*x-b) := by
        rintro ⟨rfl,eq⟩
        have h : b+b=a*a := by linear_combination eq
        rw [CharTwo.add_self_eq_zero] at h
        have a0 := mul_self_eq_zero.mp h.symm
        exact hx ⟨a0,a0⟩
      simp [host,neighbor,point,Point.graph,Point.inc,hx]
      tauto
  · simp [host,neighbor,point,Point.graph,Point.inc]

theorem min_degree (zero : r zeroRow=0) [DecidableRel (host r).Adj] (v : Vertex F s) :
    Fintype.card F ≤ (host r).degree v := by
  let f (i : F) : ↥((host r).neighborFinset v) :=
    ⟨neighbor r zeroRow v i, (mem_neighborFinset _ _ _).mpr (neighbor_adj r zeroRow zero v i)⟩
  have inj : Function.Injective f := fun _ _ e => neighbor_injective r zeroRow v (congrArg Subtype.val e)
  rw [← card_neighborFinset_eq_degree]
  exact (Fintype.card_le_of_injective f inj).trans_eq (Fintype.card_coe _)

end Deldor14.Star.EvenRows


namespace Deldor14.Star
open SimpleGraph Finset

/-- Parsons' interval at a power of two. Removing chosen points at infinity
preserves the minimum degree as long as the point for slope zero remains. -/
theorem even_field_interval (F : Type*) [Fintype F] [Field F] [CharP F 2]
    {n s : ℕ} (spos : 0<s) (sle : s ≤ Fintype.card F)
    (sz : n + Fintype.card F = Fintype.card F^2+s) :
    number n = n + Fintype.card F + 1 := by
  classical
  let q := Fintype.card F
  have two : 2 ≤ q := Fintype.one_lt_card
  let e := (Fintype.equivFin F).symm.toEmbedding
  let b := (Fin.castLEEmb sle).trans e
  let z : Fin s := ⟨0,spos⟩
  let r : Fin s ↪ F := ⟨fun x => b x - b z, fun _ _ h => b.injective (sub_left_inj.mp h)⟩
  have zero : r z=0 := sub_self _
  let G := EvenRows.host r
  have count : Fintype.card (EvenRows.Vertex F s) = n+q := by
    rw [sz]
    simp [EvenRows.Vertex,pow_two]
  have min (v) : q ≤ G.degree v := EvenRows.min_degree r z zero v
  have hs : n+q=q^2+s := sz
  have bound : ∀ v, Gᶜ.degree v < n := by
    intro v
    have := min v
    have positive : 0 < n := by
      have h : q ≤ q^2 := by exact Nat.le_self_pow (by decide : 2≠0) q
      omega
    rw [degree_compl,count]
    omega
  have lower := lower_from_host G (EvenRows.no_square r) bound
  rw [count] at lower
  have nq : n ≤ q^2 := by change s ≤ q at sle; omega
  exact Nat.le_antisymm (parsons_upper two nq) lower

theorem power_two_interval {m n s : ℕ} (hm : m≠0) (spos : 0<s) (sle : s ≤ 2^m)
    (sz : n + 2^m = (2^m)^2+s) : number n = n+2^m+1 := by
  letI : Fintype (GaloisField 2 m) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 m) = 2^m := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 m hm]
  simpa only [hq] using even_field_interval (GaloisField 2 m) spos
    (by simpa only [hq] using sle) (n:=n) (by simpa only [hq] using sz)

end Deldor14.Star


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph OMA.ChenStar Packing
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ}

def common (v w : V) : Finset V := G.neighborFinset v ∩ G.neighborFinset w

theorem mem_common {v w u : V} : u ∈ common G v w ↔ G.Adj v u ∧ G.Adj w u := by
  simp [common]

theorem codeg_le_one (red : ¬ (cycleGraph 4).IsContained G) {v w : V} (vw : v≠w) :
    (common G v w).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ab
  exact red (cycle_isContained_of_two_common G vw ab ((mem_common G).mp ha).1 ((mem_common G).mp ha).2
    ((mem_common G).mp hb).1 ((mem_common G).mp hb).2)

theorem regular_of_min (red : ¬ (cycleGraph 4).IsContained G) (large : 3≤d)
    (count : Fintype.card V=d*(d-1)+2) (minimum : ∀ v, d≤G.degree v) :
    ∀ v, G.degree v=d := by
  intro v
  have sub : endpoints G v ⊆ univ.erase v := fun x hx =>
    mem_erase.mpr ⟨((mem_endpoints G).mp hx).1, mem_univ x⟩
  have ub := card_le_card sub
  rw [card_erase_of_mem (mem_univ v),card_univ,count] at ub
  have low := local_bound G red d minimum v
  by_contra not_eq
  have high : d+1 ≤ G.degree v := by have := minimum v; omega
  have h := Nat.mul_le_mul_right (d-1) high
  rw [Nat.add_mul,one_mul] at h
  omega

def missing (v : V) := (univ.erase v) \ endpoints G v

theorem mem_missing {v w : V} : w ∈ missing G v ↔ w≠v ∧ common G v w = ∅ := by
  classical
  simp only [missing,mem_sdiff,mem_erase,mem_univ,and_true,mem_endpoints]
  rw [Finset.eq_empty_iff_forall_notMem]
  simp only [mem_common]
  constructor
  · rintro ⟨ne,none⟩
    exact ⟨ne,fun x hx => none ⟨ne,x,hx⟩⟩
  · rintro ⟨ne,none⟩
    exact ⟨ne,fun ⟨_,x,hx⟩ => none x hx⟩

theorem one_missing (red : ¬ (cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d) (v : V) :
    (missing G v).card=1 := by
  have sub : endpoints G v ⊆ univ.erase v := fun x hx =>
    mem_erase.mpr ⟨((mem_endpoints G).mp hx).1, mem_univ x⟩
  have ep : (endpoints G v).card = d*(d-1) := by
    rw [card_endpoints G red]
    simp [reg]
  unfold missing
  rw [card_sdiff_of_subset sub, card_erase_of_mem (mem_univ v), card_univ, count, ep]
  omega

noncomputable def mate (red : ¬ (cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d) (v : V) : V :=
  Classical.choose (Finset.card_eq_one.mp (one_missing G red count reg v))

theorem singleton_mate (red : ¬ (cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d) (v : V) :
    missing G v = {mate G red count reg v} :=
  Classical.choose_spec (Finset.card_eq_one.mp (one_missing G red count reg v))

end Deldor14.Star.ExcessOne


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph OMA.ChenStar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
  (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)

theorem mate_spec (v w : V) :
    w = mate G red count reg v ↔ w≠v ∧ common G v w=∅ := by
  rw [← mem_missing, singleton_mate G red count reg, mem_singleton]

theorem mate_ne (v : V) : mate G red count reg v ≠ v := ((mate_spec G red count reg v _).mp rfl).1

theorem mate_involutive : Function.Involutive (mate G red count reg) := by
  intro v
  have spec := (mate_spec G red count reg v _).mp rfl
  symm
  apply (mate_spec G red count reg _ _).mpr
  exact ⟨spec.1.symm, (inter_comm _ _).trans spec.2⟩

theorem codegree_formula (v w : V) :
    ((common G v w).card : ℤ) =
      1 + (if v=w then (d : ℤ)-1 else 0) - (if v=mate G red count reg w then 1 else 0) := by
  classical
  by_cases eq : v=w
  · subst v
    have ne := Ne.symm (mate_ne G red count reg w)
    simp [common, reg, ne]
  · by_cases opposite : v=mate G red count reg w
    · have emp := ((mate_spec G red count reg w v).mp opposite).2
      have emp' : common G v w=∅ := (inter_comm _ _).trans emp
      rw [emp',card_empty,if_neg eq,if_pos opposite]
      norm_num
    · have notemp : common G v w ≠ ∅ := by
        intro emp
        exact opposite ((mate_spec G red count reg w v).mpr ⟨eq,(inter_comm _ _).trans emp⟩)
      have lo := card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr notemp)
      have hi := codeg_le_one G red eq
      have one : (common G v w).card=1 := by omega
      simp [one,eq,opposite]

def walks (v w : V) : ℤ := ∑ a ∈ G.neighborFinset v, ((common G a w).card : ℤ)

theorem walks_expand (x y : V) : walks G x y = ∑ a ∈ G.neighborFinset x, ∑ b ∈ G.neighborFinset y,
    (if G.Adj a b then (1:ℤ) else 0)  := by
  classical
  apply sum_congr rfl
  intro a _
  rw [sum_boole]
  congr 1
  congr 1
  ext b
  simp [common,and_comm]

theorem walks_symm (v w : V) : walks G v w = walks G w v := by
  classical
  rw [walks_expand,walks_expand,Finset.sum_comm]
  simp_rw [G.adj_comm]

theorem walks_formula (v w : V) :
    walks G v w = (d:ℤ) + (if G.Adj v w then (d:ℤ)-1 else 0) -
      (if G.Adj v (mate G red count reg w) then 1 else 0) := by
  classical
  unfold walks
  simp_rw [codegree_formula G red count reg]
  rw [sum_sub_distrib,sum_add_distrib]
  simp [reg]

theorem mate_commutes (v w : V) :
    G.Adj v (mate G red count reg w) ↔ G.Adj w (mate G red count reg v) := by
  classical
  have h := walks_symm G v w
  rw [walks_formula G red count reg,walks_formula G red count reg] at h
  simp only [G.adj_comm w v] at h
  by_cases a : G.Adj v (mate G red count reg w) <;>
    by_cases b : G.Adj w (mate G red count reg v) <;> simp_all <;> omega

theorem mate_preserves (v w : V) :
    G.Adj (mate G red count reg v) (mate G red count reg w) ↔ G.Adj v w := by
  rw [mate_commutes G red count reg, mate_involutive G red count reg, G.adj_comm]

theorem even_edges (S : Finset V) :
    Even (∑ a ∈ S, ∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    simp_rw [sum_insert ha]
    rw [sum_add_distrib]
    have flip : (∑ b ∈ S, (if G.Adj b a then (1:ℤ) else 0)) =
        ∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0) := by
      apply sum_congr rfl
      intro b _
      simp only [G.adj_comm b a]
    rw [flip]
    obtain ⟨k,hk⟩ := ih
    rw [hk]
    exact ⟨(∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0))+k,by rw [if_neg (G.irrefl (v:=a))]; ring⟩

theorem even_diagonal (v : V) : Even (walks G v v) := by
  rw [walks_expand]
  exact even_edges G _

end Deldor14.Star.ExcessOne


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph Matrix
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
  (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)

theorem mate_not_adj_of_even (even : Even d) (v : V) : ¬G.Adj v (mate G red count reg v) := by
  classical
  intro adj
  obtain ⟨z,h⟩ := even_diagonal G v
  rw [walks_formula G red count reg,if_neg (G.irrefl (v:=v)),if_pos adj] at h
  obtain ⟨k,hk⟩ := even
  omega

variable (R : Type*) [CommRing R]

def ones (V : Type*) (R : Type*) [One R] : Matrix V V R := Matrix.of fun _ _ => 1

noncomputable def permutation : Matrix V V R := Matrix.of (fun i j => if i=mate G red count reg j then 1 else 0)

theorem mul_permutation (B : Matrix V V R) (i j : V) :
    (B * permutation G red count reg R) i j = B i (mate G red count reg j) := by
  classical
  simp [Matrix.mul_apply,permutation,mul_ite]

theorem permutation_mul (B : Matrix V V R) (i j : V) :
    (permutation G red count reg R * B) i j = B (mate G red count reg i) j := by
  classical
  have eq (k : V) : i=mate G red count reg k ↔ k=mate G red count reg i := by
    constructor <;> intro h
    · rw [h,mate_involutive G red count reg]
    · rw [h,mate_involutive G red count reg]
  simp [Matrix.mul_apply, permutation, eq, ite_mul]

theorem adj_square_entries (i j : V) :
    ((G.adjMatrix R)^2) i j = ((common G i j).card : R) := by
  classical
  rw [sq,mul_adjMatrix_apply]
  simp only [adjMatrix_apply,sum_boole]
  congr 1
  congr 1
  ext x
  simp [common,and_comm]

theorem adj_square_decomp :
    G.adjMatrix R ^ 2 = ones V R + ((d:R)-1) • (1 : Matrix V V R) - permutation G red count reg R := by
  classical
  ext i j
  have c := codegree_formula G red count reg i j
  rw [adj_square_entries]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, ones, permutation, Matrix.of_apply,
    Matrix.one_apply,smul_eq_mul]
  have lift := congrArg (fun z : ℤ => (z:R)) c
  by_cases same : i=j <;> by_cases opp : i=mate G red count reg j <;>
    first
    | simpa only [if_pos same,if_pos opp,mul_one,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one] using lift
    | simpa only [if_pos same,if_neg opp,mul_one,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero] using lift
    | simpa only [if_neg same,if_pos opp,mul_zero,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero] using lift
    | simpa only [if_neg same,if_neg opp,mul_zero,Int.cast_natCast,Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero] using lift

theorem commute_adj : Commute (G.adjMatrix R) (permutation G red count reg R) := by
  classical
  ext i j
  rw [mul_permutation,permutation_mul]
  simp only [adjMatrix_apply]
  have eq := (mate_commutes G red count reg i j).trans (G.adj_comm j _)
  by_cases h : G.Adj i (mate G red count reg j) <;> simp [h,← eq]

theorem perm_sq : permutation G red count reg R ^ 2 = 1 := by
  classical
  ext i j
  rw [sq,mul_permutation]
  simp only [permutation,Matrix.of_apply,Matrix.one_apply]
  rw [mate_involutive G red count reg j]

theorem perm_ones : permutation G red count reg R * ones V R = ones V R := by
  ext i j
  rw [permutation_mul]
  rfl

theorem ones_perm : ones V R * permutation G red count reg R = ones V R := by
  ext i j
  rw [mul_permutation]
  rfl

include reg in
theorem adj_ones : G.adjMatrix R * ones V R = (d:R) • ones V R := by
  classical
  ext i j
  rw [adjMatrix_mul_apply]
  simp [ones,reg]

end Deldor14.Star.ExcessOne


namespace Deldor14.Star.ExcessOne
open Finset SimpleGraph OMA.ChenStar
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
  (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)

theorem mate_adj_of_odd (odd : Odd d) (v : V) : G.Adj v (mate G red count reg v) := by
  classical
  by_contra avoid
  have h := even_diagonal G v
  rw [walks_formula G red count reg,if_neg (G.irrefl (v:=v)),if_neg avoid,sub_zero,add_zero] at h
  obtain ⟨k,hk⟩ := odd
  obtain ⟨z,hz⟩ := h
  omega

include red count reg in
theorem no_odd_excess [Nonempty V] (large : 3≤d) (odd : Odd d) : False := by
  classical
  let v : V := Classical.arbitrary V
  let m := mate G red count reg
  have single : ∃ u, G.Adj v u ∧ u≠m v := by
    by_contra! no
    have sub : G.neighborFinset v ⊆ {m v} := by
      intro u hu
      exact mem_singleton.mpr (no u ((G.mem_neighborFinset _ _).mp hu))
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,reg,card_singleton] at h
    omega
  obtain ⟨u,vu,ne⟩ := single
  have mu : v ≠ m u := by
    intro eq
    have h : m (m u)=u := mate_involutive G red count reg u
    exact ne (h.symm.trans (congrArg m eq.symm))
  have h := cycle_isContained_of_two_common G mu ne vu
    (mate_adj_of_odd G red count reg odd u).symm (mate_adj_of_odd G red count reg odd v)
    ((mate_preserves G red count reg u v).mpr vu.symm)
  exact red h

end Deldor14.Star.ExcessOne
namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

theorem upper_square_plus_one {q : ℕ} (hq : 2≤q) (even : Even q) :
    number (q^2+1) ≤ q^2+q+2 := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra blue
  have minimum (v : Fin (q^2+q+2)) : q+1 ≤ G.degree v := by
    have small : Gᶜ.degree v < q^2+1 :=
      lt_of_not_ge (fun large => blue (star_isContained_of_le_degree Gᶜ large))
    rw [degree_compl,Fintype.card_fin] at small
    omega
  have count : Fintype.card (Fin (q^2+q+2)) = (q+1)*(q+1-1)+2 := by simp; ring
  have reg := ExcessOne.regular_of_min G red (d:=q+1) (by omega) count minimum
  haveI : Nonempty (Fin (q^2+q+2)) := ⟨⟨0,by omega⟩⟩
  have odd : Odd (q+1) := by obtain ⟨l,hl⟩ := even; exact ⟨l,by omega⟩
  exact ExcessOne.no_odd_excess G red count reg (by omega) odd

theorem field_even_square_plus_one (F : Type*) [Field F] [Fintype F] (even : Even (Fintype.card F)) :
    number (Fintype.card F^2+1) = Fintype.card F^2+Fintype.card F+2 :=
  Nat.le_antisymm (upper_square_plus_one Fintype.one_lt_card even) (field_plus_one F)

end Deldor14.Star


namespace Deldor14.Star.Cubic
open Matrix Finset

theorem identities {V : Type*} [Fintype V] [DecidableEq V] (A M J : Matrix V V ℝ)
    (d : ℝ) (aa : A^2=J+(d-1) • 1-M) (mm : M^2=1) (comm : Commute A M)
    (aj : A*J=d • J) (mj : M*J=J) (jm : J*M=J) :
    let S := A*(1+M)
    S^3-(4*(d-2)) • S = (8*d) • J ∧ S*J = (2*d) • J := by
  let S := A*(1+M)
  change S^3-(4*(d-2)) • S = (8*d) • J ∧ S*J=(2*d) • J
  have pair : (1+M : Matrix V V ℝ)^2=(2:ℝ) • (1+M) := by
    have ms : M*M=1 := by simpa [sq] using mm
    rw [sq]; simp only [add_mul,mul_add,one_mul,mul_one,ms]
    module
  have mx : (J+(d-1) • (1:Matrix V V ℝ)-M)*(1+M) = (2:ℝ) • J + (d-2) • (1+M) := by
    have mm' : M*M=1 := by simpa [sq] using mm
    simp only [sub_mul,add_mul,mul_add,one_mul,mul_one,smul_mul,jm,mm']
    module
  have commute : Commute A (1+M) := (Commute.one_right A).add_right comm
  have sqS : S^2 = (4:ℝ) • J + (2*(d-2)) • (1+M) := by
    change (A*(1+M))^2 = _
    rw [commute.mul_pow,aa,pair,Matrix.mul_smul,mx,smul_add,smul_smul,smul_smul]
    norm_num
  have sp : S*(1+M)=(2:ℝ) • S := by
    change (A*(1+M))*(1+M)=_
    rw [mul_assoc,←sq,pair,Matrix.mul_smul]
  have sj : S*J=(2*d) • J := by
    change (A*(1+M))*J=_
    rw [mul_assoc,add_mul,one_mul,mj,mul_add,aj]
    module
  refine ⟨?_,sj⟩
  rw [show S^3=S*S^2 by rw [←pow_succ'],sqS,mul_add,Matrix.mul_smul,Matrix.mul_smul,sj,sp,
    smul_smul,smul_smul]
  module
end Deldor14.Star.Cubic


namespace Deldor14.Star.SpectralCount
open Finset

/-- The trace and third moment force the degree of an even-regular
excess-one graph to be six. This argument counts the spectrum with
multiplicity, including the zero eigenvalues on the antipodal subspace. -/
theorem degree_six {V : Type*} [Fintype V] (f : V → ℝ) {d : ℕ} (large : 3≤d) (even : Even d)
    (roots : ∀ i, f i=2*d ∨ f i=0 ∨ (f i)^2=4*((d:ℝ)-2))
    (trace : ∑ i, f i=0)
    (moment : ∑ i, ((f i)^3-4*((d:ℝ)-2)*f i)=8*d*((d:ℝ)^2-d+2)) : d=6 := by
  classical
  let big := (univ.filter (fun i => f i=2*d)).card
  let s := Real.sqrt ((d:ℝ)-2)
  have dr : (3:ℝ)≤d := by exact_mod_cast large
  have s_pos : 0<s := Real.sqrt_pos.mpr (by linarith)
  have s_sq : s^2=(d:ℝ)-2 := Real.sq_sqrt (by linarith)
  have row (i) : (f i)^3-4*((d:ℝ)-2)*f i =
      (if f i=2*d then 8*d*((d:ℝ)^2-d+2) else 0) := by
    by_cases top : f i=2*d
    · rw [if_pos top,top]; ring
    · rw [if_neg top]
      rcases roots i with h|h|h
      · contradiction
      · simp [h]
      · linear_combination f i*h
  have tally : (big:ℝ)*(8*d*((d:ℝ)^2-d+2))=8*d*((d:ℝ)^2-d+2) := by
    conv_rhs => rw [← moment]
    simp_rw [row]
    simp [big,Finset.sum_ite]
  have nz : 0 < 8*d*((d:ℝ)^2-d+2) := by nlinarith [sq_nonneg ((d:ℝ)-1),mul_nonneg (by linarith : (0:ℝ)≤d) (sq_nonneg ((d:ℝ)-1))]
  have one : (big:ℝ)=1 := by
    apply (mul_right_cancel₀ nz.ne')
    simpa using tally
  let plus := (univ.filter (fun i => f i=2*s)).card
  let minus := (univ.filter (fun i => f i= -(2*s))).card
  have ds : s<(d:ℝ) := by nlinarith [sq_nonneg (s-1)]
  have sign (i) : f i = (if f i=2*d then 2*(d:ℝ) else 0) +
      (if f i=2*s then 2*s else 0) - (if f i= -(2*s) then 2*s else 0) := by
    rcases roots i with top|zero|other
    · have h1 : (2*(d:ℝ)) ≠ 2*s := by linarith
      have h2 : (2*(d:ℝ)) ≠ -(2*s) := by linarith
      simp [top,h1,h2]
    · rw [zero,if_neg (by linarith),if_neg (by linarith),if_neg (by linarith)]; ring
    · have options : f i=2*s ∨ f i= -(2*s) := by
        have product : (f i-2*s)*(f i+2*s)=0 := by nlinarith
        rcases mul_eq_zero.mp product with h|h
        · left; linarith
        · right; linarith
      rcases options with h|h
      · rw [h,if_neg (by linarith),if_pos rfl,if_neg (by linarith)]; ring
      · rw [h,if_neg (by linarith),if_neg (by linarith),if_pos rfl]; ring
  have trace' : (big:ℝ)*(2*d)+(plus:ℝ)*(2*s)-(minus:ℝ)*(2*s)=0 := by
    calc
      _ = ∑ i : V, ((if f i=2*d then 2*(d:ℝ) else 0) +
        (if f i=2*s then 2*s else 0) - (if f i= -(2*s) then 2*s else 0)) := by
          simp [big,plus,minus,Finset.sum_ite,sum_add_distrib,sum_sub_distrib]
      _ = _ := by simpa only [← sign] using trace
  rw [one] at trace'
  let z : ℤ := (minus:ℤ)-plus
  have val : (d:ℝ)=(z:ℝ)*s := by dsimp [z]; push_cast; linarith
  have sqReal : (d:ℝ)^2=((z:ℝ)^2)*((d:ℝ)-2) := by
    calc
      (d:ℝ)^2 = ((z:ℝ)*s)^2 := congrArg (fun x : ℝ => x^2) val
      _ = _ := by rw [mul_pow,s_sq]
  have eq : (d:ℤ)^2=z^2*((d:ℤ)-2) := by exact_mod_cast sqReal
  have divide : ((d:ℤ)-2)*(z^2-((d:ℤ)+2))=4 := by linear_combination -eq
  have pos : 0<z^2-((d:ℤ)+2) := by
    by_contra! no
    have := mul_nonpos_of_nonneg_of_nonpos (by omega : (0:ℤ)≤(d:ℤ)-2) no
    omega
  have ub : d≤6 := by
    have h := mul_le_mul_of_nonneg_left (show (1:ℤ)≤z^2-((d:ℤ)+2) by omega)
      (show (0:ℤ)≤(d:ℤ)-2 by omega)
    omega
  obtain ⟨k,hk⟩ := even
  have cases : d=4 ∨ d=6 := by omega
  rcases cases with rfl|h
  · norm_num at eq
    by_cases small : -2≤z ∧ z≤2
    · have x := mul_nonneg (show 0≤z+2 by omega) (show 0≤2-z by omega)
      nlinarith
    · have x := mul_nonneg (show 0≤(z-3)*(z+3) by
          rcases le_total z 0 with neg|pos
          · apply mul_nonneg_of_nonpos_of_nonpos <;> omega
          · apply mul_nonneg <;> omega) (by decide : (0:ℤ)≤1)
      nlinarith
  · exact h
end Deldor14.Star.SpectralCount


namespace Deldor14.Star.SpectralMatrix
open Matrix Finset Unitary

/-- Read a cubic trace and a fourth-order annihilating relation on a real
symmetric matrix in an orthonormal eigenbasis. -/
theorem multiplicities {V : Type*} [Fintype V] [DecidableEq V] (S : Matrix V V ℝ)
    (herm : S.IsHermitian) {d : ℕ} (large : 3≤d) (even : Even d)
    (tr : S.trace=0)
    (action : S*(S^3 - (4*((d:ℝ)-2)) • S) = (2*(d:ℝ)) • (S^3-(4*((d:ℝ)-2)) • S))
    (moment : (S^3 - (4*((d:ℝ)-2)) • S).trace=8*d*((d:ℝ)^2-d+2)) : d=6 := by
  classical
  let f := herm.eigenvalues
  let c := 4*((d:ℝ)-2)
  let e := conjStarAlgAut ℝ _ (star herm.eigenvectorUnitary)
  let T := S^3-c • S
  have diagS : e S=diagonal f := by simpa [e,f,Function.comp_def] using herm.conjStarAlgAut_star_eigenvectorUnitary
  have diagT : e T=diagonal (fun i => f i ^ 3-c*f i) := by
    dsimp only [T]
    rw [map_sub,map_pow,map_smul,diagS,diagonal_pow,← diagonal_smul,diagonal_sub]
    rfl
  have h := congrArg e action
  change e (S*T)=e ((2*(d:ℝ)) • T) at h
  rw [map_mul,map_smul,diagS,diagT,diagonal_mul_diagonal] at h
  have root (i : V) : f i=2*d ∨ f i=0 ∨ (f i)^2=4*((d:ℝ)-2) := by
    have ev := congrArg (fun B : Matrix V V ℝ => B i i) h
    simp only [diagonal_apply_eq,Matrix.smul_apply,smul_eq_mul] at ev
    have zero : (f i-2*d)* (f i*(f i^2-c))=0 := by linear_combination ev
    rcases mul_eq_zero.mp zero with top | mid
    · exact Or.inl (sub_eq_zero.mp top)
    · exact Or.inr ((mul_eq_zero.mp mid).imp_right sub_eq_zero.mp)
  have traceConj (B : Matrix V V ℝ) : (e B).trace=B.trace := by
    dsimp only [e]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
  have fm : ∑ i, (f i^3-c*f i)=8*d*((d:ℝ)^2-d+2) := by
    rw [← trace_diagonal,← diagT,traceConj]
    exact moment
  apply SpectralCount.degree_six f large even root _ fm
  simpa [f] using herm.trace_eq_sum_eigenvalues.symm.trans tr
end Deldor14.Star.SpectralMatrix


namespace Deldor14.Star.ExcessOne
open Matrix SimpleGraph Finset

theorem degree_eq_six {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (count : Fintype.card V=d*(d-1)+2) (reg : ∀ v, G.degree v=d)
    (large : 3≤d) (even : Even d) : d=6 := by
  classical
  let A := G.adjMatrix ℝ
  let M := permutation G red count reg ℝ
  let J := ones V ℝ
  let S := A*(1+M)
  have s_entry (i j : V) : S i j = A i j + A i (mate G red count reg j) := by
    change (A*(1+M)) i j = _
    rw [mul_add,mul_one,Matrix.add_apply,mul_permutation]
  have symm : S.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp only [star_trivial,s_entry]
    have j1 := G.adj_comm j i
    have j2 := mate_commutes G red count reg j i
    simp only [A,adjMatrix_apply,j1,j2]
  have zero : S.trace=0 := by
    apply sum_eq_zero
    intro i _
    change S i i=0
    rw [s_entry]
    simp [A,adjMatrix_apply,G.irrefl (v:=i),mate_not_adj_of_even G red count reg even i]
  have aa := adj_square_decomp G red count reg ℝ
  obtain ⟨cubic,sj⟩ := Cubic.identities A M J (d:ℝ) aa (perm_sq G red count reg _)
    (commute_adj G red count reg _) (adj_ones G reg _) (perm_ones G red count reg _) (ones_perm G red count reg _)
  change S^3 - (4*((d:ℝ)-2)) • S = (8*(d:ℝ)) • J at cubic
  change S*J=(2*(d:ℝ)) • J at sj
  apply SpectralMatrix.multiplicities S symm large even zero
  · rw [cubic,Matrix.mul_smul,sj,smul_smul,smul_smul]
    congr 1
    ring
  · rw [cubic,Matrix.trace_smul]
    have jr : J.trace = (Fintype.card V : ℝ) := by simp [J,ones,Matrix.trace,Matrix.diag]
    rw [jr,count,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1≤d)]
    push_cast
    change (8*(d:ℝ)) * _ = _
    ring
end Deldor14.Star.ExcessOne


/-
# A signed obstruction in the degree-six case of the quadrilateral–star bound

The Ramsey bound is due to T. D. Parsons, *Ramsey Graphs and Block Designs, I*
(1975), https://doi.org/10.2307/1997368. Here we isolate a local parity
argument for the signed quotient on sixteen vertices.

In the link of any vertex every point has two neighbors. A triangle in the
link would give a tetrahedron, whose three quadrilaterals cannot all have odd
sign. Thus the link is a hexagon. Write its vertices in cyclic order as
0, 1, 2, 3, 4, 5. Each of the four pairs (0,1), (3,4), (0,3), (1,4) has
another common neighbor besides the center. For either opposite pair, degree
six forces the two indicated common neighbors of consecutive pairs to lie
next to its own common neighbor. The resulting nine vertices carry nine
quadrilaterals in which each edge occurs exactly twice. Summing their odd
sign equations modulo two gives the contradiction.
-/

namespace Deldor14.Star.SignedSix
open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
abbrev Common (p q : V) := G.neighborFinset p ∩ G.neighborFinset q

structure SignedSquares where
  sign : V → V → Bool
  sym : ∀ x y, sign x y = sign y x
  square : ∀ x a y b, x ≠ y → a ≠ b → G.Adj x a → G.Adj a y → G.Adj y b → G.Adj b x →
    Bool.xor (sign x a) (sign a y) ≠ Bool.xor (sign x b) (sign b y)

private theorem xor_odd (a b c d : Bool) (h : a.xor b ≠ c.xor d) :
    (a.toNat + b.toNat + c.toNat + d.toNat)%2 = 1 := by
  revert h
  decide +revert

private theorem circuit (S : SignedSquares G) (p : Fin 9 → V) (inj : Function.Injective p)
    (edge : ∀ i j : Fin 9, (i.val,j.val) ∈ ([(0,1),(0,2),(0,3),(0,4),
      (1,2),(3,4),(1,5),(2,5),(3,6),(4,6),(1,7),(3,7),(2,8),(4,8),
      (5,7),(5,8),(6,7),(6,8)] : List (ℕ × ℕ)) → G.Adj (p i) (p j)) : False := by
  let w (i j : Fin 9) := (S.sign (p i) (p j)).toNat
  have sym (i j) : w i j = w j i := congrArg Bool.toNat (S.sym _ _)
  have quad (i j k l : Fin 9) (hik : i ≠ k) (hjl : j ≠ l)
      (a : G.Adj (p i) (p j)) (b : G.Adj (p j) (p k))
      (c : G.Adj (p k) (p l)) (d : G.Adj (p l) (p i)) :
      (w i j + w j k + w i l + w l k)%2 = 1 :=
    xor_odd _ _ _ _ (S.square _ _ _ _ (inj.ne hik) (inj.ne hjl) a b c d)
-- The nine quadrilaterals use each of their edges twice.
  have h0 := quad 0 1 5 2 (by decide) (by decide) (edge 0 1 (by decide)) (edge 1 5 (by decide)) (edge 2 5 (by decide)).symm (edge 0 2 (by decide)).symm
  have h1 := quad 0 3 6 4 (by decide) (by decide) (edge 0 3 (by decide)) (edge 3 6 (by decide)) (edge 4 6 (by decide)).symm (edge 0 4 (by decide)).symm
  have h2 := quad 0 1 7 3 (by decide) (by decide) (edge 0 1 (by decide)) (edge 1 7 (by decide)) (edge 3 7 (by decide)).symm (edge 0 3 (by decide)).symm
  have h3 := quad 0 2 8 4 (by decide) (by decide) (edge 0 2 (by decide)) (edge 2 8 (by decide)) (edge 4 8 (by decide)).symm (edge 0 4 (by decide)).symm
  have h4 := quad 5 7 6 8 (by decide) (by decide) (edge 5 7 (by decide)) (edge 6 7 (by decide)).symm (edge 6 8 (by decide)) (edge 5 8 (by decide)).symm
  have h5 := quad 5 2 1 7 (by decide) (by decide) (edge 2 5 (by decide)).symm (edge 1 2 (by decide)).symm (edge 1 7 (by decide)) (edge 5 7 (by decide)).symm
  have h6 := quad 5 1 2 8 (by decide) (by decide) (edge 1 5 (by decide)).symm (edge 1 2 (by decide)) (edge 2 8 (by decide)) (edge 5 8 (by decide)).symm
  have h7 := quad 6 4 3 7 (by decide) (by decide) (edge 4 6 (by decide)).symm (edge 3 4 (by decide)).symm (edge 3 7 (by decide)) (edge 6 7 (by decide)).symm
  have h8 := quad 6 3 4 8 (by decide) (by decide) (edge 3 6 (by decide)).symm (edge 3 4 (by decide)) (edge 4 8 (by decide)) (edge 6 8 (by decide)).symm
  simp only [sym 2 1, sym 4 3, sym 5 1, sym 5 2, sym 6 3, sym 6 4, sym 7 1, sym 7 3, sym 7 6, sym 8 2, sym 8 4, sym 8 6] at h0 h1 h2 h3 h4 h5 h6 h7 h8
  omega

section
open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] (A : W → W → Prop) [DecidableRel A]
private abbrev N (a : W) := univ.filter (A a)

private theorem pair_neighbors (deg : ∀ v, (N A v).card=2) {v a b : W} (ne : a≠b)
    (ha : A v a) (hb : A v b) : ∀ t, A v t ↔ t=a ∨ t=b := by
  have sub : ({a,b} : Finset W) ⊆ N A v := by simp only [insert_subset_iff, singleton_subset_iff, N, mem_filter, mem_univ, true_and]; exact ⟨ha,hb⟩
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [deg,ne])
  intro t
  simpa [N] using (Finset.ext_iff.mp eq.symm t)

private theorem another (deg : ∀ v, (N A v).card=2) (v a : W) :
    ∃ b, A v b ∧ b ≠ a := by
  by_contra! bad
  have sub : N A v ⊆ {a} := by
    intro x hx
    exact mem_singleton.mpr (bad x (by simpa [N] using hx))
  have := card_le_card sub
  simp [deg] at this

private theorem closed_full (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬A a a) (deg : ∀v, (N A v).card=2)
    (S : Finset W) (large : 4≤S.card) (closed : ∀u∈S, ∀v, A u v → v∈S) :
    S = univ := by
  by_contra ne
  rw [Finset.eq_univ_iff_forall] at ne
  push Not at ne
  obtain ⟨v,hv⟩ := ne
  let B := insert v (N A v)
  have hB : B.card=3 := by simp [B,N,irr, show (univ.filter (A v)).card=2 from deg v]
  have dis : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro x hx h
    rcases Finset.mem_insert.mp h with rfl|edge
    · exact hv hx
    · exact hv (closed x hx v (sym (by simpa [N] using edge)))
  have bound := Finset.card_le_card (Finset.subset_univ (S ∪ B))
  rw [Finset.card_union_of_disjoint dis,Finset.card_univ,sz,hB] at bound
  omega

private theorem cannot_four (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬A a a) (deg : ∀v, (N A v).card=2) {a b c d : W}
    (ac : a≠c) (bd : b≠d) (ab : A a b) (bc : A b c) (cd : A c d) (da : A d a) : False := by
  have nab : a ≠ b := by rintro rfl; exact irr a ab
  have nbc : b ≠ c := by rintro rfl; exact irr b bc
  have ncd : c ≠ d := by rintro rfl; exact irr c cd
  have nda : d ≠ a := by rintro rfl; exact irr d da
  let S : Finset W := {a,b,c,d}
  have hc : S.card=4 := by simp [S,ac,bd,nab,nbc,ncd,nda.symm]
  have h := closed_full A sz sym irr deg S hc.ge (by
    intro u hu v uv
    simp only [S,mem_insert,mem_singleton] at hu ⊢
    rcases hu with rfl|rfl|rfl|rfl
    · grind [pair_neighbors A deg bd ab (sym da) v]
    · grind [pair_neighbors A deg ac (sym ab) bc v]
    · grind [pair_neighbors A deg bd (sym bc) cd v]
    · grind [pair_neighbors A deg ac da (sym cd) v])
  have hh := congrArg Finset.card h
  rw [hc,card_univ,sz] at hh
  contradiction

private theorem cannot_five (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬A a a) (deg : ∀v, (N A v).card=2)
    (tri : ∀{a b c}, A a b → A b c → A c a → False)
    {a b c d e : W} (ab : A a b) (bc : A b c) (cd : A c d) (de : A d e) (ea : A e a) : False := by
  have distinct : a≠b ∧ a≠c ∧ a≠d ∧ a≠e ∧ b≠c ∧ b≠d ∧ b≠e ∧ c≠d ∧ c≠e ∧ d≠e := by
    grind
  obtain ⟨nab,ac,ad,ae,bc',bd,be,cd',ce,de'⟩ := distinct
  let S : Finset W := {a,b,c,d,e}
  have hc : S.card=5 := by simp [S, *]
  have h := closed_full A sz sym irr deg S (by omega) (by
    intro u hu v uv
    simp only [S,mem_insert,mem_singleton] at hu ⊢
    rcases hu with rfl|rfl|rfl|rfl|rfl
    · grind [pair_neighbors A deg be ab (sym ea) v]
    · grind [pair_neighbors A deg ac (sym ab) bc v]
    · grind [pair_neighbors A deg bd (sym bc) cd v]
    · grind [pair_neighbors A deg ce (sym cd) de v]
    · grind [pair_neighbors A deg ad ea (sym de) v])
  have hh := congrArg Finset.card h
  rw [hc,card_univ,sz] at hh
  contradiction

/-- A triangle-free regular graph of degree two on six points is a hexagon. -/
theorem order_link (sz : Fintype.card W=6) (sym : ∀{a b}, A a b → A b a)
    (irr : ∀a, ¬ A a a) (deg : ∀v, (N A v).card=2)
    (tri : ∀{a b c}, A a b → A b c → A c a → False) :
    ∃ f : Fin 6 ≃ W, ∀ i j, A (f i) (f j) ↔ j=i+1 ∨ i=j+1 := by
  have non : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨a⟩ := non
  obtain ⟨b,ab,_⟩ := another A deg a a
  obtain ⟨c,bc,ca⟩ := another A deg b a
  obtain ⟨d,cd,db⟩ := another A deg c b
  obtain ⟨e,de,ec⟩ := another A deg d c
  obtain ⟨f,ef,fd⟩ := another A deg e d
  have no4 := @cannot_four W _ _ A _ sz sym irr deg
  have no5 := @cannot_five W _ _ A _ sz sym irr deg tri
  have distinct : a≠b ∧ a≠c ∧ a≠d ∧ a≠e ∧ a≠f ∧ b≠c ∧ b≠d ∧ b≠e ∧ b≠f ∧
      c≠d ∧ c≠e ∧ c≠f ∧ d≠e ∧ d≠f ∧ e≠f := by
    have ad : a ≠ d := by rintro rfl; exact tri ab bc cd
    have be : b ≠ e := by rintro rfl; exact tri bc cd de
    have cf : c ≠ f := by rintro rfl; exact tri cd de ef
    have ae : a ≠ e := by rintro rfl; exact no4 ca.symm db.symm ab bc cd de
    have bf : b ≠ f := by rintro rfl; exact no4 db.symm ec.symm bc cd de ef
    have af : a ≠ f := by rintro rfl; exact no5 ab bc cd de ef
    grind
  let t : Fin 6 → W := ![a,b,c,d,e,f]
  have inj : Function.Injective t := by
    intro i j h
    fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [t] at h; grind only)
  let E := Equiv.ofBijective t ((Fintype.bijective_iff_injective_and_card t).mpr ⟨inj,by simpa [sz]⟩)
  have fa : A f a := by
    obtain ⟨g,fg,ge⟩ := another A deg f e
    obtain ⟨i,hi⟩ := E.surjective g
    change t i = g at hi
    fin_cases i <;> simp [t] at hi <;> subst g
    · exact fg
    · exact (no5 bc cd de ef fg).elim
    · exact (no4 ec.symm fd.symm cd de ef fg).elim
    · exact (tri de ef fg).elim
    · contradiction
    · exact (irr _ fg).elim
  have cycle (i : Fin 6) : A (E i) (E (i+1)) := by
    fin_cases i <;> first | exact ab | exact bc | exact cd | exact de | exact ef | exact fa
  refine ⟨E,fun i j => ?_⟩
  have prev (i : Fin 6) : (i-1)+1 = i := by omega
  have diff (i : Fin 6) : i+1 ≠ i-1 := by decide +revert
  have back : A (E i) (E (i-1)) := by simpa only [prev] using sym (cycle (i-1))
  rw [pair_neighbors A deg (E.injective.ne (diff i)) (cycle i) back (E j)]
  simp only [Equiv.apply_eq_iff_eq]
  omega


end

section
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem small_common {p q a b : V} (hab : a ≠ b) (c : (G.neighborFinset p ∩ G.neighborFinset q).card = 2)
    (pa : G.Adj p a) (qa : G.Adj q a) (pb : G.Adj p b) (qb : G.Adj q b) :
    ∀ t, G.Adj p t ∧ G.Adj q t ↔ t=a ∨ t=b := by
  have sub : ({a,b} : Finset V) ⊆ G.neighborFinset p ∩ G.neighborFinset q := by
    simp only [insert_subset_iff, singleton_subset_iff, mem_inter, mem_neighborFinset]; exact ⟨⟨pa,qa⟩,⟨pb,qb⟩⟩
  have eq := Finset.eq_of_subset_of_card_le sub (by simp [c,hab])
  intro t
  simpa using (Finset.ext_iff.mp eq.symm t)

private theorem second_common (com : ∀ p q : V, p≠q → (G.neighborFinset p ∩ G.neighborFinset q).card=2)
    (p q o : V) (ne : p ≠ q) : ∃ x, x≠o ∧ G.Adj p x ∧ G.Adj q x := by
  by_contra! no
  have sub : G.neighborFinset p ∩ G.neighborFinset q ⊆ {o} := by
    intro t ht
    obtain ⟨pt,qt⟩ : G.Adj p t ∧ G.Adj q t := by simpa using ht
    by_contra! h
    exact no t (by simpa using h) pt qt
  have c := card_le_card sub
  simp [com p q ne] at c

/-- Four neighbors that cannot occur in the intersection force either of the
two remaining neighbors into it. -/
private theorem force_edge {p x e o l r : V} (degree : G.degree p=6)
    (co : (G.neighborFinset p ∩ G.neighborFinset x).card=2)
    (pO : G.Adj p o) (pL : G.Adj p l) (pR : G.Adj p r) (pX : G.Adj p x)
    (nO : ¬G.Adj x o) (nL : ¬G.Adj x l) (nR : ¬G.Adj x r)
    (ol : o≠l) (orr : o≠r) (ox : o≠x) (lr : l≠r) (lx : l≠x) (rx : r≠x)
    (pe : G.Adj p e) (eo : e≠o) (el : e≠l) (er : e≠r) (ex : e≠x) : G.Adj x e := by
  let C := G.neighborFinset p ∩ G.neighborFinset x
  let F : Finset V := {o,l,r,x}
  have cf : F.card=4 := by simp [F,ol,orr,ox,lr,lx,rx]
  have dis : Disjoint F C := by
    simp [F,C,nO,nL,nR]
  have inc : F ∪ C ⊆ G.neighborFinset p := by
    apply union_subset
    · simp only [F,insert_subset_iff,singleton_subset_iff,mem_neighborFinset]
      exact ⟨pO,pL,pR,pX⟩
    · exact inter_subset_left
  have eq := Finset.eq_of_subset_of_card_le inc (by
    rw [card_union_of_disjoint dis,cf,show C.card=2 from co,card_neighborFinset_eq_degree,degree])
  have he : e∈F ∪ C := eq.symm ▸ ((G.mem_neighborFinset p e).mpr pe)
  simpa [F,C,pe,eo,el,er,ex] using he


end

private theorem from_hexagon {o : V} (S : SignedSquares G)
    (reg : ∀ p, G.degree p=6) (com : ∀ p q : V, p≠q → (G.neighborFinset p ∩ G.neighborFinset q).card=2)
    (f : Fin 6 → V) (inj : Function.Injective f)
    (link : ∀ w, G.Adj o w ↔ ∃ i, f i=w)
    (cycle : ∀ i j, G.Adj (f i) (f j) ↔ j=i+1 ∨ i=j+1) : False := by
  let L : Fin 4 → Fin 6 := ![0,3,0,1]
  let R : Fin 4 → Fin 6 := ![1,4,3,4]
  have lr : ∀ k, L k ≠ R k := by decide
  choose X xo xl xr using fun k => second_common G com (f (L k)) (f (R k)) o (inj.ne (lr k))
  have localAdj (i) := (link (f i)).mpr ⟨i,rfl⟩
  have fno (i) : f i≠o := (localAdj i).ne.symm
  have noLocal : ∀ k i, ¬((i=L k+1 ∨ L k=i+1) ∧ (i=R k+1 ∨ R k=i+1)) := by decide
  have xf (k i) : X k ≠ f i := by
    intro h
    have a := xl k; have b := xr k
    rw [h,cycle] at a b
    exact noLocal k i ⟨a,b⟩
  have xOutside (k) : ¬G.Adj o (X k) := by
    intro h
    obtain ⟨i,hi⟩ := (link _).mp h
    exact xf k i hi.symm
  have adjX (k i) : G.Adj (X k) (f i) ↔ i=L k ∨ i=R k := by
    have h := small_common G (inj.ne (lr k)) (com o (X k) (xo k).symm)
      (localAdj _) (xl k).symm (localAdj _) (xr k).symm (f i)
    simpa only [localAdj,true_and,inj.eq_iff] using h
  have unique : ∀ k j, (∀ i, (i=L k ∨ i=R k) ↔ (i=L j ∨ i=R j)) → k=j := by decide
  have xi : Function.Injective X := by
    intro k j kj
    exact unique k j fun i => (adjX k i).symm.trans (kj ▸ adjX j i)
  have force (k j : Fin 4) (t l r : Fin 6) (kj : k≠j)
      (hx : t=L k ∨ t=R k) (he : t=L j ∨ t=R j) (tl : l=t+1 ∨ t=l+1)
      (tr : r=t+1 ∨ t=r+1) (lr' : l≠r) (noL : ¬(l=L k ∨ l=R k)) (noR : ¬(r=L k ∨ r=R k)) :
      G.Adj (X k) (X j) :=
    force_edge G (reg _) (com _ _ (xf k t).symm)
      (localAdj t).symm ((cycle t l).mpr tl) ((cycle t r).mpr tr) ((adjX k t).mpr hx).symm
      (fun a => xOutside k a.symm) (fun a => noL ((adjX k l).mp a))
      (fun a => noR ((adjX k r).mp a)) (fno l).symm (fno r).symm (xo k).symm (inj.ne lr')
      (xf k l).symm (xf k r).symm ((adjX j t).mpr he).symm (xo j) (xf j l) (xf j r) (xi.ne kj.symm)
  have fe1 : G.Adj (X 0) (X 2) := (force 2 0 0 1 5 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  have fe2 : G.Adj (X 0) (X 3) := (force 3 0 1 2 0 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  have fe3 : G.Adj (X 1) (X 2) := (force 2 1 3 4 2 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  have fe4 : G.Adj (X 1) (X 3) := (force 3 1 4 5 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).symm
  let emb : Unit ⊕ (Fin 6 ⊕ Fin 4) → V := Sum.elim (fun _ => o) (Sum.elim f X)
  have ei : Function.Injective emb := by
    intro i j h
    rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp [emb] at h ⊢
    all_goals first | exact (fno _ h).elim | exact (fno _ h.symm).elim | exact (xo _ h).elim
                         | exact (xo _ h.symm).elim | exact (xf _ _ h).elim | exact (xf _ _ h.symm).elim
                         | exact inj h | exact xi h
  let lab : Fin 9 → Unit ⊕ (Fin 6 ⊕ Fin 4) := ![.inl (),.inr (.inl 0), .inr (.inl 1),
    .inr (.inl 3),.inr (.inl 4),.inr (.inr 0),.inr (.inr 1),.inr (.inr 2),.inr (.inr 3)]
  have li : Function.Injective lab := by decide
  apply circuit G S (emb ∘ lab) (ei.comp li)
  intro i j h
  fin_cases i <;> fin_cases j <;> first | exact False.elim (by revert h; decide)
                                        | exact localAdj _
                                        | exact ((cycle _ _).mpr (by decide))
                                        | exact ((adjX _ _).mpr (by decide)).symm
                                        | exact fe1 | exact fe2 | exact fe3 | exact fe4

private theorem no_tetra (S : SignedSquares G) {o a b c : V}
    (oa : G.Adj o a) (ob : G.Adj o b) (oc : G.Adj o c)
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a) : False := by
  have h0 := xor_odd _ _ _ _ (S.square o b a c oa.ne bc.ne ob ab.symm ca.symm oc.symm)
  have h1 := xor_odd _ _ _ _ (S.square o a b c ob.ne ca.ne.symm oa ab bc oc.symm)
  have h2 := xor_odd _ _ _ _ (S.square o a c b oc.ne ab.ne oa ca.symm bc.symm ob.symm)
  rw [S.sym b a] at h0
  rw [S.sym c b] at h1
  rw [S.sym c a] at h0
  omega

/-- The signed quotient required by the putative 6-regular graph is impossible. -/
theorem quotient_six_impossible (card : Fintype.card V = 16) (reg : ∀ v, G.degree v = 6)
    (com : ∀ x y, x ≠ y → (G.neighborFinset x ∩ G.neighborFinset y).card = 2)
    (sign : V → V → Bool) (sym : ∀ x y, sign x y = sign y x)
    (square : ∀ x a y b, x ≠ y → a ≠ b → G.Adj x a → G.Adj a y → G.Adj y b → G.Adj b x →
      Bool.xor (sign x a) (sign a y) ≠ Bool.xor (sign x b) (sign b y)) : False := by
  let S : SignedSquares G := ⟨sign,sym,square⟩
  obtain ⟨o⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card V by omega)
  let W : Type _ := ↑(G.neighborFinset o)
  let A (a b : W) : Prop := G.Adj a.val b.val
  letI : DecidableRel A := fun x y => inferInstanceAs (Decidable (G.Adj x.val y.val))
  have local_sz : Fintype.card W=6 := by
    change Fintype.card (↑(G.neighborFinset o) : Type _) = 6
    rw [Fintype.card_coe]; exact reg o
  have spoke (x : W) : G.Adj o x.val := (G.mem_neighborFinset o x.val).mp x.property
  have deg (v : W) : (univ.filter (A v)).card=2 := by
    calc (univ.filter (A v)).card = (G.neighborFinset o ∩ G.neighborFinset v.val).card := by
           apply Finset.card_bij (fun x _ => x.val)
           · intro x hx
             exact mem_inter.mpr ⟨x.property, (mem_neighborFinset G _ _).mpr (mem_filter.mp hx).2⟩
           · intro a _ b _ eq
             exact Subtype.ext eq
           · intro x hx
             obtain ⟨ox,vx⟩ := mem_inter.mp hx
             exact ⟨⟨x,ox⟩,mem_filter.mpr ⟨mem_univ _, (mem_neighborFinset G _ _).mp vx⟩,rfl⟩
         _ = 2 := com o v.val (spoke v).ne
  have tri {a b c : W} (ab : A a b) (bc : A b c) (ca : A c a) : False :=
    no_tetra G S (spoke a) (spoke b) (spoke c) ab bc ca
  obtain ⟨f,hf⟩ := order_link A local_sz (fun h => h.symm) (fun x => G.irrefl) deg tri
  refine from_hexagon (o := o) G S reg com (fun i => (f i).val) (Subtype.val_injective.comp f.injective) ?_ hf
  intro w
  constructor
  · intro hw
    let v : W := ⟨w,(mem_neighborFinset G _ _).mpr hw⟩
    obtain ⟨i,hi⟩ := f.surjective v
    exact ⟨i,congrArg Subtype.val hi⟩
  · rintro ⟨i,rfl⟩
    exact spoke (f i)

end Deldor14.Star.SignedSix


/- The antipodal quotient of a six-regular graph of order 32. -/
namespace Deldor14.Star.SignedQuotient
open SimpleGraph Finset Deldor14.Star.ExcessOne

private structure Cover {X Q : Type*} (G : SimpleGraph X) where
  lift : Q × Bool ≃ X
  flip : ∀ x y : Q, G.Adj (lift (x,true)) (lift (y,true)) ↔ G.Adj (lift (x,false)) (lift (y,false))
  cross : ∀ x y : Q, G.Adj (lift (x,false)) (lift (y,true)) ↔ G.Adj (lift (y,false)) (lift (x,true))
  separate : ∀ x : Q, ¬G.Adj (lift (x,false)) (lift (x,true))
  exclusive : ∀ (y : Q) (u : X), ¬(G.Adj u (lift (y,false)) ∧ G.Adj u (lift (y,true)))

variable {X Q : Type*} {G : SimpleGraph X}

private def project (s : Cover (Q:=Q) G) : SimpleGraph Q where
  Adj x y := G.Adj (s.lift (x,false)) (s.lift (y,false)) ∨ G.Adj (s.lift (x,false)) (s.lift (y,true))
  symm := ⟨fun {_ _} h => h.elim (fun e=>Or.inl e.symm) (fun e=>Or.inr ((s.cross ..).mp e))⟩
  loopless := ⟨fun x h=>h.elim (G.irrefl) (s.separate x)⟩

private def sign [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (x y : Q) :=
  decide (G.Adj (s.lift (x,false)) (s.lift (y,true)))

private theorem sign_symm [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (x y : Q) :
    sign s x y=sign s y x := by simp [sign,s.cross x y]

private theorem lift_adj [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (x y : Q) (i j : Bool) :
    G.Adj (s.lift (x,i)) (s.lift (y,j)) ↔
      (project s).Adj x y ∧ (Bool.xor i j)=sign s x y := by
  have excl := s.exclusive y (s.lift (x,false))
  have cross : G.Adj (s.lift (x,true)) (s.lift (y,false)) ↔ G.Adj (s.lift (x,false)) (s.lift (y,true)) :=
    (G.adj_comm _ _).trans (s.cross y x)
  cases i <;> cases j <;> simp only [Bool.false_xor,Bool.true_xor,Bool.not_true,Bool.not_false,
    sign,project,s.flip,cross]
  all_goals by_cases h : G.Adj (s.lift (x,false)) (s.lift (y,true)) <;> simp_all

private def side (s : Cover (Q:=Q) G) [DecidableRel G.Adj] (x y : Q) := s.lift (y,sign s x y)

private theorem side_bij (s : Cover (Q:=Q) G) [Fintype X] [DecidableRel G.Adj] [Fintype Q]
    [DecidableRel (project s).Adj] (x : Q) :
    Set.BijOn (side s x) ((project s).neighborFinset x : Set Q) (G.neighborFinset (s.lift (x,false)) : Set X) := by
  refine ⟨?_,?_,?_⟩
  · intro y hy
    exact (G.mem_neighborFinset ..).mpr ((lift_adj s x y false _).mpr ⟨((project s).mem_neighborFinset ..).mp hy,by simp⟩)
  · intro a _ b _ hh
    exact congrArg Prod.fst (s.lift.injective hh)
  · intro z hz
    obtain ⟨⟨y,j⟩,rfl⟩ := s.lift.surjective z
    obtain ⟨adj,eq⟩ := (lift_adj s x y false j).mp ((G.mem_neighborFinset ..).mp hz)
    refine ⟨y,((project s).mem_neighborFinset ..).mpr adj,?_⟩
    rw [Bool.false_xor] at eq
    exact congrArg (fun b=>s.lift (y,b)) eq.symm

private theorem degree_proj (s : Cover (Q:=Q) G) [Fintype X] [DecidableRel G.Adj] [Fintype Q]
    [DecidableRel (project s).Adj] (x : Q) :
    (project s).degree x=G.degree (s.lift (x,false)) := by
  have h := side_bij s x
  simpa using card_nbij (side s x) h.mapsTo h.injOn h.surjOn

private theorem either_lift [DecidableRel G.Adj] (s : Cover (Q:=Q) G) (y z : Q) (j : Bool) :
    (project s).Adj y z ↔ G.Adj (s.lift (y,false)) (s.lift (z,j)) ∨
      G.Adj (s.lift (y,true)) (s.lift (z,j)) := by
  rw [lift_adj,lift_adj]
  cases j <;> cases h : sign s y z <;> simp

private theorem codegree_proj (s : Cover (Q:=Q) G) [Fintype X] [DecidableEq X] [DecidableRel G.Adj]
    [Fintype Q] [DecidableEq Q] [DecidableRel (project s).Adj] (x y : Q)
    (one : ∀ j,(common G (s.lift (x,false)) (s.lift (y,j))).card=1) :
    (common (project s) x y).card=2 := by
  let C (j : Bool) := common G (s.lift (x,false)) (s.lift (y,j))
  have dis : Disjoint (C false) (C true) := by
    apply Finset.disjoint_left.mpr
    intro z hz hw
    exact s.exclusive y z ⟨((mem_common G).mp hz).2.symm,((mem_common G).mp hw).2.symm⟩
  have e : (common (project s) x y).card=(C false ∪ C true).card := by
    apply Finset.card_bij' (fun z _=>side s x z) (fun u _=>(s.lift.symm u).1)
    · intro z hz
      have adj := (mem_common _).mp hz
      have a := (lift_adj s x z false (sign s x z)).mpr ⟨adj.1,by simp⟩
      exact mem_union.mpr (((either_lift s y z _).mp adj.2).imp (fun h=>(mem_common G).mpr ⟨a,h⟩) (fun h=>(mem_common G).mpr ⟨a,h⟩))
    · intro u hu
      obtain ⟨⟨z,j⟩,rfl⟩ := s.lift.surjective u
      simp only [Equiv.symm_apply_apply]
      rcases mem_union.mp hu with h|h <;> obtain ⟨a,b⟩ := (mem_common G).mp h
      · exact (mem_common _).mpr ⟨((lift_adj s x z false j).mp a).1,((lift_adj s y z false j).mp b).1⟩
      · exact (mem_common _).mpr ⟨((lift_adj s x z false j).mp a).1,((lift_adj s y z true j).mp b).1⟩
    · intro z _; simp [side]
    · intro u hu
      obtain ⟨⟨z,j⟩,rfl⟩ := s.lift.surjective u
      have a : G.Adj (s.lift (x,false)) (s.lift (z,j)) := (mem_union.mp hu).elim (fun h=>((mem_common G).mp h).1) (fun h=>((mem_common G).mp h).1)
      have eq := ((lift_adj s x z false j).mp a).2
      simpa [side] using congrArg (fun i=>s.lift (z,i)) eq.symm
  rw [e,card_union_of_disjoint dis,show (C false).card=1 from one false,show (C true).card=1 from one true]

private theorem signed_square (s : Cover (Q:=Q) G) [Fintype X] [DecidableEq X] [DecidableRel G.Adj]
    (red : ¬ (cycleGraph 4).IsContained G) (x a y b : Q) (xy : x≠y) (ab : a≠b)
    (xa : (project s).Adj x a) (ay : (project s).Adj a y) (yb : (project s).Adj y b) (bx : (project s).Adj b x) :
    (Bool.xor (sign s x a) (sign s a y)) ≠ (Bool.xor (sign s x b) (sign s b y)) := by
  intro eq
  let v := Bool.xor (sign s x a) (sign s a y)
  have f (c : Q) (xc : (project s).Adj x c) (cy : (project s).Adj c y)
      (hh : v=Bool.xor (sign s x c) (sign s c y)) : side s x c∈common G (s.lift (x,false)) (s.lift (y,v)) := by
    apply (mem_common G).mpr
    refine ⟨(lift_adj s x c false _).mpr ⟨xc,by simp⟩,((lift_adj s c y _ v).mpr ⟨cy,?_⟩).symm⟩
    rw [hh]; cases sign s x c <;> cases sign s c y <;> rfl
  have under : s.lift (x,false)≠s.lift (y,v) := fun h=>xy (congrArg Prod.fst (s.lift.injective h))
  have eq' := Finset.card_le_one.mp (codeg_le_one G red under) (side s x a) (f a xa ay rfl) (side s x b) (f b bx.symm yb.symm eq)
  exact ab (congrArg Prod.fst (s.lift.injective eq'))

private def splitSides {A : Type*} (P : A→Prop) [DecidablePred P]
    (m : A→A) (mm : Function.Involutive m) (switch : ∀ x,P (m x) ↔ ¬P x) :
    A ≃ Subtype P × Bool where
  toFun x := if h : P x then (⟨x,h⟩,false) else (⟨m x,(switch x).mpr h⟩,true)
  invFun x := if x.2 then m x.1.val else x.1.val
  left_inv x := by by_cases h : P x <;> simp [h,mm x]
  right_inv := by
    rintro ⟨⟨x,hx⟩,b⟩
    cases b
    · simp [hx]
    · simp [show ¬P (m x) from fun z=>(switch x).mp z hx,mm x]

theorem regular_six_from_quotient
    (obstruction : ∀ {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj],
      Fintype.card W=16 → (∀ x,H.degree x=6) →
      (∀ x y,x≠y → (H.neighborFinset x ∩ H.neighborFinset y).card=2) →
      ∀ (sig : W→W→Bool), (∀ x y,sig x y=sig y x) →
      (∀ x a y b,x≠y → a≠b → H.Adj x a → H.Adj a y → H.Adj y b → H.Adj b x →
        (Bool.xor (sig x a) (sig a y)) ≠ (Bool.xor (sig x b) (sig b y))) → False)
    (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj] (red : ¬(cycleGraph 4).IsContained G)
    (reg : ∀ v,G.degree v=6) : False := by
  classical
  have count : Fintype.card (Fin 32)=6*(6-1)+2 := by decide
  let m := mate G red count reg
  have mm : Function.Involutive m := mate_involutive G red count reg
  have fixed := mate_ne G red count reg
  let P (x : Fin 32) := x < m x
  have switch (x : Fin 32) : P (m x) ↔ ¬P x := by
    change m x < m (m x) ↔ ¬x < m x
    rw [mm]
    exact ⟨not_lt_of_gt,fun h=>lt_of_le_of_ne (le_of_not_gt h) (fixed x)⟩
  let W := Subtype P
  let L : W × Bool ≃ Fin 32 := (splitSides P m mm switch).symm
  have neg (x : W) : L (x,false)=x.val := rfl
  have pos (x : W) : L (x,true)=m x.val := rfl
  have toggle (x : W) (j : Bool) : m (L (x,j))=L (x,!j) := by
    cases j with
    | false => rfl
    | true => exact mm x.val
  let s : Cover (Q:=W) G := {
    lift := L
    flip := fun x y => mate_preserves G red count reg x.val y.val
    cross := fun x y => mate_commutes G red count reg x.val y.val
    separate := fun x=>mate_not_adj_of_even G red count reg (by decide) x.val
    exclusive := by
      intro y u hh
      have z : u∈common G y.val (m y.val) := (mem_common G).mpr ⟨hh.1.symm,hh.2.symm⟩
      have emp := ((mate_spec G red count reg y.val (m y.val)).mp rfl).2
      rw [emp] at z
      exact notMem_empty u z }
  let : Fintype W := Fintype.ofFinite W
  let : DecidableRel (project s).Adj := Classical.decRel _
  have cw : Fintype.card W=16 := by
    have c := Fintype.card_congr L
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at c
    omega
  have com (x y : W) (ne : x≠y) (j : Bool) : (common G (L (x,false)) (L (y,j))).card=1 := by
    have distinct (k : Bool) : L (x,false)≠L (y,k) := fun e=>ne (congrArg Prod.fst (L.injective e))
    have other : L (x,false)≠mate G red count reg (L (y,j)) := by
      change L (x,false)≠m (L (y,j))
      rw [toggle]
      exact distinct _
    have c := codegree_formula G red count reg (L (x,false)) (L (y,j))
    rw [if_neg (distinct j),if_neg other] at c
    omega
  exact obstruction (project s) cw (fun x=>(degree_proj s x).trans (reg _))
    (fun x y ne=>codegree_proj s x y (com x y ne)) (sign s) (sign_symm s) (signed_square s red)

end Deldor14.Star.SignedQuotient


namespace Deldor14.Star.SignedQuotient
open SimpleGraph

theorem six_regular_impossible (G : SimpleGraph (Fin 32)) [DecidableRel G.Adj]
    (red : ¬(cycleGraph 4).IsContained G) (reg : ∀ x,G.degree x=6) : False :=
  regular_six_from_quotient (@Deldor14.Star.SignedSix.quotient_six_impossible) G red reg

end Deldor14.Star.SignedQuotient


namespace Deldor14.Star
open SimpleGraph OMA.ChenStar

/-- The upper bound at one more than a square, including the last exceptional order. -/
theorem parsons_upper_plus_one {q : ℕ} (hq : 2≤q) :
    number (q^2+1)≤q^2+q+2 := by
  classical
  rcases Nat.even_or_odd q with h|h
  · exact upper_square_plus_one hq h
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra bad
  have min (v) : q+1 ≤ G.degree v := by
    have lt : Gᶜ.degree v<q^2+1 :=
      lt_of_not_ge (fun ge => bad (star_isContained_of_le_degree Gᶜ ge))
    rw [degree_compl,Fintype.card_fin] at lt
    omega
  have count : Fintype.card (Fin (q^2+q+2)) = (q+1)*(q+1-1)+2 := by simp; ring
  have reg := ExcessOne.regular_of_min G red (d:=q+1) (by omega) count min
  have he : Even (q+1) := by obtain ⟨k,hk⟩ := h; exact ⟨k+1,by omega⟩
  have := ExcessOne.degree_eq_six G red count reg (by omega) he
  have five : q=5 := by omega
  subst q
  exact SignedQuotient.six_regular_impossible G red reg

/-- Parsons' square-plus-one value of the quadrilateral-star Ramsey number. -/
theorem field_plus_one_exact (F : Type*) [Fintype F] [Field F] :
    number (Fintype.card F^2+1) = Fintype.card F^2+Fintype.card F+2 :=
  Nat.le_antisymm (parsons_upper_plus_one Fintype.one_lt_card) (field_plus_one F)

end Deldor14.Star


/- X. Zhang, Y. Chen and T. C. E. Cheng, Polarity graphs and Ramsey numbers for C₄ versus stars (2017), https://doi.org/10.1016/j.disc.2016.12.005. -/
namespace Deldor14.Star.OddWindow
open Finset
theorem choose_pairs {α : Type*} [DecidableEq α] (f : α → α) (sq : Function.Involutive f)
    (U : Finset α) (stable : ∀ x∈U,f x∈U) (free : ∀ x∈U,f x≠x) :
    ∃ k, U.card=2*k ∧ ∀ i≤k,∃ T : Finset α, T⊆U ∧ T.card=2*i ∧ ∀ x∈T,f x∈T := by
  induction U using Finset.strongInduction with
  | H U ih =>
    rcases U.eq_empty_or_nonempty with eq|⟨x,hx⟩
    · subst U
      exact ⟨0,rfl,by intro i hi; have := Nat.eq_zero_of_le_zero hi; subst i; exact ⟨∅,by simp⟩⟩
    let y := f x
    have hy : y∈U := stable x hx
    have dif : y≠x := free x hx
    let V := (U.erase x).erase y
    have inside : V⊆U := (erase_subset ..).trans (erase_subset ..)
    have smaller : V ⊂ U := Finset.ssubset_iff_subset_ne.mpr ⟨inside,fun he => by
      have : x∈V := he ▸ hx
      simp [V] at this⟩
    have vc : V.card + 2 = U.card := by
      have first := card_erase_add_one hx
      have second := card_erase_add_one (mem_erase.mpr ⟨dif,hy⟩ : y∈U.erase x)
      dsimp [V]
      omega
    have sv (a) (ha : a∈V) : f a∈V := by
      obtain ⟨ay,ax,au⟩ := show a≠y ∧ a≠x ∧ a∈U by simpa [V] using ha
      have ex : f a≠x := fun e => ay (by simpa [y,sq a] using congrArg f e)
      have ey : f a≠y := fun e => ax (sq.injective e)
      simp [V,ex,ey,stable a au]
    obtain ⟨k,hk,sub⟩ := ih V smaller sv (fun a ha=>free a (inside ha))
    refine ⟨k+1,by omega,?_⟩
    intro i hi
    cases i with
    | zero => exact ⟨∅,by simp⟩
    | succ i =>
      obtain ⟨T,hT,cT,sT⟩ := sub i (by omega)
      have xn : x∉T := by intro h; have := hT h; simp [V] at this
      have yn : y∉T := by intro h; have := hT h; simp [V] at this
      refine ⟨insert x (insert y T),?_,?_,?_⟩
      · exact insert_subset hx (insert_subset hy (hT.trans inside))
      · rw [card_insert_of_notMem (by simp [dif.symm,xn]),card_insert_of_notMem yn,cT]
        omega
      · intro a ha
        rcases mem_insert.mp ha with rfl|h
        · exact mem_insert_of_mem (mem_insert_self ..)
        rcases mem_insert.mp h with e|h
        · rw [e,show f y=x from sq x]; simp
        · exact mem_insert_of_mem (mem_insert_of_mem (sT _ h))
end Deldor14.Star.OddWindow

/- Count the points of the hyperbola by factoring its equation. -/
namespace Deldor14.Star.OddWindow
open Finset
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private abbrev Conic (F : Type*) [Field F] := {p : F × F // p.2^2=p.1^2+1}

private def toUnit (p : Conic F) : Fˣ where
  val := p.val.2 + p.val.1
  inv := p.val.2 - p.val.1
  val_inv := by linear_combination p.property
  inv_val := by linear_combination p.property

private def ofUnit (two : (2:F)≠0) (u : Fˣ) : Conic F :=
  ⟨⟨((u:F)-(↑u⁻¹:F))/2,((u:F)+(↑u⁻¹:F))/2⟩,by
    dsimp
    field_simp
    linear_combination 4 * (Units.val_inv u)⟩

private def hyperbola (two : (2:F)≠0) : Conic F ≃ Fˣ where
  toFun := toUnit
  invFun := ofUnit two
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · change ((p.val.2+p.val.1)-(p.val.2-p.val.1))/2 = p.val.1
      field_simp; ring
    · change ((p.val.2+p.val.1)+(p.val.2-p.val.1))/2 = p.val.2
      field_simp; ring
  right_inv u := by
    apply Units.ext
    change ((u:F)+↑u⁻¹)/2+((u:F)-↑u⁻¹)/2=(u:F)
    field_simp; ring

private def fibers : (Σ a : F,{y : F // y^2=a^2+1}) ≃ Conic F where
  toFun := fun ⟨a,y⟩ => ⟨(a,y.val),y.property⟩
  invFun := fun p => ⟨p.val.1,p.val.2,p.property⟩
  left_inv := by rintro ⟨a,⟨y,h⟩⟩; rfl
  right_inv := by rintro ⟨⟨a,y⟩,h⟩; rfl

private def solutions (x : F) := univ.filter fun y : F => y^2=x
private theorem sum_solutions (two : (2:F)≠0) :
    ∑ a : F,(solutions (a^2+1)).card = Fintype.card F-1 := by
  have e := Fintype.card_congr (fibers.trans (hyperbola two))
  simpa [Fintype.card_sigma,Fintype.card_subtype,solutions,Fintype.card_units] using e

def zeroSet (F : Type*) [Field F] [Fintype F] [DecidableEq F] := univ.filter (fun a : F=>a^2+1=0)
noncomputable def dark (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F := by
  classical exact univ.filter (fun a : F=>¬∃y : F,y^2=a^2+1)

private theorem sols_nonzero (two : (2:F)≠0) {x : F} (hx : x≠0) (y : F) (hy : y^2=x) :
    (solutions x).card=2 := by
  have nz : y≠0 := by intro e; simp [e] at hy; exact hx hy.symm
  have dif : y≠-y := by
    intro e
    exact (mul_ne_zero two nz) (by linear_combination e)
  have set : solutions x = {y,-y} := by
    ext z
    simp only [solutions,mem_filter,mem_univ,true_and,mem_insert,mem_singleton]
    rw [←hy]
    exact sq_eq_sq_iff_eq_or_eq_neg
  simp [set,dif]

theorem zero_count (two : (2:F)≠0) : (zeroSet F).card=0 ∨ (zeroSet F).card=2 := by
  classical
  have eq : zeroSet F=solutions (-1:F) := by
    ext a
    simp [zeroSet,solutions,eq_neg_iff_add_eq_zero]
  rw [eq]
  by_cases h : ∃y : F, y^2= -1
  · obtain ⟨y,hy⟩ := h
    exact Or.inr (sols_nonzero two (neg_ne_zero.mpr one_ne_zero) y hy)
  · left
    apply Finset.card_eq_zero.mpr
    simpa [solutions,Finset.filter_eq_empty_iff] using h

theorem dark_count (two : (2:F)≠0) :
    2*(dark F).card+(zeroSet F).card=Fintype.card F+1 := by
  classical
  have fiber (a : F) : (solutions (a^2+1)).card +
      2*(if a∈dark F then 1 else 0) + (if a∈zeroSet F then 1 else 0) = 2 := by
    by_cases z : a^2+1=0
    · have notdark : a∉dark F := by simp only [dark,mem_filter,mem_univ,true_and,not_not]; exact ⟨0,by simp [z]⟩
      have sing : (univ.filter (fun x : F=>x=0)) = {0} := by ext x; simp
      simp [solutions,z,notdark,zeroSet,sing]
    by_cases sq : ∃y:F,y^2=a^2+1
    · obtain ⟨y,hy⟩ := sq
      have n : a∉dark F := by simp only [dark,mem_filter,mem_univ,true_and,not_not]; exact ⟨y,hy⟩
      simp [sols_nonzero two z y hy,n,zeroSet,z]
    · have card : (solutions (a^2+1)).card=0 := by
        apply card_eq_zero.mpr
        simpa [solutions,Finset.filter_eq_empty_iff] using sq
      simp [card,dark,sq,zeroSet,z]
  have h := Finset.sum_congr (s₁:=univ) rfl (fun a _=> fiber a)
  simp only [sum_add_distrib,← Finset.mul_sum,Finset.sum_boole,filter_mem_eq_inter,univ_inter,
    sum_const,card_univ,smul_eq_mul,sum_solutions two,Nat.cast_id] at h
  have pos : 0<Fintype.card F := Fintype.card_pos
  omega
end Deldor14.Star.OddWindow

namespace Deldor14.Star.OddWindow
open SimpleGraph Finset
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

def center : Point F := .aff 0 (2⁻¹)
def row (a : F) : Point F := .aff a (-(2⁻¹))

def removed (S : Finset F) : Finset (Point F) := insert center (S.image row)

theorem row_inj : Function.Injective (row (F:=F)) := by
  intro a b e
  exact (Point.aff.inj e).1

theorem center_ne (two : (2:F) ≠ 0) (a : F) : center ≠ row a := by
  intro e
  have h := (Point.aff.inj e).2
  change (2:F)⁻¹ = -2⁻¹ at h
  field_simp at h
  exact two (by linear_combination h)

theorem card_removed (two : (2:F) ≠ 0) (S : Finset F) : (removed S).card = S.card+1 := by
  have ex : center ∉ S.image row := by
    rintro h
    obtain ⟨a,_,eq⟩ := mem_image.mp h
    exact center_ne two a eq.symm
  simp [removed,ex,card_image_of_injective _ row_inj]

def through (v : Point F) : Option F → Point F :=
  match v with
  | .pole => fun | none => .pole | some a => .inf a
  | .inf a => fun | none => .pole | some b => .aff a b
  | .aff a b => fun | none => .inf a | some x => .aff x (a*x-b)

theorem through_inj (v : Point F) : Function.Injective (through v) := by
  cases v <;> rintro (_|a) (_|b) h <;> simp_all [through]

theorem through_inc (v : Point F) (i : Option F) :
    Point.inc v (through v i) ∨ (v=.pole ∧ through v i=.pole) := by
  cases v <;> cases i <;> simp [through,Point.inc]

theorem inc_center_row (a : F) : Point.inc center (row a) := by simp [center,row,Point.inc]

theorem inc_pair (two : (2:F)≠0) {a : F} (ha : a≠0) :
    Point.inc (row a) (row (-a⁻¹)) := by
  simp [row,Point.inc,ha]
  field_simp
  ring

theorem blocked_neighbor (two : (2:F)≠0) (S : Finset F)
    (nozero : 0∉S) (pairs : ∀ a∈S,-a⁻¹∈S) (v : Point F) (hv : v∉removed S)
    {u w : Point F} (hu : u∈removed S) (hw : w∈removed S)
    (iu : Point.inc v u) (iw : Point.inc v w) : u=w := by
  have nc (a : F) := center_ne two a
  have diff (a : F) (ha : a∈S) : a≠0 := fun h => nozero (h ▸ ha)
  have cx (a : F) (ha : a∈S) (hx : Point.inc v center) (hy : Point.inc v (row a)) : False := by
    have e := Point.common_unique (nc a) (Point.inc_symm hx) (Point.inc_symm hy)
      (inc_center_row (-a⁻¹)) (inc_pair two (diff a ha))
    exact hv (e ▸ mem_insert_of_mem (mem_image_of_mem row (pairs a ha)))
  rcases mem_insert.mp hu with h|h <;> rcases mem_insert.mp hw with k|k
  · exact h.trans k.symm
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp k
    exact (cx a ha (h ▸ iu) iw).elim
  · obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact (cx a ha (k ▸ iw) iu).elim
  · obtain ⟨a,_,rfl⟩ := mem_image.mp h
    obtain ⟨b,_,rfl⟩ := mem_image.mp k
    by_contra neq
    have e := Point.common_unique neq (Point.inc_symm iu) (Point.inc_symm iw)
      (Point.inc_symm (inc_center_row a)) (Point.inc_symm (inc_center_row b))
    exact hv (e ▸ mem_insert_self ..)

theorem absolute_safe (two : (2:F)≠0) (S : Finset F)
    (roots : ∀ a : F, a^2+1=0 → a∈S)
    (safe : ∀ a∈S, (∃ x : F, x^2=a^2+1) → a^2+1=0)
    (v : Point F) (hv : v∉removed S) (self : Point.inc v v ∨ v=.pole)
    {u : Point F} (hu : u∈removed S) (h : Point.inc v u) : False := by
  cases v with
  | pole =>
    rcases mem_insert.mp hu with e|e
    · subst u; exact h
    · obtain ⟨a,_,rfl⟩ := mem_image.mp e; exact h
  | inf x => simp [Point.inc] at self
  | aff x y =>
    have abs : y+y=x*x := by simpa [Point.inc] using self
    rcases mem_insert.mp hu with e|e
    · subst u
      change y+2⁻¹=x*0 at h
      have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
      have z : x^2+1=0 := by linear_combination -abs+2*h-h2
      apply hv
      have yy : y= -(2:F)⁻¹ := by linear_combination h
      rw [yy]
      exact mem_insert_of_mem (mem_image_of_mem row (roots x z))
    · obtain ⟨a,ha,rfl⟩ := mem_image.mp e
      change y+ -(2:F)⁻¹=x*a at h
      have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
      have e : (x-a)^2=a^2+1 := by linear_combination -abs+2*h+h2
      have z := safe a ha ⟨_,e⟩
      have eq : x=a := sub_eq_zero.mp (sq_eq_zero_iff.mp (e.trans z))
      subst x
      have yy : y= -(2:F)⁻¹ := by linear_combination h+z+h2
      apply hv; rw [yy]
      exact mem_insert_of_mem (mem_image_of_mem row ha)

abbrev Vertex (S : Finset F) := {v : Point F // v∉removed S}

def host (S : Finset F) : SimpleGraph (Vertex S) := Point.graph.comap Subtype.val

theorem no_square (S : Finset F) : ¬(cycleGraph 4).IsContained (host S) := by
  have sub : (host S).IsContained Point.graph :=
    ⟨⟨⟨Subtype.val,fun h=>h⟩,Subtype.val_injective⟩⟩
  exact fun bad=>Point.no_square (bad.trans sub)

theorem minimum (two : (2:F)≠0) (S : Finset F)
    (nozero : 0∉S) (pairs : ∀ a∈S,-a⁻¹∈S)
    (roots : ∀ a : F, a^2+1=0 → a∈S)
    (safe : ∀ a∈S, (∃ x : F, x^2=a^2+1) → a^2+1=0)
    [DecidableRel (host S).Adj] (v : Vertex S) : Fintype.card F ≤ (host S).degree v := by
  classical
  have pole_ok : Point.pole ∉ removed S := by
    simp [removed,center,row]
  let bad (i : Option F) := through v.val i=v.val ∨ through v.val i ∈ removed S
  have abs (i) (e : through v.val i=v.val) : Point.inc v.val v.val ∨ v.val=.pole := by
    rcases through_inc v.val i with h|⟨h,_⟩
    · exact Or.inl (by simpa only [e] using h)
    · exact Or.inr h
  have hits (i) (h : through v.val i ∈ removed S) : Point.inc v.val (through v.val i) := by
    rcases through_inc v.val i with out|⟨_,e⟩
    · exact out
    · exact (pole_ok (e ▸ h)).elim
  have small : (univ.filter bad).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    apply through_inj v.val
    rcases (mem_filter.mp hi).2 with a|a <;> rcases (mem_filter.mp hj).2 with b|b
    · exact a.trans b.symm
    · exact (absolute_safe two S roots safe v.val v.property (abs i a) b (hits j b)).elim
    · exact (absolute_safe two S roots safe v.val v.property (abs j b) a (hits i a)).elim
    · exact blocked_neighbor two S nozero pairs v.val v.property a b (hits i a) (hits j b)
  let A := univ.filter (fun i => ¬bad i)
  have many : Fintype.card F ≤ A.card := by
    have h := card_filter_add_card_filter_not (s:=univ) bad
    rw [card_univ,Fintype.card_option] at h
    change _ ≤ (univ.filter (fun i=>¬bad i)).card
    omega
  have clean (i : A) : through v.val i.val ≠ v.val ∧ through v.val i.val ∉ removed S :=
    not_or.mp (mem_filter.mp i.property).2
  let target (i : A) : Vertex S := ⟨through v.val i.val,(clean i).2⟩
  have adj (i : A) : (host S).Adj v (target i) := by
    refine ⟨(clean i).1.symm,?_⟩
    rcases through_inc v.val i.val with h|⟨e,f⟩
    · exact h
    · exact ((clean i).1 (f.trans e.symm)).elim
  let f (i : A) : ↥((host S).neighborFinset v) := ⟨target i,(mem_neighborFinset ..).mpr (adj i)⟩
  have inj : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact through_inj v.val (congrArg (fun x : ↥((host S).neighborFinset v) => x.val.val) h)
  simpa only [Fintype.card_coe,card_neighborFinset_eq_degree] using
    (many.trans (by simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f inj) :
        Fintype.card F ≤ ((host S).neighborFinset v).card)

theorem cardinality (two : (2:F)≠0) (S : Finset F) :
    Fintype.card (Vertex S) + S.card = (Fintype.card F)^2 + Fintype.card F := by
  classical
  have h := Finset.card_le_univ (removed S)
  rw [card_removed two,Point.card_points] at h
  change Fintype.card {v : Point F // v∉removed S} + _ = _
  rw [Fintype.card_subtype_compl, Fintype.card_coe, card_removed two, Point.card_points]
  omega

end Deldor14.Star.OddWindow

/- Even steps of the quadratic-star Ramsey interval in odd characteristic.
Parsons (1976); Zhang, Chen and Cheng (2017), DOI 10.1016/j.disc.2016.12.005. -/
namespace Deldor14.Star.OddWindow
open Finset SimpleGraph
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem dark_iff (a : F) : a∈dark F ↔ ¬∃x : F,x^2=a^2+1 := by
  classical
  simp [dark]
theorem zero_iff (a : F) : a∈zeroSet F ↔ a^2+1=0 := by simp [zeroSet]
theorem nz_dark {a : F} (ha : a∈dark F) : a≠0 := by
  rintro rfl
  exact (dark_iff _).mp ha ⟨1,by simp⟩
theorem flip_eq {a : F} (h : a^2+1=0) : -a⁻¹=a := by
  have nz : a≠0 := by rintro rfl; simp at h
  field_simp
  linear_combination -h
private theorem flip_dark (a : F) (ha : a∈dark F) : -a⁻¹∈dark F := by
  apply (dark_iff _).mpr
  rintro ⟨x,hx⟩
  apply (dark_iff _).mp ha
  refine ⟨x*a,?_⟩
  have nz := nz_dark ha
  field_simp at hx
  linear_combination hx

theorem choose_rows (two : (2:F)≠0) {t : ℕ} (ht : Even t) (pos : 2 ≤ t)
    (le : t≤2*((Fintype.card F+3)/4)) :
    ∃ S : Finset F, S.card=t ∧ 0∉S ∧ (∀ a∈S,-a⁻¹∈S) ∧
      (∀ a : F,a^2+1=0 → a∈S) ∧ (∀ a∈S,(∃ x : F,x^2=a^2+1) → a^2+1=0) := by
  classical
  let f (a : F) := -a⁻¹
  have sq : Function.Involutive f := by intro a; simp [f]
  have free (a : F) (ha : a∈dark F) : f a≠a := by
    intro e
    have nz := nz_dark ha
    change -a⁻¹=a at e
    field_simp at e
    exact (dark_iff _).mp ha ⟨0,by linear_combination e⟩
  obtain ⟨k,hk,sub⟩ := choose_pairs f sq (dark F) flip_dark free
  obtain ⟨u,hu⟩ := ht
  have ze := zero_count two
  have dc := dark_count two
  have size : (zeroSet F).card ≤ t ∧ t≤2*k+(zeroSet F).card := by omega
  obtain ⟨T,hT,cT,sT⟩ := sub ((t-(zeroSet F).card)/2) (by omega)
  have dis : Disjoint (zeroSet F) T := by
    apply Finset.disjoint_left.mpr
    intro a hz h
    exact (dark_iff _).mp (hT h) ⟨0,by simp [(zero_iff _).mp hz]⟩
  refine ⟨zeroSet F ∪ T,?_,?_,?_,?_,?_⟩
  · rw [card_union_of_disjoint dis,cT]; omega
  · intro h
    rcases mem_union.mp h with z|h
    · simpa using (zero_iff _).mp z
    · exact nz_dark (hT h) rfl
  · intro a ha
    rcases mem_union.mp ha with z|t'
    · rw [flip_eq ((zero_iff _).mp z)]
      exact mem_union_left _ z
    · exact mem_union_right _ (sT a t')
  · intro a z; exact mem_union_left _ ((zero_iff _).mpr z)
  · intro a ha ex
    rcases mem_union.mp ha with z|t'
    · exact (zero_iff _).mp z
    · exact ((dark_iff _).mp (hT t') ex).elim

theorem field_even_step (two : (2:F)≠0) {t n : ℕ} (ht : Even t) (pos : 2 ≤ t)
    (le : t≤2*((Fintype.card F+3)/4)) (hn : n+t=Fintype.card F^2) :
    number n = n + Fintype.card F + 1 := by
  classical
  obtain ⟨S,sc,nz,fl,roots,safe⟩ := choose_rows two ht pos le
  let q := Fintype.card F
  have qtwo : 2≤q := Fintype.one_lt_card
  have count := cardinality two S
  rw [sc] at count
  have card : Fintype.card (Vertex S)=n+q := by dsimp [q]; omega
  let G := host S
  have red := no_square S
  have npos : 0<n := by
    have p2 : q≤q^2 := Nat.le_self_pow (by decide : 2≠0) q
    change t≤2*((q+3)/4) at le
    change n+t=q^2 at hn
    by_contra! e
    have qsq : q+1 ≤ q^2 := by nlinarith [show 0≤(q-2)^2 by positivity]
    omega
  have blue : ∀ v,Gᶜ.degree v < n := by
    intro v
    have low := minimum two S nz fl roots safe v
    rw [degree_compl,card]
    change q≤G.degree v at low
    omega
  have lower := lower_from_host G red blue
  rw [card] at lower
  exact Nat.le_antisymm (parsons_upper qtwo (by omega)) lower

theorem prime_power_even_step {p m t n : ℕ} (hp : p.Prime) (odd : p≠2) (hm : m≠0)
    (ht : Even t) (pos : 2≤t) (le : t≤2*((p^m+3)/4)) (hn : n+t=(p^m)^2) :
    number n=n+p^m+1 := by
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  letI : Fintype F := Fintype.ofFinite _
  classical
  have two : (2:F)≠0 := by
    intro h
    have d : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using h)
    exact odd (Nat.le_antisymm (Nat.le_of_dvd (by decide) d) hp.two_le)
  have hq : Fintype.card F=p^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card p m hm]
  simpa only [hq] using field_even_step two ht pos (by simpa only [hq] using le)
    (n:=n) (by simpa only [hq] using hn)
end Deldor14.Star.OddWindow

/- Add one edge and delete the matching between its two old neighbourhoods. -/
namespace Deldor14.Star.OddWindow
open SimpleGraph Finset
variable {V : Type*}

def special (a b v w : V) := v=a ∧ w=b ∨ v=b ∧ w=a
def cross (G : SimpleGraph V) (a b v w : V) := G.Adj a v ∧ G.Adj b w ∨ G.Adj b v ∧ G.Adj a w

def switch (G : SimpleGraph V) (a b : V) (ab : a≠b) : SimpleGraph V where
  Adj v w := special a b v w ∨ G.Adj v w ∧ ¬cross G a b v w
  symm := ⟨by intro x y; simp only [special,cross]; grind [SimpleGraph.adj_symm]⟩
  loopless := ⟨by intro v; simp [special]; grind⟩

theorem switch_nosquare (G : SimpleGraph V) (a b : V) (ab : a≠b)
    (uniq : ∀ {x y u w},x≠y → G.Adj x u → G.Adj y u → G.Adj x w → G.Adj y w → u=w) :
    ¬(cycleGraph 4).IsContained (switch G a b ab) := by
  rintro ⟨f⟩
  let H := switch G a b ab
  have impossible {v w x y : V} (vx : v≠x) (wy : w≠y) (vw : v≠w) (xy : x≠y)
      (wx : w≠x) (yv : y≠v) (s : special a b v w)
      (h1 : H.Adj w x) (h2 : H.Adj x y) (h3 : H.Adj y v) : False := by
    change special a b _ _ ∨ _ ∧ ¬cross G a b _ _ at h1 h2 h3
    have pw := h1.resolve_left (by unfold special at *; grind)
    have px := h2.resolve_left (by unfold special at *; grind)
    have py := h3.resolve_left (by unfold special at *; grind)
    rcases s with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact px.2 (Or.inr ⟨pw.1,py.1.symm⟩)
    · exact px.2 (Or.inl ⟨pw.1,py.1.symm⟩)
  have go {v w x y : V} (distinct : [v,w,x,y].Nodup)
      (h0 : H.Adj v w) (h1 : H.Adj w x) (h2 : H.Adj x y) (h3 : H.Adj y v) : False := by
    simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true,not_or] at distinct
    by_cases s0 : special a b v w
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s0 h1 h2 h3
    by_cases s1 : special a b w x
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s1 h2 h3 h0
    by_cases s2 : special a b x y
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s2 h3 h0 h1
    by_cases s3 : special a b y v
    · exact impossible (by grind) (by grind) (by grind) (by grind) (by grind) (by grind) s3 h0 h1 h2
    change special a b _ _ ∨ _ ∧ _ at h0 h1 h2 h3
    exact (by grind : w≠y) (uniq (by grind : v≠x) (h0.resolve_left s0).1
      (h1.resolve_left s1).1.symm (h3.resolve_left s3).1.symm (h2.resolve_left s2).1)
  apply go (v:=f 0) (w:=f 1) (x:=f 2) (y:=f 3)
  · exact List.Nodup.map f.injective (by decide : ([0,1,2,3] : List (Fin 4)).Nodup)
  all_goals apply f.toHom.map_adj; decide

theorem switch_old [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (ab : a≠b) [DecidableRel (switch G a b ab).Adj] (v : V)
    (uncut : ∀ w,G.Adj v w → ¬cross G a b v w) :
    G.degree v≤(switch G a b ab).degree v := by
  apply card_le_card
  intro w hw
  have e := (mem_neighborFinset ..).mp hw
  exact (mem_neighborFinset ..).mpr (Or.inr ⟨e,uncut w e⟩)

theorem switch_loss [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (ab : a≠b) [DecidableRel (switch G a b ab).Adj]
    (separate : ∀ v,G.Adj a v → ¬G.Adj b v)
    (uniq : ∀ {x y u w},x≠y → G.Adj x u → G.Adj y u → G.Adj x w → G.Adj y w → u=w)
    (nedge : ¬G.Adj a b) (v : V) : G.degree v≤(switch G a b ab).degree v+1 := by
  classical
  let A := G.neighborFinset v
  let B := (switch G a b ab).neighborFinset v
  have lost (w : V) (hw : w∈A \ B) : G.Adj v w ∧ cross G a b v w := by
    obtain ⟨e,ne⟩ := mem_sdiff.mp hw
    have ed := (mem_neighborFinset ..).mp e
    exact ⟨ed,by by_contra h; exact ne ((mem_neighborFinset ..).mpr (Or.inr ⟨ed,h⟩))⟩
  have small : (A \ B).card≤1 := by
    apply card_le_one.mpr
    intro x hx y hy
    obtain ⟨vx,dx⟩ := lost x hx
    obtain ⟨vy,dy⟩ := lost y hy
    rcases dx with ⟨av,bx⟩|⟨bv,ax⟩ <;> rcases dy with ⟨_,by'⟩|⟨_,ay⟩
    · exact uniq (x:=v) (y:=b) (fun e=>nedge (by simpa only [e] using av)) vx bx vy by'
    · exact (separate _ av ‹G.Adj b v›).elim
    · exact (separate _ ‹G.Adj a v› bv).elim
    · exact uniq (x:=v) (y:=a) (fun e=>nedge (by simpa only [e] using bv.symm)) vx ax vy ay
  have bound := card_le_card_sdiff_add_card (s:=A) (t:=B)
  change A.card≤B.card+1
  omega
theorem switch_gain [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : V) (ab : a≠b) [DecidableRel (switch G a b ab).Adj] (noab : ¬G.Adj a b) :
    G.degree a+1≤(switch G a b ab).degree a := by
  have lower : insert b (G.neighborFinset a) ⊆ (switch G a b ab).neighborFinset a := by
    intro w hw
    apply (mem_neighborFinset ..).mpr
    rcases mem_insert.mp hw with rfl|h
    · exact Or.inl (Or.inl ⟨rfl,rfl⟩)
    · exact Or.inr ⟨(mem_neighborFinset ..).mp h, by
        unfold cross; simp [show ¬G.Adj b a from fun e=>noab e.symm]⟩
  simpa [card_insert_of_notMem,mem_neighborFinset,noab] using card_le_card lower

end Deldor14.Star.OddWindow

/- Neighbours near the polar line retained in the odd-step construction. -/
namespace Deldor14.Star.OddWindow
open SimpleGraph Finset
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

theorem row_neighbor (two : (2:F)≠0) {a b : F} (az : a≠0)
    (h : Point.inc (row a) (row b)) : b= -a⁻¹ := by
  change -2⁻¹+ -2⁻¹=a*b at h
  field_simp
  have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
  linear_combination -h-h2

theorem absolute_row (two : (2:F)≠0) {a : F}
    (safe : (∃x:F,x^2=a^2+1) → a^2+1=0) (v : Point F)
    (absv : Point.inc v v ∨ v=.pole) (near : Point.inc v (row a)) : v=row a := by
  cases v with
  | pole => exact False.elim near
  | inf t => simp [Point.inc] at absv
  | aff x y =>
    have abs : y+y=x*x := by simpa [Point.inc] using absv
    change y+ -(2:F)⁻¹=x*a at near
    have h2 : (2:F)*2⁻¹=1 := mul_inv_cancel₀ two
    have e : (x-a)^2=a^2+1 := by linear_combination -abs+2*near+h2
    have z := safe ⟨_,e⟩
    have eq : x=a := sub_eq_zero.mp (sq_eq_zero_iff.mp (e.trans z))
    subst x
    have yy : y= -(2:F)⁻¹ := by linear_combination near+z+h2
    rw [yy]; rfl

theorem retained_row (two : (2:F)≠0) {S : Finset F} {a : F} (ha : a∉S) :
    row a∉removed S := by
  intro h
  rcases mem_insert.mp h with e|e
  · exact center_ne two a e.symm
  · obtain ⟨b,hb,eq⟩ := mem_image.mp e
    exact ha (row_inj eq ▸ hb)

theorem through_degree (S : Finset F) [DecidableRel (host S).Adj] (v : Vertex S)
    (A : Finset (Option F)) (good : ∀ i∈A, through v.val i≠v.val ∧ through v.val i∉removed S) :
    A.card≤(host S).degree v := by
  let vertex (i : A) : Vertex S := ⟨through v.val i.val,(good i i.property).2⟩
  have adj (i : A) : (host S).Adj v (vertex i) := by
    refine ⟨(good i i.property).1.symm,?_⟩
    rcases through_inc v.val i.val with h|⟨e,f⟩
    · exact h
    · exact ((good i i.property).1 (f.trans e.symm)).elim
  let f (i : A) : ↥((host S).neighborFinset v) := ⟨vertex i,(mem_neighborFinset ..).mpr (adj i)⟩
  have inj : Function.Injective f := by
    intro i j h
    apply Subtype.ext
    exact through_inj v.val (congrArg (fun x : ↥((host S).neighborFinset v) => x.val.val) h)
  simpa only [Fintype.card_coe,card_neighborFinset_eq_degree] using Fintype.card_le_of_injective f inj

theorem new_degree (two : (2:F)≠0) (S : Finset F) [DecidableRel (host S).Adj]
    (a : F) (az : a≠0) (ha : row a∉removed S) :
    Fintype.card F ≤ (host S).degree ⟨row a,ha⟩+1 := by
  classical
  let A : Finset (Option F) := (univ.erase (some 0)).erase (some (-a⁻¹))
  have good (i) (hi : i∈A) : through (row a) i≠row a ∧ through (row a) i∉removed S := by
    have no := mem_erase.mp hi
    have ne0 := (mem_erase.mp no.2).1
    cases i with
    | none => simp [through,row,removed,center]
    | some x =>
      have dif : x≠ -a⁻¹ := by simpa using no.1
      have nz : x≠0 := by simpa using ne0
      have eq : ∀ b:F, through (row a) (some x) ≠ row b := by
        intro b e
        have i := through_inc (row a) (some x)
        have ii : Point.inc (row a) (row b) := by
          rw [e] at i
          exact i.resolve_right (by simp [row])
        have xeq : x=b := (Point.aff.inj e).1
        exact dif (xeq.trans (row_neighbor two az ii))
      refine ⟨eq _,?_⟩
      intro e
      rcases mem_insert.mp e with cen|im
      · exact nz (Point.aff.inj cen).1
      · obtain ⟨b,_,ex⟩ := mem_image.mp im
        exact eq b ex.symm
  have deg := through_degree S (⟨row a,ha⟩) A good
  have card : A.card+2=Fintype.card F+1 := by
    have eq1 := card_erase_add_one (mem_univ (some (0:F)))
    have e : some (-a⁻¹)∈(univ.erase (some (0:F))) := by simp [az]
    have eq2 := card_erase_add_one e
    rw [card_univ,Fintype.card_option] at eq1
    dsimp [A]
    omega
  omega

theorem surplus (two : (2:F)≠0) (S : Finset F) [DecidableRel (host S).Adj]
    {a b : F} (safe : (∃x:F,x^2=a^2+1) → a^2+1=0) (ha : row a∉removed S)
    (nedge : ¬Point.graph.Adj (row a) (row b)) (v w : Vertex S)
    (va : Point.graph.Adj (row a) v.val) (wb : Point.graph.Adj (row b) w.val)
    (vw : Point.graph.Adj v.val w.val) : Fintype.card F+1≤(host S).degree v := by
  classical
  have vnc : v.val ≠center := fun e => v.property (e ▸ mem_insert_self ..)
  have wnc : w.val ≠center := fun e => w.property (e ▸ mem_insert_self ..)
  have vnb : v.val≠row b := fun e => nedge (by simpa only [e] using va)
  have noC : ¬Point.inc v.val center := by
    intro e
    exact wnc (Point.common_unique vnb vw.2 wb.2 e (Point.inc_symm (inc_center_row b)))
  have clean (p : Point F) (h : Point.inc v.val p) : p∉removed S := by
    intro hp
    rcases mem_insert.mp hp with rfl|im
    · exact noC h
    · obtain ⟨c,hc,rfl⟩ := mem_image.mp im
      have d : row a≠row c := by intro z; exact ha (z ▸ mem_insert_of_mem (mem_image_of_mem row hc))
      exact vnc (Point.common_unique d va.2 (Point.inc_symm h)
        (Point.inc_symm (inc_center_row a)) (Point.inc_symm (inc_center_row c)))
  have good (i : Option F) (hi : i∈univ) :
      through v.val i≠v.val ∧ through v.val i∉removed S := by
    rcases through_inc v.val i with h|⟨vp,_⟩
    · refine ⟨fun e=>?_,clean _ h⟩
      have abs : Point.inc v.val v.val := by simpa only [e] using h
      exact va.1 (absolute_row two safe _ (Or.inl abs) (Point.inc_symm va.2)).symm
    · exact (va.1 (absolute_row two safe _ (Or.inr vp) (Point.inc_symm va.2)).symm).elim
  simpa only [card_univ,Fintype.card_option] using through_degree S v univ good

theorem min_old (S T : Finset F) (sub : S⊆T)
    [DecidableRel (host S).Adj] [DecidableRel (host T).Adj]
    {v : Vertex S} (old : v.val∉removed T) :
    (host T).degree ⟨v.val,old⟩ ≤ (host S).degree v := by
  let v' : Vertex T := ⟨v.val,old⟩
  have incl : removed S⊆removed T := insert_subset_insert _ (image_subset_image sub)
  let inc (x : Vertex T) : Vertex S := ⟨x.val,fun e=>x.property (incl e)⟩
  let f (x : (host T).neighborSet v') : (host S).neighborSet v := ⟨inc x.val,x.property⟩
  have inj : Function.Injective f := fun _ _ e=>Subtype.ext (Subtype.ext (congrArg (fun x : (host S).neighborSet v=>x.val.val) e))
  simpa only [card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj
end Deldor14.Star.OddWindow

/- Complete odd-order interval of Zhang, Chen, and Cheng (2017). The odd steps
use a single edge switch between two surviving points of the polar line. -/
namespace Deldor14.Star.OddWindow
open Finset SimpleGraph
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem extra_dark (two : (2:F)≠0) (T : Finset F) (roots : ∀a:F,a^2+1=0 → a∈T)
    (small : T.card < 2*((Fintype.card F+3)/4)) :
    ∃ b∈dark F,b∉T := by
  classical
  by_contra! h
  have sub : dark F ∪ zeroSet F ⊆ T := by
    intro v hv
    exact (mem_union.mp hv).elim (h v) (fun e =>roots v ((zero_iff v).mp e))
  have d : Disjoint (dark F) (zeroSet F) := by
    apply Finset.disjoint_left.mpr
    intro a ha hz
    exact (dark_iff _).mp ha ⟨0,by simp [(zero_iff _).mp hz]⟩
  have bound := card_le_card sub
  rw [card_union_of_disjoint d] at bound
  have z := zero_count two
  have count := dark_count two
  have flip_stable (a : F) (ha : a∈dark F) : -a⁻¹∈dark F := by
    apply (dark_iff _).mpr
    rintro ⟨x,hx⟩
    apply (dark_iff _).mp ha
    have nz := nz_dark ha
    field_simp at hx
    exact ⟨x*a,by linear_combination hx⟩
  have flip_free (a : F) (ha : a∈dark F) : -a⁻¹≠a := by
    intro e
    have nz := nz_dark ha
    field_simp at e
    exact (dark_iff _).mp ha ⟨0,by linear_combination e⟩
  obtain ⟨k,dup,_⟩ := choose_pairs (fun a:F=> -a⁻¹) (by intro a; simp) (dark F) flip_stable flip_free
  omega

private theorem odd_host (two : (2:F)≠0) {t : ℕ} (ht : Odd t)
    (room : t+1 < 2*((Fintype.card F+3)/4)) :
    ∃ (S : Finset F) (H : SimpleGraph (Vertex S)) (_ : DecidableRel H.Adj),
      S.card=t ∧ ¬(cycleGraph 4).IsContained H ∧ ∀v,Fintype.card F≤H.degree v := by
  classical
  obtain ⟨k,hk⟩ := ht
  have pe : Even (t+1) := ⟨k+1,by omega⟩
  obtain ⟨T,tc,nz,pairs,roots,safe⟩ := choose_rows two pe (by omega) room.le
  obtain ⟨b,bd,bT⟩ := extra_dark two T roots (by omega)
  obtain ⟨a,aT⟩ := card_pos.mp (show 0<T.card by omega)
  let S := T.erase a
  have sc : S.card=t := by have h := card_erase_add_one aT; dsimp [S]; omega
  have a0 : a≠0 := fun e=>nz (e ▸ aT)
  have aS : a∉S := by simp [S]
  have bS : b∉S := fun e=>bT (mem_of_mem_erase e)
  let A : Vertex S := ⟨row a,retained_row two aS⟩
  let B : Vertex S := ⟨row b,retained_row two bS⟩
  have diff : A≠B := fun e => bT (row_inj (congrArg Subtype.val e) ▸ aT)
  have nepoint : ¬Point.graph.Adj (row a) (row b) := by
    intro e
    exact bT ((row_neighbor two a0 e.2) ▸ pairs a aT)
  let G := host S
  have nedge : ¬G.Adj A B := nepoint
  have uniq {v w x y : Vertex S} (vw : v≠w) (vx : G.Adj v x) (wx : G.Adj w x)
      (vy : G.Adj v y) (wy : G.Adj w y) : x=y := by
    apply Subtype.ext
    exact Point.common_unique (fun e=>vw (Subtype.ext e)) vx.2 wx.2 vy.2 wy.2
  have sep (v : Vertex S) (av : G.Adj A v) (bv : G.Adj B v) : False := by
    have e := Point.common_unique (show row a≠row b from fun e=>diff (Subtype.ext e))
      av.2 bv.2 (Point.inc_symm (inc_center_row a)) (Point.inc_symm (inc_center_row b))
    exact v.property (e ▸ mem_insert_self ..)
  let H := switch G A B diff
  refine ⟨S,H,inferInstance,sc,switch_nosquare G A B diff (fun e=>uniq e),?_⟩
  intro v
  by_cases va : v=A
  · subst v
    have d := new_degree two S a a0 A.property
    have g := switch_gain G A B diff nedge
    exact d.trans g
  have old : v.val∉removed T := by
    intro h
    rcases mem_insert.mp h with e|im
    · exact v.property (e ▸ mem_insert_self ..)
    · obtain ⟨c,hc,e⟩ := mem_image.mp im
      by_cases eq : c=a
      · exact va (Subtype.ext (by simpa only [eq] using e.symm))
      · exact v.property (e ▸ mem_insert_of_mem (mem_image_of_mem row (mem_erase.mpr ⟨eq,hc⟩)))
  by_cases unc : ∀ w,G.Adj v w → ¬cross G A B v w
  · have d0 := minimum two T nz pairs roots safe (⟨v.val,old⟩)
    exact (d0.trans (min_old S T (erase_subset ..) old)).trans (switch_old G A B diff v unc)
  push Not at unc
  obtain ⟨w,vw,cut⟩ := unc
  have plus : Fintype.card F+1 ≤ G.degree v := by
    rcases cut with ⟨av,bw⟩|⟨bv,aw⟩
    · exact surplus two S (safe a aT) A.property nepoint v w av bw vw
    · exact surplus two S (fun ex=>((dark_iff _).mp bd ex).elim) B.property
        (fun h=>nepoint h.symm) v w bv aw vw
  have enough := switch_loss G A B diff sep (fun e=>uniq e) nedge v
  change Fintype.card F≤(switch G A B diff).degree v
  omega

theorem field_odd_step (two : (2:F)≠0) {t n : ℕ} (ht : Odd t)
    (room : t+1<2*((Fintype.card F+3)/4)) (hn : n+t=Fintype.card F^2) :
    number n=n+Fintype.card F+1 := by
  classical
  obtain ⟨S,H,inst,sc,red,min⟩ := odd_host two ht room
  have count := cardinality two S
  rw [sc] at count
  have qtwo := Fintype.one_lt_card (α:=F)
  have card : Fintype.card (Vertex S)=n+Fintype.card F := by omega
  have npos : 0<n := by
    have qsq : Fintype.card F+1 ≤ Fintype.card F^2 := by nlinarith only [qtwo]
    omega
  have blue : ∀ v,Hᶜ.degree v<n := by
    intro v
    have d := min v
    rw [degree_compl,card]; omega
  have low := lower_from_host H red blue
  rw [card] at low
  exact Nat.le_antisymm (parsons_upper qtwo (by omega)) low

theorem prime_power_interval {p m t n : ℕ} (hp : p.Prime) (op : p≠2) (hm : m≠0)
    (pos : 1≤t) (le : t≤2*((p^m+3)/4)) (except : t+1≠2*((p^m+3)/4)) (hn : n+t=(p^m)^2) :
    number n=n+p^m+1 := by
  rcases Nat.even_or_odd t with he|ho
  · have ⟨v,hv⟩ := he
    exact prime_power_even_step hp op hm he (by omega) le hn
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  letI : Fintype F := Fintype.ofFinite _
  classical
  have two : (2:F)≠0 := by
    intro e
    have div := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using e)
    exact op (Nat.le_antisymm (Nat.le_of_dvd (by decide) div) hp.two_le)
  have hq : Fintype.card F=p^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card p m hm]
  have room : t+1<2*((p^m+3)/4) := by obtain ⟨k,hk⟩ := ho; omega
  simpa only [hq] using field_odd_step two ho (by simpa only [hq] using room)
    (n:=n) (by simpa only [hq] using hn)
end Deldor14.Star.OddWindow

/- The following formalizes Zach Waddle’s 2026 preprint calculation for 39 leaves. Original mathematical argument and graph data: https://github.com/zach7036/c4-star-ramsey/tree/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33 . The original written proof is available under CC BY 4.0; the witness data and code under the MIT license, Copyright 2026 Zach Waddle. The verification and Bernstein certificates in Lean were written for Left to Solve. -/
/- The adjacent even steps at q(q−1), from Zhang, Chen, and Cheng,
Some values of Ramsey numbers for C₄ versus stars, Finite Fields Appl. 45 (2017).
Deleting the line at infinity leaves at most one fewer neighbour per point. -/
namespace Deldor14.Star.OddWindow
open Finset SimpleGraph OMA.ChenStar
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Affine (S : Finset F) := {p:F×F // Point.aff p.1 p.2∉removed S}
def embed (S : Finset F) (v : Affine S) : Vertex S := ⟨Point.aff v.val.1 v.val.2,v.property⟩
def affineGraph (S : Finset F) := (host S).comap (embed S)
private theorem injective_embed (S : Finset F) : Function.Injective (embed S) := by
  rintro ⟨⟨a,b⟩,h⟩ ⟨⟨c,d⟩,k⟩ e
  obtain ⟨rfl,rfl⟩ := Point.aff.inj (congrArg Subtype.val e)
  rfl
private theorem erase_line (S : Finset F) : Fintype.card (Vertex S)=Fintype.card (Affine S)+Fintype.card F+1 := by
  classical
  have ip (a : F) : Point.inf a∉removed S := by simp [removed,center,row]
  have pp : Point.pole∉removed S := by simp [removed,center,row]
  let e : Vertex S ≃ (Affine S ⊕ Option F) := {
    toFun := fun | ⟨.aff x y,h⟩ => .inl ⟨(x,y),h⟩ | ⟨.inf a,_⟩ => .inr (some a) | ⟨.pole,_⟩ => .inr none
    invFun := fun | .inl v => embed S v | .inr (some a) => ⟨.inf a,ip a⟩ | .inr none=>⟨.pole,pp⟩
    left_inv := by rintro ⟨v,h⟩; cases v <;> rfl
    right_inv := by rintro (⟨⟨x,y⟩,h⟩|_|a) <;> rfl }
  simpa [Nat.add_assoc] using Fintype.card_congr e

private theorem loses_one (S : Finset F) [DecidableRel (host S).Adj] [DecidableRel (affineGraph S).Adj]
    (v : Affine S) : (host S).degree (embed S v) ≤ (affineGraph S).degree v+1 := by
  let f : (host S).neighborSet (embed S v) → Option ((affineGraph S).neighborSet v) :=
    fun | ⟨⟨.aff x y,h⟩,e⟩ => some ⟨⟨(x,y),h⟩,e⟩ | _ => none
  have inj : Function.Injective f := by
    rintro ⟨⟨z,hz⟩,e⟩ ⟨⟨w,hw⟩,k⟩ h
    have ze := e.2
    have wk := k.2
    change Point.inc (Point.aff v.val.1 v.val.2) z at ze
    change Point.inc (Point.aff v.val.1 v.val.2) w at wk
    cases z <;> cases w <;> simp_all [f,Point.inc,Subtype.ext_iff]
  simpa only [Fintype.card_option,card_neighborSet_eq_degree] using Fintype.card_le_of_injective f inj

private theorem odd_regular_upper {q t n : ℕ} (qtwo : 2≤q) (qo : Odd q) (te : Even t)
    (pos : 0<t) (hn : n+q+t=q^2) : number n ≤ n+q := by
  classical
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra hs
  have min (v : Fin (n+q)) : q ≤ G.degree v := by
    have small : Gᶜ.degree v<n := lt_of_not_ge (fun large=>hs (star_isContained_of_le_degree Gᶜ large))
    rw [degree_compl,Fintype.card_fin] at small
    omega
  have product : (q+1)*(q-1)+1=q^2 := by
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
    simp only [Nat.succ_sub_one,Nat.succ_eq_add_one]
    ring
  have reg (v) : G.degree v=q := by
    apply le_antisymm _ (min v)
    by_contra! h
    have lb := Packing.local_bound G red q min v
    have ub := Finset.card_lt_univ_of_notMem (Packing.no_self G v)
    have x : (q+1)*(q-1) ≤ G.degree v*(q-1) := Nat.mul_le_mul_right _ h
    rw [Fintype.card_fin] at ub
    have endlt : (q+1)*(q-1)<n+q := (x.trans lb).trans_lt ub
    omega
  have ev := G.even_card_odd_degree_vertices
  simp only [reg,qo,filter_true,card_univ,Fintype.card_fin] at ev
  have oo := qo.pow (n:=2)
  obtain ⟨i,hi⟩ := ev
  obtain ⟨j,hj⟩ := te
  obtain ⟨k,hk⟩ := oo
  omega

theorem affine_field_even (two : (2:F)≠0) (odd : Odd (Fintype.card F))
    (five : 5≤Fintype.card F) {t n : ℕ} (et : Even t) (pos : 2≤t)
    (le : t≤2*((Fintype.card F+3)/4)) (hn : n+Fintype.card F+t=Fintype.card F^2) :
    number n=n+Fintype.card F := by
  classical
  obtain ⟨S,sc,nz,pairs,roots,safe⟩ := choose_rows two et pos le
  let q := Fintype.card F
  let G := affineGraph S
  have count := cardinality two S
  have ec := erase_line S
  rw [sc,ec] at count
  have cardinal : Fintype.card (Affine S)+1=n+q := by dsimp [q]; omega
  have red : ¬(cycleGraph 4).IsContained G := by
    have sub : G.IsContained (host S) := ⟨⟨⟨embed S,fun h=>h⟩,injective_embed S⟩⟩
    exact fun h => no_square S (h.trans sub)
  have npos : 0<n := by
    change n+q+t=q^2 at hn
    change 5≤q at five
    change t≤2*((q+3)/4) at le
    have qsq : 2*q+1≤q^2 := by nlinarith only [five]
    omega
  have blue : ∀v,Gᶜ.degree v<n := by
    intro v
    have lb := minimum two S nz pairs roots safe (embed S v)
    have l := loses_one S v
    change q≤(host S).degree (embed S v) at lb
    change (host S).degree (embed S v) ≤ G.degree v+1 at l
    rw [degree_compl]
    omega
  have low : Fintype.card (Affine S)<number n := lower_from_host G red blue
  change Fintype.card (Affine S)+1=n+Fintype.card F at cardinal
  apply le_antisymm (odd_regular_upper (by omega) odd et (by omega) hn)
  omega

theorem prime_power_affine {p m t n : ℕ} (hp : p.Prime) (op : p≠2) (hm : m≠0) (five : 5≤p^m)
    (et : Even t) (pos : 2≤t) (le : t≤2*((p^m+3)/4)) (hn : n+p^m+t=(p^m)^2) :
    number n=n+p^m := by
  letI : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p m
  letI : Fintype F := Fintype.ofFinite _
  classical
  have two : (2:F)≠0 := by
    intro e
    have d := (CharP.cast_eq_zero_iff F p 2).mp (by simpa using e)
    exact op (Nat.le_antisymm (Nat.le_of_dvd (by decide) d) hp.two_le)
  have card : Fintype.card F=p^m := by rw [← Nat.card_eq_fintype_card,GaloisField.card p m hm]
  have odd : Odd (p^m) := (hp.odd_of_ne_two op).pow
  simpa only [card] using affine_field_even two (by simpa only [card] using odd)
    (by simpa only [card] using five) et pos (by simpa only [card] using le)
    (n:=n) (by simpa only [card] using hn)
end Deldor14.Star.OddWindow

/- Deficiency matrices for near-extremal quadrilateral-free graphs.
These identities generalize the antipodal decomposition to regular deficiency >1. -/
namespace Deldor14.Star.Deficiency
open SimpleGraph Finset Matrix OMA.ChenStar Packing ExcessOne

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
def graph : SimpleGraph V where
  Adj i j := j∈missing G i
  symm := ⟨fun i j h => (mem_missing G).mpr ⟨((mem_missing G).mp h).1.symm,
    by simpa [common,inter_comm] using ((mem_missing G).mp h).2⟩⟩
  loopless := ⟨fun i h => ((mem_missing G).mp h).1 rfl⟩
instance : DecidableRel (graph G).Adj := fun i j => inferInstanceAs (Decidable (j∈missing G i))

theorem neighbors (i : V) : (graph G).neighborFinset i=missing G i := by
  ext
  exact mem_neighborFinset _ _ _

theorem regular_of_bounds {d : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (min : ∀ v, d≤G.degree v) (small : Fintype.card V ≤ (d+1)*(d-1)) : ∀ v,G.degree v=d := by
  intro v
  have sub : endpoints G v ⊆ univ.erase v := fun x hx =>
    mem_erase.mpr ⟨((mem_endpoints G).mp hx).1,mem_univ x⟩
  have ub := card_le_card sub
  rw [card_erase_of_mem (mem_univ v),card_univ] at ub
  have low := local_bound G red d min v
  have vz : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  by_contra bad
  have high : d+1≤G.degree v := by have := min v; omega
  have big := Nat.mul_le_mul_right (d-1) high
  omega

theorem degree {d e : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (size : Fintype.card V = d*(d-1)+1+e) (reg : ∀ v,G.degree v=d) (v : V) :
    (graph G).degree v=e := by
  rw [←card_neighborFinset_eq_degree,neighbors,missing,card_sdiff_of_subset (by
    intro x hx
    exact mem_erase.mpr ⟨((mem_endpoints G).mp hx).1,mem_univ _⟩)]
  rw [card_erase_of_mem (mem_univ v),card_univ,card_endpoints G red]
  simp [reg,size]

theorem adj_square {d : ℕ} (red : ¬(cycleGraph 4).IsContained G)
    (reg : ∀ v,G.degree v=d) :
    (G.adjMatrix ℝ)^2 = ((d:ℝ)-1) • (1:Matrix V V ℝ) + ones V ℝ - (graph G).adjMatrix ℝ := by
  classical
  ext i j
  rw [adj_square_entries G]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, ones, Matrix.of_apply, adjMatrix_apply]
  by_cases ij : i=j
  · subst j
    have nope := (graph G).irrefl (v:=i)
    simp [common,reg,nope]
  · rw [if_neg ij,mul_zero,zero_add]
    have few := codeg_le_one G red ij
    by_cases h : (graph G).Adj i j
    · rw [if_pos h,sub_self]
      have emp := ((mem_missing G).mp h).2
      simp [emp]
    · rw [if_neg h,sub_zero]
      have ne : common G i j ≠ ∅ := fun e => h ((mem_missing G).mpr ⟨Ne.symm ij,e⟩)
      have pos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ne)
      exact_mod_cast (show (common G i j).card=1 by omega)

theorem adj_trace : (G.adjMatrix ℝ).trace=0 := by simp [Matrix.trace,Matrix.diag,adjMatrix_apply]
end Deldor14.Star.Deficiency

/- Lower-bound examples of Zach Waddle. The edge lists were taken from
https://github.com/zach7036/c4-star-ramsey/tree/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33 .
The code below independently checks the symmetry, all codegrees, and each minimum degree.
The original edge lists are distributed under the MIT license (Copyright 2026 Zach Waddle). -/
namespace Deldor14.Star.Waddle39
open SimpleGraph Finset

namespace Host45
private def rows : List ℕ := [279206957088, 4398591836676, 2233655656706, 17731772745744, 8865903150088, 1116827828353, 34634616274944, 567212640288, 618609545220, 687734260738, 585222865424, 554055237768, 826798047489, 66060288, 1101660193824, 8937828008196, 17610440708098, 2474439082128, 4432542042120, 68989223425, 1040384, 2336613212704, 1375463286788, 4468947034242, 8796363567120, 17630849147905, 541165879296, 4407712547104, 17600793280644, 1112396661250, 8728413200, 2207621599240, 8805253416961, 8522825728, 8830519935136, 2216304051204, 1099587649808, 17867133190664, 4535556902913, 8128, 17661446602848, 36509450308, 9071113797698, 4419538157648, 1237252636744]
private def edge (i j : Fin 45) : Bool := (rows.getD i.val 0).testBit j.val
private theorem symm : ∀ i j, edge i j=edge j i := by decide +kernel
private theorem irrefl : ∀ i, edge i i=false := by decide +kernel
private def G : SimpleGraph (Fin 45) where
  Adj i j := edge i j=true
  symm := ⟨fun i j h => (symm i j).symm ▸ h⟩
  loopless := ⟨fun i h => Bool.noConfusion ((irrefl i).symm.trans h)⟩
private instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (edge i j=true))
private theorem codegree : ∀ i j : Fin 45, i≠j → (univ.filter (fun x => edge i x && edge j x)).card≤1 := by decide +kernel
private theorem no_square : ¬(cycleGraph 4).IsContained G := by
  rintro ⟨f⟩
  have e01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have e21 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide)
  have e03 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide)
  have e23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have few := Finset.card_le_one.mp (codegree (f 0) (f 2) (f.injective.ne (by decide)))
  have eq := few (a:=f 1) (b:=f 3)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e01,e21⟩)⟩)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e03,e23⟩)⟩)
  exact (by decide : (1:Fin 4)≠3) (f.injective eq)
private theorem minimum : ∀ i : Fin 45, 6 ≤ (univ.filter (fun j => edge i j)).card := by decide +kernel
theorem lower : 46 ≤ Deldor14.Star.number 39 := by
  classical
  apply (show 45<Deldor14.Star.number 39 from ?_)
  have h := lower_from_host G no_square (n:=39) (by
    intro v
    have mn : 6 ≤ G.degree v := by
      rw [←card_neighborFinset_eq_degree]
      have seteq : G.neighborFinset v = univ.filter (fun j => edge v j) := by
        ext j
        simp only [mem_neighborFinset,mem_filter,mem_univ,true_and]
        rfl
      rw [seteq]
      exact minimum v
    rw [degree_compl,Fintype.card_fin]
    omega)
  simpa using h
end Host45

namespace Host58
private def rows : List ℕ := [4538922520609024, 72622751672176656, 144119603437510688, 1134730630152256, 9077845041086978, 18155690048750596, 36311371541121032, 32512, 145242196101169281, 18014707755778192, 9290877818175648, 36169689193251008, 563500817580162, 4582764599312516, 72097178606108808, 17523466567680, 36028868154885121, 72128065894875424, 4785151914541632, 19140367202983938, 35270288478212, 144678211052126216, 2234207627640832, 18034206934303233, 36055189594046736, 9029189495820352, 144132952061118466, 72076287077785604, 17875788170248, 285978576338026496, 2533859040169985, 2323285249441808, 2814887224935456, 2396935617249538, 3379900900706308, 2260597047689736, 4161536, 74771152799745, 144150922472227344, 37154972877492256, 18577350744637760, 72347882295952386, 9007345317232644, 4646570515537928, 532676608, 72198606409449473, 281614567481360, 18058387568724000, 144187756921488448, 4504703440261122, 9007766195142920, 68182605824, 9578945838325761, 5633898151150608, 141837545767456, 72058144347457600, 36066181085544450, 281750460694788]
private def edge (i j : Fin 58) : Bool := (rows.getD i.val 0).testBit j.val
private theorem symm : ∀ i j, edge i j=edge j i := by decide +kernel
private theorem irrefl : ∀ i, edge i i=false := by decide +kernel
private def G : SimpleGraph (Fin 58) where
  Adj i j := edge i j=true
  symm := ⟨fun i j h => (symm i j).symm ▸ h⟩
  loopless := ⟨fun i h => Bool.noConfusion ((irrefl i).symm.trans h)⟩
private instance : DecidableRel G.Adj := fun i j => inferInstanceAs (Decidable (edge i j=true))
private theorem codegree : ∀ i j : Fin 58, i≠j → (univ.filter (fun x => edge i x && edge j x)).card≤1 := by decide +kernel
private theorem no_square : ¬(cycleGraph 4).IsContained G := by
  rintro ⟨f⟩
  have e01 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 1 by decide)
  have e21 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 1 by decide)
  have e03 := f.toHom.map_adj (show (cycleGraph 4).Adj 0 3 by decide)
  have e23 := f.toHom.map_adj (show (cycleGraph 4).Adj 2 3 by decide)
  have few := Finset.card_le_one.mp (codegree (f 0) (f 2) (f.injective.ne (by decide)))
  have eq := few (a:=f 1) (b:=f 3)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e01,e21⟩)⟩)
     (mem_filter.mpr ⟨mem_univ _,(by simp only [Bool.and_eq_true]; exact ⟨e03,e23⟩)⟩)
  exact (by decide : (1:Fin 4)≠3) (f.injective eq)
private theorem minimum : ∀ i : Fin 58, 7 ≤ (univ.filter (fun j => edge i j)).card := by decide +kernel
theorem lower : 59 ≤ Deldor14.Star.number 51 := by
  classical
  apply (show 58<Deldor14.Star.number 51 from ?_)
  have h := lower_from_host G no_square (n:=51) (by
    intro v
    have mn : 7 ≤ G.degree v := by
      rw [←card_neighborFinset_eq_degree]
      have seteq : G.neighborFinset v = univ.filter (fun j => edge v j) := by
        ext j
        simp only [mem_neighborFinset,mem_filter,mem_univ,true_and]
        rfl
      rw [seteq]
      exact minimum v
    rw [degree_compl,Fintype.card_fin]
    omega)
  simpa using h
end Host58
end Deldor14.Star.Waddle39

/-
The no-triangle lemma follows §5 of Zach Waddle, *The Ramsey number
R(C₄,K₁,₃₉)* (2026), © Zach Waddle, CC BY 4.0.
https://github.com/zach7036/c4-star-ramsey/blob/86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33/R_C4_K1_39.md
https://creativecommons.org/licenses/by/4.0/
Lean formalization by Deldor14.
-/

namespace Deldor14.Star.Waddle39
open Finset SimpleGraph ExcessOne
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem common_unique (red : ¬ (cycleGraph 4).IsContained G)
    {v x a b : V} (vx : v ≠ x) (va : G.Adj v a) (xa : G.Adj x a)
    (vb : G.Adj v b) (xb : G.Adj x b) : a = b :=
  Finset.card_le_one.mp (codeg_le_one G red vx) a ((mem_common G).mpr ⟨va,xa⟩)
    b ((mem_common G).mpr ⟨vb,xb⟩)

theorem no_triangle {d : ℕ} (red : ¬ (cycleGraph 4).IsContained G)
    (reg : ∀ v, G.degree v = d) (odd : Odd d) (v : V)
    (close : missing G v ⊆ G.neighborFinset v) {u w : V}
    (vu : G.Adj v u) (vw : G.Adj v w) (uw : G.Adj u w) : False := by
  classical
  let S := ((G.neighborFinset u).erase v).erase w
  have Smem {x : V} : x ∈ S ↔ x ≠ w ∧ x ≠ v ∧ G.Adj u x := by simp [S]
  have wm : w ∈ (G.neighborFinset u).erase v := by simp [vw.ne.symm,uw]
  have vm : v ∈ G.neighborFinset u := by simp [vu.symm]
  have Ssize : S.card = d - 1 - 1 := by
    simp only [S,card_erase_of_mem wm,card_erase_of_mem vm,card_neighborFinset_eq_degree,reg]
  have deg : 0 < d-1 := by
    have pos := Finset.card_pos.mpr ⟨w,wm⟩
    rwa [card_erase_of_mem vm,card_neighborFinset_eq_degree,reg] at pos
  have inside (x : V) (hx : x ∈ S) : (S.filter (G.Adj x)).card = 1 := by
    obtain ⟨xw,xv,ux⟩ := Smem.mp hx
    have vx : ¬ G.Adj v x := fun h => xw (common_unique G red vu.ne h ux vw uw)
    let X := (G.neighborFinset x).erase u
    let A := (G.neighborFinset v).erase w
    have xm {y : V} : y ∈ X ↔ y ≠ u ∧ G.Adj x y := by simp [X]
    have am {a : V} : a ∈ A ↔ a ≠ w ∧ G.Adj v a := by simp [A]
    have outside {y : V} (hy : y ∈ X) : y ≠ v ∧ ¬G.Adj v y := by
      obtain ⟨yu,xy⟩ := xm.mp hy
      refine ⟨fun h => vx (h ▸ xy.symm), ?_⟩
      intro vy
      exact yu (common_unique G red xv xy vy ux.symm vu)
    have witness (y : X) : ∃ a : A, G.Adj y.val a.val := by
      have yv := outside y.property
      have notEmpty : common G v y.val ≠ ∅ := by
        intro h
        have mem := close ((mem_missing G).mpr ⟨yv.1,h⟩)
        exact yv.2 ((G.mem_neighborFinset _ _).mp mem)
      obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr notEmpty
      obtain ⟨va,ya⟩ := (mem_common G).mp ha
      have aw : a ≠ w := by
        intro e
        subst a
        exact xw (common_unique G red (xm.mp y.property).1 (xm.mp y.property).2.symm ux ya uw)
      exact ⟨⟨a,am.mpr ⟨aw,va⟩⟩,ya⟩
    choose f hf using witness
    have inj : Function.Injective f := by
      intro y z e
      have az := hf z
      rw [←e] at az
      apply Subtype.ext
      have xa : x ≠ (f y).val := fun h => vx (h ▸ (am.mp (f y).property).2)
      exact common_unique G red xa (xm.mp y.property).2 (hf y).symm
        (xm.mp z.property).2 az.symm
    have sz : Fintype.card X = Fintype.card A := by
      rw [Fintype.card_coe,Fintype.card_coe]
      change ((G.neighborFinset x).erase u).card = ((G.neighborFinset v).erase w).card
      rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr ux.symm),
        card_erase_of_mem ((G.mem_neighborFinset _ _).mpr vw),card_neighborFinset_eq_degree,
        card_neighborFinset_eq_degree,reg,reg]
    have onto := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨inj,sz⟩).2
    obtain ⟨y,hy⟩ := onto ⟨u,am.mpr ⟨uw.ne,vu⟩⟩
    have yu := hf y
    rw [hy] at yu
    have yo := outside y.property
    have ys : y.val ∈ S := Smem.mpr ⟨fun e => yo.2 (e ▸ vw),yo.1,yu.symm⟩
    apply Finset.card_eq_one.mpr
    refine ⟨y.val, ?_⟩
    ext z
    simp only [Finset.mem_filter,Finset.mem_singleton]
    constructor
    · rintro ⟨hz,xz⟩
      exact common_unique G red ux.ne (Smem.mp hz).2.2 xz yu.symm (xm.mp y.property).2
    · rintro rfl
      exact ⟨ys,(xm.mp y.property).2⟩
  have ev := even_edges G S
  have eq : (∑ a ∈ S, ∑ b ∈ S, (if G.Adj a b then (1:ℤ) else 0)) = (S.card : ℤ) := by
    trans ∑ _a ∈ S, (1:ℤ)
    swap
    · simp
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_boole,inside a ha]
    norm_num
  rw [eq,Ssize] at ev
  obtain ⟨k,hk⟩ := ev
  obtain ⟨j,hj⟩ := odd
  omega

theorem one_missing_neighbor (red : ¬ (cycleGraph 4).IsContained G)
    (reg : ∀ v, G.degree v = 7) (v : V) (three : (missing G v).card = 3) :
    (G.neighborFinset v ∩ missing G v).card = 1 := by
  classical
  let T := G.neighborFinset v
  let D := missing G v
  have Tsize : T.card = 7 := (G.card_neighborFinset_eq_degree v).trans (reg v)
  have Dsize : D.card = 3 := three
  have val (a : V) (ha : a ∈ T) : (common G v a).card = if a ∈ D then 0 else 1 := by
    have va := (G.mem_neighborFinset _ _).mp ha
    split
    · rename_i h
      rw [((mem_missing G).mp h).2,Finset.card_empty]
    · rename_i h
      have emp : common G v a ≠ ∅ := fun e => h ((mem_missing G).mpr ⟨va.ne.symm,e⟩)
      have low := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr emp)
      have high := codeg_le_one G red va.ne
      omega
  have even := even_edges G T
  have count : (∑ a ∈ T, ∑ b ∈ T, if G.Adj a b then (1:ℤ) else 0) =
      ((T.filter (fun a => a ∉ D)).card : ℤ) := by
    trans ∑ a ∈ T, if a ∉ D then (1:ℤ) else 0
    · apply sum_congr rfl
      intro a ha
      rw [sum_boole]
      have e : T.filter (G.Adj a) = common G v a := by
        ext b
        simp [T,common]
      rw [e,val a ha]
      by_cases h : a ∈ D <;> simp [h]
    · rw [sum_boole]
  rw [count] at even
  obtain ⟨k,hk⟩ := even
  have partition := Finset.card_filter_add_card_filter_not (s:=T) (fun a => a ∈ D)
  have meet : T.filter (fun a => a ∈ D) = T ∩ D := by ext; simp
  rw [meet,Tsize] at partition
  have upper := Finset.card_le_card (Finset.inter_subset_right (s₁:=T) (s₂:=D))
  change (T ∩ D).card = 1
  by_contra ne
  have full : (T ∩ D).card = 3 := by omega
  have eq : T ∩ D = D := eq_of_subset_of_card_le inter_subset_right (by omega)
  have close : D ⊆ T := fun a ha => Finset.mem_inter.mp (eq ▸ ha) |>.1
  have sub : T ⊆ D := by
    intro a ha
    have va := (G.mem_neighborFinset _ _).mp ha
    apply (mem_missing G).mpr
    refine ⟨va.ne.symm, Finset.eq_empty_iff_forall_notMem.mpr ?_⟩
    intro b hb
    obtain ⟨vb,ab⟩ := (mem_common G).mp hb
    exact no_triangle G red reg (by decide : Odd 7) v close va vb ab
  have low := Finset.card_le_card sub
  omega

end Deldor14.Star.Waddle39

/- Triangle and edge counts in rows of the deficiency graph. -/

namespace Deldor14.Star.Waddle39
open Finset SimpleGraph Matrix ExcessOne
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem deficiency_row_bound (v : V) (three : (missing G v).card = 3)
    (one : (G.neighborFinset v ∩ missing G v).card = 1) :
    let e := ∑ x ∈ missing G v, ∑ y ∈ missing G v, G.adjMatrix ℝ y x
    0 ≤ e ∧ e ≤ 2 := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp one
  have ain : a ∈ G.neighborFinset v ∩ missing G v := by rw [ha]; simp
  obtain ⟨va,ma⟩ := mem_inter.mp ain
  have va' := (G.mem_neighborFinset _ _).mp va
  have isolated (b : V) (hb : b ∈ missing G v) : ¬G.Adj a b := by
    intro ab
    have mem := (mem_common G).mpr ⟨va',ab.symm⟩
    rw [((mem_missing G).mp hb).2] at mem
    exact Finset.notMem_empty _ mem
  have two : ((missing G v).erase a).card = 2 := by rw [card_erase_of_mem ma,three]
  obtain ⟨b,c,bc,pair⟩ := Finset.card_eq_two.mp two
  have triple := Finset.insert_erase ma
  rw [pair] at triple
  have bm : b ∈ (missing G v).erase a := by rw [pair]; simp
  have cm : c ∈ (missing G v).erase a := by rw [pair]; simp
  obtain ⟨ba,bm⟩ := Finset.mem_erase.mp bm
  obtain ⟨ca,cm⟩ := Finset.mem_erase.mp cm
  have ab := isolated b bm
  have ac := isolated c cm
  change 0 ≤ ∑ x ∈ missing G v, ∑ y ∈ missing G v, G.adjMatrix ℝ y x ∧
    (∑ x ∈ missing G v, ∑ y ∈ missing G v, G.adjMatrix ℝ y x) ≤ 2
  rw [←triple]
  have hn : a ∉ ({b,c} : Finset V) := by simp [ba.symm,ca.symm]
  have hb : b ∉ ({c} : Finset V) := by simp [bc]
  simp only [Finset.sum_insert hn,Finset.sum_insert hb,Finset.sum_singleton]
  by_cases ed : G.Adj b c <;>
    simp [adjMatrix_apply,ab,ac,
      G.adj_comm b a,G.adj_comm c a,G.adj_comm c b,ed] <;> norm_num

theorem trace_counts (B : SimpleGraph V) [DecidableRel B.Adj]
    (rows : ∀ v, B.neighborFinset v = missing G v)
    (three : ∀ v, (missing G v).card = 3)
    (one : ∀ v, (G.neighborFinset v ∩ missing G v).card = 1) :
    (G.adjMatrix ℝ * B.adjMatrix ℝ).trace = Fintype.card V ∧
    0 ≤ (G.adjMatrix ℝ * B.adjMatrix ℝ ^ 2).trace ∧
    (G.adjMatrix ℝ * B.adjMatrix ℝ ^ 2).trace ≤ 2 * (Fintype.card V : ℝ) := by
  classical
  have diag1 (v : V) : (G.adjMatrix ℝ * B.adjMatrix ℝ) v v = 1 := by
    rw [B.mul_adjMatrix_apply,rows]
    simp only [adjMatrix_apply,sum_boole]
    have eq : (missing G v).filter (G.Adj v) = G.neighborFinset v ∩ missing G v := by
      ext x
      simp [and_comm]
    rw [eq,one]
    norm_num
  have diag2 (v : V) :
      0 ≤ (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v ∧
      (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v ≤ 2 := by
    simp only [B.mul_adjMatrix_apply,B.adjMatrix_mul_apply,rows]
    exact deficiency_row_bound G v (three v) (one v)
  constructor
  · simp [Matrix.trace,Matrix.diag,diag1]
  rw [sq,←Matrix.mul_assoc,Matrix.trace_mul_cycle]
  change 0 ≤ ∑ v, (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v ∧
    (∑ v, (B.adjMatrix ℝ * G.adjMatrix ℝ * B.adjMatrix ℝ) v v) ≤ _
  refine ⟨Finset.sum_nonneg (fun v _ => (diag2 v).1),?_⟩
  calc
    _ ≤ ∑ _v : V, (2:ℝ) := Finset.sum_le_sum fun v _ => (diag2 v).2
    _ = _ := by simp [mul_comm]

end Deldor14.Star.Waddle39

/- The two mixed traces for the putative regular graph on 46 vertices. -/
namespace Deldor14.Star.Waddle39
open Finset SimpleGraph ExcessOne Deficiency

theorem traces_46 (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj]
    (red : ¬ (cycleGraph 4).IsContained G) (reg : ∀ v, G.degree v = 7) :
    let A := G.adjMatrix ℝ
    let D := (graph G).adjMatrix ℝ
    (A*D).trace = 46 ∧ 0 ≤ (A*D^2).trace ∧ (A*D^2).trace ≤ 92 := by
  have three (v : Fin 46) : (missing G v).card = 3 := by
    rw [←neighbors,card_neighborFinset_eq_degree]
    exact degree G red (d:=7) (e:=3) (by decide) reg v
  have result := trace_counts G (graph G) (neighbors G) three
    (fun v => one_missing_neighbor G red reg v (three v))
  norm_num at result
  exact result

end Deldor14.Star.Waddle39

/- Positive semidefiniteness of the signless Laplacian and the two-sided degree bound. -/
namespace Deldor14.Star.Waddle39
open Matrix SimpleGraph Finset Unitary
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem sum_endpoint (f : V → ℝ) :
    (∑ i, ∑ j, if G.Adj i j then f i else 0) = ∑ i, G.degree i * f i := by
  apply sum_congr rfl
  intro i _
  rw [← Finset.sum_filter]
  simp [← G.neighborFinset_eq_filter]

theorem signless_pos : (G.degMatrix ℝ + G.adjMatrix ℝ).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change _ᴴ=_
    rw [conjTranspose_eq_transpose_of_trivial,transpose_add]
    rw [show (G.adjMatrix ℝ)ᵀ = G.adjMatrix ℝ from G.isSymm_adjMatrix]
    simp [degMatrix]
  · intro x
    simp only [star_trivial,Matrix.add_mulVec,dotProduct_add,G.dotProduct_mulVec_degMatrix,
      G.dotProduct_mulVec_adjMatrix]
    have e1 := sum_endpoint G (fun i => x i*x i)
    have e2 : (∑ i,∑ j,if G.Adj i j then x j*x j else 0) = ∑ i,(G.degree i:ℝ)*(x i*x i) := by
      rw [Finset.sum_comm]
      simpa only [G.adj_comm] using e1
    have pos : 0 ≤ ∑ i,∑ j, if G.Adj i j then x i*x i+2*(x i*x j)+x j*x j else 0 := by
      apply sum_nonneg
      intro i _
      apply sum_nonneg
      intro j _
      split_ifs
      · nlinarith [sq_nonneg (x i+x j)]
      · exact le_rfl
    have dist (i j : V) : (if G.Adj i j then x i*x i+2*(x i*x j)+x j*x j else 0) =
        (if G.Adj i j then x i*x i else 0) + 2*(if G.Adj i j then x i*x j else 0) +
        (if G.Adj i j then x j*x j else 0) := by split_ifs <;> ring
    simp_rw [dist] at pos
    simp only [sum_add_distrib,←mul_sum,e1,e2] at pos
    simp only [mul_assoc] at *
    linarith

theorem signed_diag_bound (reg : ∀ x,G.degree x=3) (U : Matrix.unitaryGroup V ℝ) (i : V) :
    -3 ≤ ((conjStarAlgAut ℝ _ (star U)) (G.adjMatrix ℝ)) i i ∧
      ((conjStarAlgAut ℝ _ (star U)) (G.adjMatrix ℝ)) i i ≤ 3 := by
  let e := conjStarAlgAut ℝ _ (star U)
  have deg : G.degMatrix ℝ = (3:ℝ) • (1:Matrix V V ℝ) := by
    ext i j
    simp [degMatrix,Matrix.smul_apply,Matrix.one_apply,diagonal_apply,reg]
  have diagPos {B : Matrix V V ℝ} (h : B.PosSemidef) : 0≤(e B) i i := by
    have p := h.mul_mul_conjTranspose_same ((star U : Matrix.unitaryGroup V ℝ) : Matrix V V ℝ)
    exact p.diag_nonneg
  have plus := diagPos (signless_pos G)
  have minus := diagPos (G.posSemidef_lapMatrix ℝ)
  rw [lapMatrix,deg,map_sub,map_smul,map_one,Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] at minus
  rw [deg,map_add,map_smul,map_one,Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one] at plus
  change -3 ≤ (e _) i i ∧ (e _) i i ≤ 3
  constructor <;> linarith
end Deldor14.Star.Waddle39

/- Integer-scaled dual polynomials from Zach Waddle's certificate for the star with 39 leaves.
Source https://github.com/zach7036/c4-star-ramsey, commit 86a1c5055eea5e3891b2eeaea6c7ee1b3977bd33.
The interval bounds are independently checked in a rational Bernstein basis. -/
namespace Deldor14.Star.Waddle39
open Finset
def upperPoly (x : ℝ) := (555946:ℝ)*(x)^0 + (390143:ℝ)*(x)^1 + (-16348:ℝ)*(x)^2 + (-43595:ℝ)*(x)^3 + (1216:ℝ)*(x)^4 + (2115:ℝ)*(x)^5
def lowerPoly (x : ℝ) := (459756:ℝ)*(x)^0 + (395916:ℝ)*(x)^1 + (11122:ℝ)*(x)^2 + (-45053:ℝ)*(x)^3 + (-812:ℝ)*(x)^4 + (2200:ℝ)*(x)^5
private theorem upPosPart1 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (1123671614636531795861820261283532351891813399904303174240/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (1197531464085065941450187494881695368303835725480760757935600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (3416316947996018576902430246843087421321691917461760757935600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (3294906434713644886308663101510879994966649054721380378967800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (1221662348416924877555492969987761009267331787677970094741950/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (153275347093737278341368453924605583424222006167559509474195/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart2 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(1262259526419/500000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(1262259526419/500000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (156953955423986973021561296818796117426403334315580937701575680/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*((1262259526419/500000000000:ℝ)-x)^5 + (668216660205185812730551904800608915542583901826820516380908800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*((1262259526419/500000000000:ℝ)-x)^4 + (1099551759347805882914618699706051562603232949955318774571363200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*((1262259526419/500000000000:ℝ)-x)^3 + (869633778837464336177826210934607046293692535377805080928522400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*((1262259526419/500000000000:ℝ)-x)^2 + (329226520188459210738422204641115057378453884358420405348195900/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*((1262259526419/500000000000:ℝ)-x)^1 + (47888406195466785886070519443971824555567522692524585802229385/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*((1262259526419/500000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart3 (x : ℝ) (ha : (1262259526419/500000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(1262259526419/500000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(670753175473/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (47888406195466785886070519443971824555567522692524585802229385/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^0*((670753175473/250000000000:ℝ)-x)^5 + (149657541766208648122282989798603188177221342566825452674097950/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^1*((670753175473/250000000000:ℝ)-x)^4 + (151357865148462085713269351564559569488762368211425270232130600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^2*((670753175473/250000000000:ℝ)-x)^3 + (47886924791301947315847210032575302521430853111388846821420400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^3*((670753175473/250000000000:ℝ)-x)^2 + (1438818470182442462122644193751348988840042471720282273806800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^4*((670753175473/250000000000:ℝ)-x)^1 + (3147233534465586743178749384329301318271528965285904303174240/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^5*((670753175473/250000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart4 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  rcases le_total x (1262259526419/500000000000:ℝ) with h|h
  · exact upPosPart2 x ha h
  · exact upPosPart3 x h hb
private theorem upPosPart5 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have posA : 0≤x-(670753175473/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (x) + (-1000000) = (98351047952049585724335918260290666195985280165184509474195/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^0*(3-x)^5 + (1385339564894341131982373511794900681137276547995250000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^1*(3-x)^4 + (13758346061960374283079150752184561031187500000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^2*(3-x)^3 + (37732094713286814137917547171875000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^3*(3-x)^2 + (39530494077903863281250000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^4*(3-x)^1 + (14276367187500000000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^5*(3-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upPosPart6 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  rcases le_total x (670753175473/250000000000:ℝ) with h|h
  · exact upPosPart4 x ha h
  · exact upPosPart5 x h hb
private theorem upPosPart7 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact upPosPart1 x ha h
  · exact upPosPart6 x h hb
private theorem upPos (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ 1*upperPoly (x) + (-1000000) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply upPosPart7 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
private theorem upNegPart8 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (1088109726824542504769843427702844561940778491624095696825760/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (3035282761365202474713882898687731122574175189591239242064400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (2758510375486067405546562885848966428702654150122239242064400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (856047856027819045164171637440721161618691555326619621032200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (52843671856683197329599226240722975772295258898029905258050/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (1522878909403467921516990439032698469069887896440490525805/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart9 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(2445272228311/1000000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(2445272228311/1000000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (49901696103332836852268742706223463434482086590561993549578240/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*((2445272228311/1000000000000:ℝ)-x)^5 + (64249360656272831031973247040505673055640356625580721779404800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*((2445272228311/1000000000000:ℝ)-x)^4 + (95850283931664874356409215176284054406487772730542263113958400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*((2445272228311/1000000000000:ℝ)-x)^3 + (369570845725970819811821291046880675147904306195528480224713600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*((2445272228311/1000000000000:ℝ)-x)^2 + (458140964050148631216183891888168428840745167422676710098312200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*((2445272228311/1000000000000:ℝ)-x)^1 + (170066127425037823461220877670064549494416572654841699267204635/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*((2445272228311/1000000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart10 (x : ℝ) (ha : (2445272228311/1000000000000:ℝ)≤x) (hb : x≤(1262259526419/500000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(2445272228311/1000000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(1262259526419/500000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (170066127425037823461220877670064549494416572654841699267204635/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^0*((1262259526419/500000000000:ℝ)-x)^5 + (1242520310200229603396024884812477066103420559125740282573734150/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^1*((1262259526419/500000000000:ℝ)-x)^4 + (3507088230326294708531185262744115224198605873007782770126401400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^2*((1262259526419/500000000000:ℝ)-x)^3 + (4731481847223618772223775339394121663856379858685723517251201200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^3*((1262259526419/500000000000:ℝ)-x)^2 + (3060477718039532849327977552081711793854021394911434650250514800/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^4*((1262259526419/500000000000:ℝ)-x)^1 + (763623308089152137580737034276067788603489631494765254328659680/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2445272228311/1000000000000:ℝ))^5*((1262259526419/500000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart11 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(1262259526419/500000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (2445272228311/1000000000000:ℝ) with h|h
  · exact upNegPart9 x ha h
  · exact upNegPart10 x h hb
private theorem upNegPart12 (x : ℝ) (ha : (1262259526419/500000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(1262259526419/500000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(670753175473/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (23863228377786004299398032321127118393859050984211414197770615/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^0*((670753175473/250000000000:ℝ)-x)^5 + (166668568289319261407971887811799788792009427581206547325902050/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^1*((670753175473/250000000000:ℝ)-x)^4 + (443767496374043096477811662264422018038846024731166729767869400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^2*((670753175473/250000000000:ℝ)-x)^3 + (560104384163795235974495429560902727873397430680483153178579600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^3*((670753175473/250000000000:ℝ)-x)^2 + (335761940226871103448830932250154653267354726068951717726193200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^4*((670753175473/250000000000:ℝ)-x)^1 + (76613102247720838723726875449776224050899152254810095696825760/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1262259526419/500000000000:ℝ))^5*((670753175473/250000000000:ℝ)-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart13 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (1262259526419/500000000000:ℝ) with h|h
  · exact upNegPart11 x ha h
  · exact upNegPart12 x h hb
private theorem upNegPart14 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have posA : 0≤x-(670753175473/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : 1*upperPoly (-x) + (0) = (2394159445241276210116464857805507001590598507962815490525805/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^0*(3-x)^5 + (14927270414439699186195039601447939194649307240132750000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^1*(3-x)^4 + (33665942922035935820670566709992481176812500000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^2*(3-x)^3 + (32402060040213468943495557953125000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^3*(3-x)^2 + (11276814927740824218750000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^4*(3-x)^1 + (976562500000000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^5*(3-x)^0 := by unfold upperPoly; ring
  rw [eq]
  positivity
private theorem upNegPart15 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (670753175473/250000000000:ℝ) with h|h
  · exact upNegPart13 x ha h
  · exact upNegPart14 x h hb
private theorem upNegPart16 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ 1*upperPoly (-x) + (0) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact upNegPart8 x ha h
  · exact upNegPart15 x h hb
private theorem upNeg (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ 1*upperPoly (-x) + (0) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply upNegPart16 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
private theorem loPosPart17 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(512259526419/250000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(512259526419/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (27584982012691358767241415817142022109440685392730334305689600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((512259526419/250000000000:ℝ)-x)^5 + (103536234988737114429558001266207765955493123584210753646336000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((512259526419/250000000000:ℝ)-x)^4 + (150392172347464616636426126376539613288125515418524130469504000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((512259526419/250000000000:ℝ)-x)^3 + (105332363260223745744153936595299575572696009095549097852128000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((512259526419/250000000000:ℝ)-x)^2 + (35528391364599752328243391402301406319900768110201911694548000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((512259526419/250000000000:ℝ)-x)^1 + (4630071536644650128571499361381086589155689296435936754182200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((512259526419/250000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart18 (x : ℝ) (ha : (512259526419/250000000000:ℝ)≤x) (hb : x≤(220753175473/100000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(512259526419/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(220753175473/100000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (148162289172628804114287979564194770852982057485949976133830400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^0*((220753175473/100000000000:ℝ)-x)^5 + (542762906961119993605265584294638280278953141381394233890960000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^1*((220753175473/100000000000:ℝ)-x)^4 + (765584841464361835013345458335843942063190627618883723151600000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^2*((220753175473/100000000000:ℝ)-x)^3 + (516741112800872016200483979319096018654132794112869769293000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^3*((220753175473/100000000000:ℝ)-x)^2 + (166539427788601200648657001981693625496606971615279070538750000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^4*((220753175473/100000000000:ℝ)-x)^1 + (20775662724449612540913379894903425879571574280588178423125000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(512259526419/250000000000:ℝ))^5*((220753175473/100000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart19 (x : ℝ) (ha : (220753175473/100000000000:ℝ)≤x) (hb : x≤(2286778579257/1000000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(220753175473/100000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(2286778579257/1000000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (664821207182387601309228156636909628146290376978821709540000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^0*((2286778579257/1000000000000:ℝ)-x)^5 + (2321528209250287799440699143069724203151466281496697692930000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^1*((2286778579257/1000000000000:ℝ)-x)^4 + (3104620996304981896790433168640646734850326559859655847274000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^2*((2286778579257/1000000000000:ℝ)-x)^3 + (2005540035041667447240579280593957745966212431722730262546600000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^3*((2286778579257/1000000000000:ℝ)-x)^2 + (658298212063313659906445838616286118308658931807296618145970000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^4*((2286778579257/1000000000000:ℝ)-x)^1 + (100665295319577693895201243857065918587475008481085631266274600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(220753175473/100000000000:ℝ))^5*((2286778579257/1000000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart20 (x : ℝ) (ha : (2286778579257/1000000000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(2286778579257/1000000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (100665295319577693895201243857065918587475008481085631266274600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (348354741132463279045566599954373067566091153003559694516776000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (765766151318265923797062325946305542995941316507782568029824000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (1182685749991710460514441896697506388537134345588457393804288000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (957205484070547973775750508478747916465624083384196175024128000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (292589563645067634478378085257145308345692762835786697782067200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(2286778579257/1000000000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart21 (x : ℝ) (ha : (220753175473/100000000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (2286778579257/1000000000000:ℝ) with h|h
  · exact loPosPart19 x ha h
  · exact loPosPart20 x h hb
private theorem loPosPart22 (x : ℝ) (ha : (512259526419/250000000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (220753175473/100000000000:ℝ) with h|h
  · exact loPosPart18 x ha h
  · exact loPosPart21 x h hb
private theorem loPosPart23 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (512259526419/250000000000:ℝ) with h|h
  · exact loPosPart17 x ha h
  · exact loPosPart22 x h hb
private theorem loPosPart24 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (x) + (1000000) = (8929124867098011306102846840122842661916893397088217095400/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*(3-x)^5 + (168117873884999382364532768821458604242894948136500000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*(3-x)^4 + (1129585422963148100372143066560324361703125000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*(3-x)^3 + (1921743878691896243045591771484375000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*(3-x)^2 + (958253661474991943359375000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*(3-x)^1 + (30517578125000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*(3-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loPosPart25 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact loPosPart23 x ha h
  · exact loPosPart24 x h hb
private theorem loPos (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ -1*lowerPoly (x) + (1000000) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply loPosPart25 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
private theorem loNegPart26 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤(295753175473/125000000000:ℝ)) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(108253175473/62500000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(295753175473/125000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (3814038667054337964233557192002608887255133845177052947200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^0*((295753175473/125000000000:ℝ)-x)^5 + (1330596721324964004229442968423987087803616525704942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^1*((295753175473/125000000000:ℝ)-x)^4 + (3857827929155154033334920021988173482982845216796942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^2*((295753175473/125000000000:ℝ)-x)^3 + (3834677632413381655624022684062845353877911953944471316184000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^3*((295753175473/125000000000:ℝ)-x)^2 + (1497118317934343731469434290161207970265319074872617829046000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^4*((295753175473/125000000000:ℝ)-x)^1 + (200361871168423872542618589949165220576037891125911782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(108253175473/62500000000:ℝ))^5*((295753175473/125000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart27 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤(670753175473/250000000000:ℝ)) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(295753175473/125000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(670753175473/250000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (6411579877389563921363794878373287058433212516029177052947200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^0*((670753175473/250000000000:ℝ)-x)^5 + (24132955993472229706717512945220325414003988672256942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^1*((670753175473/250000000000:ℝ)-x)^4 + (31214609778875243254611874380425756500299946054440942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^2*((670753175473/250000000000:ℝ)-x)^3 + (15630347238340659817755407008587255452485451718312471316184000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^3*((670753175473/250000000000:ℝ)-x)^2 + (2355409415715779774260321796386448578502107602351117829046000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^4*((670753175473/250000000000:ℝ)-x)^1 + (225171779317914855390567474472524870867972727512411782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(295753175473/125000000000:ℝ))^5*((670753175473/250000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart28 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤(1420753175473/500000000000:ℝ)) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(670753175473/250000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤(1420753175473/500000000000:ℝ)-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (7205496938173275372498159183120795867775127280397177052947200/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^0*((1420753175473/500000000000:ℝ)-x)^5 + (16354676384847088905571045131222791752279732965360942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^1*((1420753175473/500000000000:ℝ)-x)^4 + (61047155106909116094260945235816887108621647729728942632368000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^2*((1420753175473/500000000000:ℝ)-x)^3 + (172251149333502393002330519198292137869231781247048471316184000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^3*((1420753175473/500000000000:ℝ)-x)^2 + (191350052963739772143014658092315619705225684657308117829046000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^4*((1420753175473/500000000000:ℝ)-x)^1 + (71003755229622899131499694554832986660233092400285411782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(670753175473/250000000000:ℝ))^5*((1420753175473/500000000000:ℝ)-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart29 (x : ℝ) (ha : (1420753175473/500000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have posA : 0≤x-(1420753175473/500000000000:ℝ) := sub_nonneg.mpr ha
  have posB : 0≤3-x := sub_nonneg.mpr hb
  have eq : -1*lowerPoly (-x) + (0) = (71003755229622899131499694554832986660233092400285411782904600/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^0*(3-x)^5 + (518687499332489219171982287456014246897105239345546000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^1*(3-x)^4 + (1481600934808500181118201036653086646636750000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^2*(3-x)^3 + (2060358888134182641007345940125000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^3*(3-x)^2 + (1396278571489398562500000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^4*(3-x)^1 + (369843750000000000000000000000000000000000000000000000000000000/3125426886462468012498351406642545510066793300267371407:ℝ)*(x-(1420753175473/500000000000:ℝ))^5*(3-x)^0 := by unfold lowerPoly; ring
  rw [eq]
  positivity
private theorem loNegPart30 (x : ℝ) (ha : (670753175473/250000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  rcases le_total x (1420753175473/500000000000:ℝ) with h|h
  · exact loNegPart28 x ha h
  · exact loNegPart29 x h hb
private theorem loNegPart31 (x : ℝ) (ha : (295753175473/125000000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  rcases le_total x (670753175473/250000000000:ℝ) with h|h
  · exact loNegPart27 x ha h
  · exact loNegPart30 x h hb
private theorem loNegPart32 (x : ℝ) (ha : (108253175473/62500000000:ℝ)≤x) (hb : x≤3) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  rcases le_total x (295753175473/125000000000:ℝ) with h|h
  · exact loNegPart26 x ha h
  · exact loNegPart31 x h hb
private theorem loNeg (x : ℝ) (hp : 0≤x) (lo : 3≤x^2) (hi : x^2≤9) : 0 ≤ -1*lowerPoly (-x) + (0) := by
  have rpos : 0≤(108253175473/62500000000:ℝ) := by norm_num
  have rsq : (108253175473/62500000000:ℝ)^2<3 := by norm_num
  apply loNegPart32 x
  · by_contra! gap
    nlinarith [mul_pos (sub_pos.mpr gap) (show 0<(108253175473/62500000000:ℝ)+x by linarith)]
  · nlinarith [sq_nonneg (x-3)]
theorem dual (x : ℝ) (lo : 3≤x^2) (hi : x^2≤9) :
    lowerPoly x ≤ (if 0<x then 1000000 else 0) ∧ (if 0<x then 1000000 else 0) ≤ upperPoly x := by
  by_cases h : 0<x
  · rw [if_pos h]
    constructor <;> linarith only [upPos x h.le lo hi,loPos x h.le lo hi]
  · rw [if_neg h]
    have xp : 0≤ -x := by linarith
    have l : 3≤(-x)^2 := by nlinarith
    have u : (-x)^2≤9 := by nlinarith
    have a := upNeg (-x) xp l u
    have b := loNeg (-x) xp l u
    rw [neg_neg] at a b
    constructor <;> linarith
end Deldor14.Star.Waddle39

/- Integer obstruction for the nonprincipal eigenvalues, using Waddle's dual polynomials. -/
namespace Deldor14.Star.Waddle39
open Finset

theorem eigenvalue_count_impossible (f j : Fin 46 → ℝ)
    (jSum : ∑ i, j i = 46)
    (principal : ∀ i, f i = 7 → 40 ≤ j i)
    (other : ∀ i, f i ≠ 7 → j i = 0 ∧ 3 ≤ (f i)^2 ∧ (f i)^2 ≤ 9)
    (p1 : ∑ i, (f i)^1 = 0) (p2 : ∑ i, (f i)^2 = 322)
    (p3 : ∑ i, (f i)^3 = 276) (p4 : ∑ i, (f i)^4 = 4186)
    (p5 : 16192 ≤ ∑ i, (f i)^5) (p5' : ∑ i, (f i)^5 ≤ 16284) : False := by
  classical
  let top := univ.filter (fun i => f i = 7)
  have row (i : Fin 46) : (if f i = 7 then (40:ℝ) else 0) ≤ j i := by
    split
    · exact principal i ‹_›
    · rw [(other i ‹_›).1]
  have upper := Finset.sum_le_sum (s:=univ) (fun i _ => row i)
  rw [jSum] at upper
  have tally : (top.card:ℝ)*40 ≤ 46 := by
    simpa [top,Finset.sum_ite] using upper
  have card_le : top.card ≤ 1 := by
    by_contra! h
    have hn : (2:ℝ) ≤ top.card := by exact_mod_cast h
    linarith
  have nonempty : top.Nonempty := by
    by_contra! empty
    have zero (i : Fin 46) : j i = 0 := by
      apply (other i _).1
      intro hi
      have h : i ∈ top := mem_filter.mpr ⟨mem_univ _,hi⟩
      simp [empty] at h
    simp [zero] at jSum
  obtain ⟨t,ht⟩ := Finset.card_eq_one.mp (le_antisymm card_le (Finset.card_pos.mpr nonempty))
  have ft : f t = 7 := (mem_filter.mp (show t ∈ top by rw [ht]; simp)).2
  let S := univ.erase t
  have Ssize : S.card = 45 := by simp [S]
  have band (i : Fin 46) (h : i ∈ S) : 3 ≤ (f i)^2 ∧ (f i)^2 ≤ 9 := by
    apply (other i _).2
    intro hi
    have mem : i ∈ top := mem_filter.mpr ⟨mem_univ _,hi⟩
    rw [ht,mem_singleton] at mem
    exact (mem_erase.mp h).1 mem
  let m (k : ℕ) := ∑ i ∈ S, (f i)^k
  have apart (k : ℕ) : m k + (7:ℝ)^k = ∑ i, (f i)^k := by
    simpa only [m,S,←ft] using (Finset.sum_erase_add univ (fun i => (f i)^k) (mem_univ t))
  have m0 : m 0 = 45 := by simp [m,Ssize]
  have m1 : m 1 = -7 := by linarith only [apart 1,p1]
  have m2 : m 2 = 273 := by linarith only [apart 2,p2]
  have m3 : m 3 = -67 := by linarith only [apart 3,p3]
  have m4 : m 4 = 1785 := by linarith only [apart 4,p4]
  have m5 : -615 ≤ m 5 := by linarith only [apart 5,p5]
  have m5' : m 5 ≤ -523 := by linarith only [apart 5,p5']
  let positive := (S.filter (fun i => 0 < f i)).card
  have indicator : (∑ i ∈ S, if 0 < f i then (1000000:ℝ) else 0) =
      (positive:ℝ) * 1000000 := by simp [positive,Finset.sum_ite]
  have low := Finset.sum_le_sum (s:=S) fun i hi => (dual (f i) (band i hi).1 (band i hi).2).1
  have high := Finset.sum_le_sum (s:=S) fun i hi => (dual (f i) (band i hi).1 (band i hi).2).2
  rw [indicator] at low high
  simp only [upperPoly,lowerPoly,Finset.sum_add_distrib,←Finset.mul_sum] at low high
  change 459756*m 0 + 395916*m 1 + 11122*m 2 + (-45053)*m 3 +
    (-812)*m 4 + 2200*m 5 ≤ (positive:ℝ)*1000000 at low
  change (positive:ℝ)*1000000 ≤ 555946*m 0 + 390143*m 1 + (-16348)*m 2 +
    (-43595)*m 3 + 1216*m 4 + 2115*m 5 at high
  have lb : (21:ℝ) < positive := by linarith only [low,m0,m1,m2,m3,m4,m5]
  have ub : (positive:ℝ) < 22 := by linarith only [high,m0,m1,m2,m3,m4,m5']
  have l : 21 < positive := by exact_mod_cast lb
  have h : positive < 22 := by exact_mod_cast ub
  omega

end Deldor14.Star.Waddle39

/- Waddle's fifth-moment obstruction read in an orthonormal eigenbasis. -/
namespace Deldor14.Star.Waddle39
open Finset Matrix Unitary SimpleGraph

theorem spectral_impossible (A J : Matrix (Fin 46) (Fin 46) ℝ) (D : SimpleGraph (Fin 46))
    [DecidableRel D.Adj] (regD : ∀ i, D.degree i = 3) (hermA : A.IsHermitian)
    (square : A^2 = (6:ℝ) • 1 + J - D.adjMatrix ℝ)
    (rightJ : J*A = (7:ℝ) • J) (trJ : J.trace = 46) (trA : A.trace = 0)
    (tr2 : (A^2).trace = 322) (tr3 : (A^3).trace = 276) (tr4 : (A^4).trace = 4186)
    (tr5 : 16192 ≤ (A^5).trace ∧ (A^5).trace ≤ 16284) : False := by
  classical
  let f := hermA.eigenvalues
  let e := conjStarAlgAut ℝ _ (star hermA.eigenvectorUnitary)
  let j (i : Fin 46) := (e J) i i
  have diagA : e A = diagonal f := by
    simpa [e,f,Function.comp_def] using hermA.conjStarAlgAut_star_eigenvectorUnitary
  have traceConj (B : Matrix (Fin 46) (Fin 46) ℝ) : (e B).trace = B.trace := by
    dsimp only [e]
    rw [conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul]
  have sumPow (k : ℕ) : ∑ i, (f i)^k = (A^k).trace := by
    rw [←traceConj (A^k),map_pow,diagA,diagonal_pow,trace_diagonal]
    simp only [Pi.pow_apply]
  have jSum : ∑ i, j i = 46 := (traceConj J).trans trJ
  have relation (i : Fin 46) : j i * f i = 7*j i := by
    have eq := congrArg e rightJ
    rw [map_mul,map_smul,diagA] at eq
    have entry := congrArg (fun B : Matrix (Fin 46) (Fin 46) ℝ => B i i) eq
    simpa only [j,mul_diagonal,Matrix.smul_apply,smul_eq_mul] using entry
  have row (i : Fin 46) : f i ^ 2 = 6 + j i - (e (D.adjMatrix ℝ)) i i := by
    have eq := congrArg e square
    rw [map_pow,map_sub,map_add,map_smul,map_one,diagA,diagonal_pow] at eq
    have entry := congrArg (fun B : Matrix (Fin 46) (Fin 46) ℝ => B i i) eq
    simpa only [j,diagonal_apply_eq,Pi.pow_apply,Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,
      Matrix.one_apply_eq,smul_eq_mul,mul_one] using entry
  have bounds (i : Fin 46) : -3 ≤ (e (D.adjMatrix ℝ)) i i ∧ (e (D.adjMatrix ℝ)) i i ≤ 3 :=
    signed_diag_bound D regD hermA.eigenvectorUnitary i
  apply eigenvalue_count_impossible f j jSum
  · intro i top
    have eq := row i
    rw [top] at eq
    linarith only [eq,(bounds i).1]
  · intro i off
    have product : j i * (f i - 7) = 0 := by linear_combination relation i
    have zero := (mul_eq_zero.mp product).resolve_right (sub_ne_zero.mpr off)
    have eq := row i
    rw [zero] at eq
    exact ⟨zero, by linarith only [eq,(bounds i).2], by linarith only [eq,(bounds i).1]⟩
  · rw [sumPow,pow_one,trA]
  · rw [sumPow,tr2]
  · rw [sumPow,tr3]
  · rw [sumPow,tr4]
  · rw [sumPow]
    exact tr5.1
  · rw [sumPow]
    exact tr5.2

end Deldor14.Star.Waddle39

/- The nonprincipal moment calculation for Zach Waddle's 46-vertex obstruction.
Source https://github.com/zach7036/c4-star-ramsey (2026). -/
namespace Deldor14.Star.Waddle39
open Matrix
theorem moment_traces (A D J : Matrix (Fin 46) (Fin 46) ℝ)
    (aa : A^2=(6:ℝ) • (1:Matrix _ _ ℝ)+J-D)
    (aj : A*J=(7:ℝ) • J) (dj : D*J=(3:ℝ) • J) (jd : J*D=(3:ℝ) • J)
    (jj : J*J=(46:ℝ) • J)
    (ta : A.trace=0) (td : D.trace=0) (tj : J.trace=46)
    (dd : (D^2).trace=138)
    (ad : (A*D).trace=46) (fifth : 0≤(A*D^2).trace ∧ (A*D^2).trace≤92) :
    (A^2).trace=322 ∧ (A^3).trace=276 ∧ (A^4).trace=4186 ∧
    16192≤(A^5).trace ∧ (A^5).trace≤16284 := by
  let I : Matrix (Fin 46) (Fin 46) ℝ := 1
  let P := (6:ℝ) • I - D
  have a2 : A^2=P+J := by rw [aa]; dsimp [P,I]; abel
  have p2 : P*P = (36:ℝ) • I - (12:ℝ) • D + D^2 := by
    dsimp only [P,I]
    simp only [sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,one_mul,mul_one,
        smul_sub,smul_smul,sq]
    module
  have pj : P*J=(3:ℝ) • J := by
    dsimp only [P,I]
    rw [sub_mul,Matrix.smul_mul,one_mul,dj]
    module
  have jp : J*P=(3:ℝ) • J := by
    dsimp only [P,I]
    rw [mul_sub,Matrix.mul_smul,mul_one,jd]
    module
  have a3 : A^3 = (6:ℝ) • A + (7:ℝ) • J - A*D := by
    rw [show A^3=A*A^2 by rw [←pow_succ'],aa,mul_sub,mul_add,Matrix.mul_smul,mul_one,aj]
  have a4 : A^4 = (36:ℝ) • I - (12:ℝ) • D + D^2 + (52:ℝ) • J := by
    rw [show A^4=A^2*A^2 by rw [←pow_add],a2,add_mul,mul_add,mul_add,p2,pj,jp,jj]
    module
  have a5 : A^5 = (36:ℝ) • A -(12:ℝ) • (A*D) + A*D^2 + (364:ℝ) • J := by
    rw [show A^5=A*A^4 by rw [←pow_succ'],a4,mul_add,mul_add,mul_sub]
    dsimp only [I]
    simp only [Matrix.mul_smul,mul_one,aj,smul_smul]
    norm_num
  have t1 : I.trace=46 := by simp [I]
  have t1' : (1:Matrix (Fin 46) (Fin 46) ℝ).trace=46 := t1
  simp only [aa,a3,a4,a5,trace_sub,trace_add,trace_smul,t1,t1',ta,td,tj,dd,ad,smul_eq_mul]
  obtain ⟨lo,hi⟩ := fifth
  norm_num at *
  constructor <;> linarith
end Deldor14.Star.Waddle39

/- Transfer the 46-vertex obstruction and certified lower-bound graph to the Ramsey number. -/
namespace Deldor14.Star.Waddle39
open Finset SimpleGraph Matrix ExcessOne OMA.ChenStar

theorem field_ones_adj {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {d : ℕ} (reg : ∀ i,G.degree i=d) :
    ones V ℝ * G.adjMatrix ℝ = (d:ℝ) • ones V ℝ := by
  ext i j
  rw [mul_adjMatrix_apply]
  simp [ones,reg]

theorem of_finite_obstruction
    (local_structure : ∀ (G : SimpleGraph (Fin 46)) [DecidableRel G.Adj],
      ¬(cycleGraph 4).IsContained G → (∀ v,G.degree v=7) →
      let A := G.adjMatrix ℝ
      let D := (Deficiency.graph G).adjMatrix ℝ
      (A*D).trace=46 ∧ 0≤(A*D^2).trace ∧ (A*D^2).trace≤92)
    (spectrum : ∀ (A J : Matrix (Fin 46) (Fin 46) ℝ) (D : SimpleGraph (Fin 46))
      [DecidableRel D.Adj], (∀ i,D.degree i=3) → A.IsHermitian →
      A^2=(6:ℝ) • (1:Matrix _ _ ℝ)+J-D.adjMatrix ℝ → J*A=(7:ℝ) • J →
      J.trace=46 → A.trace=0 → (A^2).trace=322 → (A^3).trace=276 → (A^4).trace=4186 →
      (16192≤(A^5).trace ∧ (A^5).trace≤16284) → False) : number 39=46 := by
  classical
  apply Nat.le_antisymm _ Host45.lower
  apply Nat.sInf_le
  intro G
  by_cases red : (cycleGraph 4).IsContained G
  · exact Or.inl red
  right
  by_contra nonstar
  have minimum (v) : 7≤G.degree v := by
    have l : Gᶜ.degree v<39 := lt_of_not_ge (fun ge => nonstar (star_isContained_of_le_degree Gᶜ ge))
    rw [degree_compl,Fintype.card_fin] at l
    omega
  have reg := Deficiency.regular_of_bounds G red minimum (by decide)
  let D := Deficiency.graph G
  have dr (v) : D.degree v=3 := Deficiency.degree G red (d:=7) (e:=3) (by decide) reg v
  let A := G.adjMatrix ℝ
  let B := D.adjMatrix ℝ
  let J := ones (Fin 46) ℝ
  have aa : A^2=(6:ℝ) • (1:Matrix _ _ ℝ)+J-B := by
    simpa only [Nat.cast_ofNat,show (7:ℝ)-1=6 by norm_num] using Deficiency.adj_square G red reg
  have ta := Deficiency.adj_trace G
  have tb := Deficiency.adj_trace D
  have tj : J.trace=46 := by simp [J,ones,Matrix.trace,Matrix.diag]
  have jj : J*J=(46:ℝ) • J := by ext i j; simp [J,ones,mul_apply]
  have dd : (B^2).trace=138 := by
    have ent (i : Fin 46) : (B^2) i i=3 := by
      rw [show B=D.adjMatrix ℝ by rfl,adj_square_entries D]
      simp [common,dr]
    norm_num [trace,Matrix.diag,ent]
  obtain ⟨ad,lo,hi⟩ := local_structure G red reg
  obtain ⟨m2,m3,m4,m5⟩ := moment_traces A B J aa
    (adj_ones G reg _) (adj_ones D dr _) (field_ones_adj D dr) jj ta tb tj dd ad ⟨lo,hi⟩
  exact spectrum A J D dr (by
    change Aᴴ=A
    rw [conjTranspose_eq_transpose_of_trivial]
    exact G.isSymm_adjMatrix) aa (field_ones_adj G reg) tj ta m2 m3 m4 m5

end Deldor14.Star.Waddle39

namespace Deldor14.Star.Waddle39
theorem ramsey_star_39 : Deldor14.Star.number 39=46 :=
  of_finite_obstruction (@traces_46) (@spectral_impossible)
end Deldor14.Star.Waddle39

theorem OMA.solution : OMA.R_Erdos552_erdos_552_parts_ii_R1.H1 := by
  intro p hp
  exact Deldor14.Star.prime_square hp
