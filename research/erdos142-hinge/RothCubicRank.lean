import Mathlib

open Finset
namespace Erdos142CubicRank

def localCost (D A B C AB AC BC H x y z : ℝ) : ℝ :=
  D + A*x + B*y + C*z + AB*x*y + AC*x*z + BC*y*z + H*x*y*z + x^3+y^3+z^3

theorem schur_cost {x y z : ℝ} (hx : 0 ≤ x) (xy : x ≤ y) (yz : y ≤ z) :
    2*((x+y+z)/2)^3 ≤ x^3+y^3+z^3+15/4*x*y*z := by
  have p := mul_nonneg (sq_nonneg (z-y)) (show 0 ≤ z+y-x by linarith)
  have q := mul_nonneg (mul_nonneg hx (show 0 ≤ z-x by linarith)) (sub_nonneg.mpr xy)
  nlinarith

/-- A deterministic choice among at most three mass-preserving replacements.
The comparison is uniform in every coefficient contributed by other edges. -/
theorem compress {x y z H AB AC BC : ℝ} (D A B C : ℝ)
    (hx : 0 < x) (xy : x ≤ y) (yz : y ≤ z)
    (hH : 15/4 ≤ H) (hab : 0 ≤ AB) (hac : 0 ≤ AC) (hbc : 0 ≤ BC) :
    ∃ a b c : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ a+b+c=x+y+z ∧
      (a=0 ∨ b=0 ∨ c=0) ∧
      localCost D A B C AB AC BC H a b c ≤ localCost D A B C AB AC BC H x y z := by
  let F := localCost D A B C AB AC BC H
  have hy : 0 < y := lt_of_lt_of_le hx xy
  have hz : 0 < z := lt_of_lt_of_le hy yz
  by_cases big : x+y ≤ z
  · have gap : 0 ≤ H*z - 3*(x+y) := by nlinarith [mul_nonneg (sub_nonneg.mpr hH) hz.le]
    have drop := mul_nonneg (mul_nonneg hx.le hy.le) (add_nonneg gap hab)
    have hav : x*F (x+y) 0 z + y*F 0 (x+y) z ≤ (x+y)*F x y z := by
      dsimp [F,localCost]
      nlinarith [mul_nonneg (add_nonneg hx.le hy.le) drop]
    by_cases choose : F (x+y) 0 z ≤ F x y z
    · exact ⟨x+y,0,z,by linarith,le_rfl,hz.le,by ring,Or.inr (Or.inl rfl),choose⟩
    · refine ⟨0,x+y,z,le_rfl,by linarith,hz.le,by ring,Or.inl rfl,?_⟩
      by_contra! h
      nlinarith [mul_pos hx (sub_pos.mpr (lt_of_not_ge choose)),mul_pos hy (sub_pos.mpr h)]
  · let t := (x+y+z)/2
    have ht : 0 < t := by dsimp [t]; linarith
    have tx : 0 < t-x := by dsimp [t]; linarith
    have ty : 0 < t-y := by dsimp [t]; linarith
    have tz : 0 < t-z := by dsimp [t]; linarith
    have cube : 0 ≤ x^3+y^3+z^3+H*x*y*z-2*t^3 := by
      have q := schur_cost hx.le xy yz
      dsimp [t]
      nlinarith [mul_nonneg (sub_nonneg.mpr hH) (mul_nonneg (mul_nonneg hx.le hy.le) hz.le)]
    have savings := mul_nonneg ht.le (add_nonneg (add_nonneg (add_nonneg cube
      (mul_nonneg hab (mul_nonneg tx.le ty.le))) (mul_nonneg hac (mul_nonneg tx.le tz.le)))
      (mul_nonneg hbc (mul_nonneg ty.le tz.le)))
    have hav : (t-x)*F 0 t t + (t-y)*F t 0 t + (t-z)*F t t 0 ≤ t*F x y z := by
      dsimp [F,localCost,t] at *
      linarith only [savings]
    by_cases one : F 0 t t ≤ F x y z
    · exact ⟨0,t,t,le_rfl,ht.le,ht.le,by dsimp [t]; ring,Or.inl rfl,one⟩
    by_cases two : F t 0 t ≤ F x y z
    · exact ⟨t,0,t,ht.le,le_rfl,ht.le,by dsimp [t]; ring,Or.inr (Or.inl rfl),two⟩
    refine ⟨t,t,0,ht.le,ht.le,le_rfl,by dsimp [t]; ring,Or.inr (Or.inr rfl),?_⟩
    by_contra! three
    have e : (t-x)+(t-y)+(t-z)=t := by dsimp [t]; ring
    have h := add_pos (add_pos (mul_pos tx (sub_pos.mpr (lt_of_not_ge one)))
      (mul_pos ty (sub_pos.mpr (lt_of_not_ge two)))) (mul_pos tz (sub_pos.mpr three))
    nlinarith [congrArg (fun r : ℝ => r*F x y z) e]

theorem sharp_single_edge {L : ℝ} (valid : (3:ℝ)^3 ≤ 2^2*(3+L)) : 15/4 ≤ L := by
  linarith

variable {α : Type*} [DecidableEq α]
private def poly (v : Fin 8 → ℝ) (x y z : ℝ) : ℝ :=
  v 0 + v 1*x + v 2*y + v 3*z + v 4*x*y + v 5*x*z + v 6*y*z + v 7*x*y*z

private def basis (j : Fin 8) (w : ℝ) (i : Fin 8) : ℝ := if i=j then w else 0

private def update3 (a b c : α) (w : α → ℝ) (x y z : ℝ) :=
  Function.update (Function.update (Function.update w c z) b y) a x

private theorem prod_update (S : Finset α) (v : α → ℝ) (a : α) (r : ℝ) :
    (∏ i ∈ S, Function.update v a r i) =
      (if a ∈ S then r else 1) * ∏ i ∈ S.erase a, v i := by
  have same : (∏ i ∈ S.erase a, Function.update v a r i) = ∏ i ∈ S.erase a, v i :=
    prod_congr rfl (fun i hi => Function.update_of_ne (mem_erase.mp hi).1 ..)
  by_cases h : a ∈ S
  · rw [if_pos h, ← mul_prod_erase S _ h, Function.update_self, same]
  · rw [if_neg h, erase_eq_of_notMem h, one_mul]
    apply prod_congr rfl
    intro i hi
    apply Function.update_of_ne
    intro eq
    exact h (eq ▸ hi)

private theorem edge_poly (S : Finset α) (a b c : α) (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ v : Fin 8 → ℝ, (∀ i, 0 ≤ v i) ∧ ∀ x y z,
      (∏ i ∈ S, update3 a b c w x y z i) = poly v x y z := by
  let I := S.erase a
  let K := I.erase b
  let q := ∏ i ∈ K.erase c, w i
  have hq : 0 ≤ q := prod_nonneg (fun i _ => hw i)
  let j : Fin 8 := if a ∈ S then (if b ∈ I then (if c ∈ K then 7 else 4)
    else (if c ∈ K then 5 else 1)) else (if b ∈ I then (if c ∈ K then 6 else 2)
    else (if c ∈ K then 3 else 0))
  refine ⟨basis j q, fun i => by dsimp [basis]; split <;> positivity, ?_⟩
  intro x y z
  simp only [update3, prod_update]
  change (if a ∈ S then x else 1) * ((if b ∈ I then y else 1) *
      ((if c ∈ K then z else 1)*q)) = _
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ I <;> by_cases hc : c ∈ K <;>
    simp [j,ha,hb,hc,poly,basis] <;> ring

private theorem edges_poly (E : Finset (Finset α)) (a b c : α) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) :
    ∃ v : Fin 8 → ℝ, (∀ i, 0 ≤ v i) ∧ ∀ x y z,
      (∑ e ∈ E, ∏ i ∈ e, update3 a b c w x y z i) = poly v x y z := by
  induction E using Finset.induction_on with
  | empty => exact ⟨0,by simp,by simp [poly]⟩
  | @insert e T he ih =>
    obtain ⟨v,hv,eqv⟩ := ih
    obtain ⟨u,hu,equ⟩ := edge_poly e a b c w hw
    refine ⟨u+v,fun i => add_nonneg (hu i) (hv i),?_⟩
    intro x y z
    rw [sum_insert he,equ,eqv]
    simp [poly]; ring

noncomputable def cost (V : Finset α) (E : Finset (Finset α)) (w : α → ℝ) : ℝ :=
  (∑ i ∈ V, w i ^ 3) + 15/4 * ∑ e ∈ E, ∏ i ∈ e, w i

private theorem sum_update (S : Finset α) (v : α → ℝ) (a : α) (r : ℝ)
    (g : ℝ → ℝ) (ha : a ∈ S) :
    (∑ i ∈ S, g (Function.update v a r i)) = g r + ∑ i ∈ S.erase a, g (v i) := by
  rw [← add_sum_erase S _ ha, Function.update_self]
  congr 1
  apply sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (mem_erase.mp hi).1]

private theorem sum_three (V : Finset α) (a b c : α) (ha : a ∈ V) (hb : b ∈ V)
    (hc : c ∈ V) (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c)
    (w : α → ℝ) (g : ℝ → ℝ) (x y z : ℝ) :
    (∑ i ∈ V, g (update3 a b c w x y z i)) =
      g x + (g y + (g z + ∑ i ∈ ((V.erase a).erase b).erase c, g (w i))) := by
  simp only [update3]
  rw [sum_update _ _ _ _ _ ha, sum_update _ _ _ _ _ (mem_erase.mpr ⟨ab.symm,hb⟩),
    sum_update _ _ _ _ _ (mem_erase.mpr ⟨bc.symm,mem_erase.mpr ⟨ac.symm,hc⟩⟩)]

private theorem three_step (V : Finset α) (E : Finset (Finset α)) (w : α → ℝ)
    (hw : ∀ i, 0 ≤ w i) (a b c : α) (ha : a ∈ V) (hb : b ∈ V) (hc : c ∈ V)
    (ab : a ≠ b) (ac : a ≠ c) (bc : b ≠ c) (edge : {a,b,c} ∈ E)
    (hx : 0 < w a) (xy : w a ≤ w b) (yz : w b ≤ w c) :
    ∃ u : α → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i ∈ V, u i) = (∑ i ∈ V, w i) ∧
      cost V E u ≤ cost V E w ∧ (V.filter (fun i => 0 < u i)).card <
        (V.filter (fun i => 0 < w i)).card := by
  let T : Finset α := {a,b,c}
  obtain ⟨v,hv,eqv⟩ := edges_poly (E.erase T) a b c w hw
  let F := localCost ((∑ i ∈ ((V.erase a).erase b).erase c, w i^3) + 15/4*v 0)
    (15/4*v 1) (15/4*v 2) (15/4*v 3) (15/4*v 4) (15/4*v 5) (15/4*v 6) (15/4*(v 7+1))
  have formula (x y z : ℝ) : cost V E (update3 a b c w x y z) = F x y z := by
    unfold cost
    rw [sum_three V a b c ha hb hc ab ac bc w (fun t => t^3),
      ← add_sum_erase E (fun e => ∏ i ∈ e, update3 a b c w x y z i) (show T ∈ E from edge), eqv]
    simp [T,update3,ab,ac,bc,ab.symm,ac.symm,bc.symm,F,poly,localCost]
    ring
  have original : update3 a b c w (w a) (w b) (w c) = w := by
    ext i
    by_cases h : i=a <;> by_cases k : i=b <;> by_cases m : i=c <;>
      simp_all [update3,Function.update_apply]
  obtain ⟨x,y,z,hx',hy',hz',mass,kill,hcost⟩ := compress
    ((∑ i ∈ ((V.erase a).erase b).erase c, w i^3) + 15/4*v 0)
    (15/4*v 1) (15/4*v 2) (15/4*v 3) hx xy yz
    (show 15/4 ≤ 15/4*(v 7+1) by linarith [hv 7])
    (show 0 ≤ 15/4*v 4 by linarith [hv 4]) (show 0 ≤ 15/4*v 5 by linarith [hv 5])
    (show 0 ≤ 15/4*v 6 by linarith [hv 6])
  let u := update3 a b c w x y z
  have unchanged (i : α) (h : i≠a) (k : i≠b) (m : i≠c) : u i=w i := by
    simp [u,update3,h,k,m]
  have vals : u a=x ∧ u b=y ∧ u c=z := by simp [u,update3,ab.symm,ac.symm,bc.symm]
  obtain ⟨ua,ub,uc⟩ := vals
  refine ⟨u,?_,?_,?_,?_⟩
  · intro i
    by_cases h : i=a; · simpa [h,ua] using hx'
    by_cases k : i=b; · simpa [k,ub] using hy'
    by_cases m : i=c; · simpa [m,uc] using hz'
    rw [unchanged _ h k m]; exact hw i
  · change (∑ i ∈ V, id (update3 a b c w x y z i)) = ∑ i ∈ V, w i
    conv_rhs => rw [← original]
    rw [sum_three V a b c ha hb hc ab ac bc w id]
    change _ = ∑ i ∈ V, id (update3 a b c w (w a) (w b) (w c) i)
    rw [sum_three V a b c ha hb hc ab ac bc w id]
    dsimp; linarith
  · change cost V E (update3 a b c w x y z) ≤ cost V E w
    exact (formula x y z).le.trans (hcost.trans_eq ((formula _ _ _).symm.trans (congrArg (cost V E) original)))
  · apply card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro i hi
      obtain ⟨hV,hp⟩ := mem_filter.mp hi
      apply mem_filter.mpr
      refine ⟨hV,?_⟩
      by_cases h : i=a; · simpa [h] using hx
      by_cases k : i=b; · simpa [k] using hx.trans_le xy
      by_cases m : i=c; · simpa [m] using (hx.trans_le xy).trans_le yz
      rwa [unchanged i h k m] at hp
    · intro same
      have pos : ∀ i ∈ V, 0 < w i → 0 < u i := by
        intro i hi hp
        have hmem : i ∈ V.filter (fun j => 0<u j) := same.symm ▸ (mem_filter.mpr ⟨hi,hp⟩ : i ∈ V.filter (fun j => 0<w j))
        exact (mem_filter.mp hmem).2
      rcases kill with e|e|e
      · linarith [pos a ha hx]
      · linarith [pos b hb (hx.trans_le xy)]
      · linarith [pos c hc ((hx.trans_le xy).trans_le yz)]

private theorem sort_three (e : Finset α) (w : α → ℝ) (size : e.card=3) :
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ w a ≤ w b ∧ w b ≤ w c ∧ e={a,b,c} := by
  obtain ⟨x,y,z,xy,xz,yz,rfl⟩ := card_eq_three.mp size
  by_cases h : w x ≤ w y
  · by_cases g : w y ≤ w z
    · exact ⟨x,y,z,xy,xz,yz,h,g,rfl⟩
    · by_cases j : w x ≤ w z
      · exact ⟨x,z,y,xz,xy,yz.symm,j,by linarith,by ext; simp; tauto⟩
      · exact ⟨z,x,y,xz.symm,yz.symm,xy,by linarith,h,by ext; simp; tauto⟩
  · by_cases g : w x ≤ w z
    · exact ⟨y,x,z,xy.symm,yz,xz,by linarith,g,by ext; simp; tauto⟩
    · by_cases j : w y ≤ w z
      · exact ⟨y,z,x,yz,xy.symm,xz.symm,j,by linarith,by ext; simp; tauto⟩
      · exact ⟨z,y,x,yz.symm,xz.symm,xy.symm,by linarith,by linarith,by ext; simp; tauto⟩

/-- The complete rounding theorem for any finite 3-uniform hypergraph. -/
theorem round_to_free (V : Finset α) (E : Finset (Finset α)) (h3 : ∀ e ∈ E, e.card=3)
    (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ u : α → ℝ, (∀ i, 0 ≤ u i) ∧ (∑ i ∈ V, u i)=(∑ i ∈ V, w i) ∧
      cost V E u ≤ cost V E w ∧ ∀ e ∈ E, ¬e ⊆ V.filter (fun i => 0<u i) := by
  classical
  by_cases free : ∀ e ∈ E, ¬e ⊆ V.filter (fun i => 0<w i)
  · exact ⟨w,hw,rfl,le_rfl,free⟩
  push Not at free
  obtain ⟨e,he,hs⟩ := free
  obtain ⟨a,b,c,ab,ac,bc,xy,yz,hh⟩ := sort_three e w (h3 e he)
  subst e
  have ha := mem_filter.mp (hs (show a ∈ ({a,b,c}:Finset α) by simp))
  have hb := mem_filter.mp (hs (show b ∈ ({a,b,c}:Finset α) by simp))
  have hc := mem_filter.mp (hs (show c ∈ ({a,b,c}:Finset α) by simp))
  obtain ⟨v,hv,mass,price,shorter⟩ := three_step V E w hw a b c ha.1 hb.1 hc.1 ab ac bc he ha.2 xy yz
  obtain ⟨u,hu,um,up,uf⟩ := round_to_free V E h3 v hv
  exact ⟨u,hu,um.trans mass,up.trans price,uf⟩
termination_by (V.filter (fun i => 0 < w i)).card

omit [DecidableEq α] in
private theorem cube_sum (S : Finset α) (u : α → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (∑ i ∈ S, u i)^3 ≤ (S.card:ℝ)^2*∑ i ∈ S, (u i)^3 := by
  by_cases emp : S.card=0
  · have h := card_eq_zero.mp emp
    simp [h]
  have hp : (0:ℝ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero emp
  let t := (∑ i ∈ S, u i)/(S.card:ℝ)
  have ht : 0 ≤ t := div_nonneg (sum_nonneg (fun i _ => hu i)) hp.le
  have mass : (S.card:ℝ)*t=∑ i ∈ S, u i := by dsimp [t]; field_simp
  have tang : ∑ i ∈ S, (3*t^2*u i-2*t^3) ≤ ∑ i ∈ S, (u i)^3 := by
    apply sum_le_sum
    intro i _
    nlinarith [mul_nonneg (sq_nonneg (u i-t)) (show 0 ≤ u i+2*t by linarith [hu i])]
  rw [sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, ← mass] at tang
  rw [← mass]
  nlinarith [mul_le_mul_of_nonneg_left tang (sq_nonneg (S.card:ℝ))]

/-- Direct upper certificate for the mass of every nonnegative weight vector
using any independent-set bound r for the specified graph. -/
theorem rank_inequality (V : Finset α) (E : Finset (Finset α)) (h3 : ∀ e ∈ E, e.card=3)
    (r : ℕ) (rank : ∀ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) → S.card ≤ r)
    (w : α → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i ∈ V, w i)^3 ≤ (r:ℝ)^2*cost V E w := by
  obtain ⟨u,hu,mass,fee,free⟩ := round_to_free V E h3 w hw
  let S := V.filter (fun i => 0<u i)
  have size := rank S (filter_subset _ _) free
  have sumS : (∑ i ∈ S, u i) = ∑ i ∈ V, u i := by
    apply sum_subset (filter_subset _ _)
    intro i hi h
    have h0 : ¬ 0<u i := fun hp => h (mem_filter.mpr ⟨hi,hp⟩)
    exact le_antisymm (le_of_not_gt h0) (hu i)
  have costS : (∑ i ∈ S, u i^3) ≤ cost V E u := by
    unfold cost
    have h := sum_le_sum_of_subset_of_nonneg (f:=fun i => u i^3)
      (show S ⊆ V from filter_subset _ _) (fun i _ _ => pow_nonneg (hu i) 3)
    have h0 : 0 ≤ ∑ e ∈ E, ∏ i ∈ e, u i := sum_nonneg (fun _ _ => prod_nonneg (fun i _ => hu i))
    linarith
  rw [← mass, ← sumS]
  have sz : (S.card:ℝ) ≤ r := by exact_mod_cast size
  exact (cube_sum S u hu).trans (mul_le_mul (pow_le_pow_left₀ (by positivity) sz 2)
    (costS.trans fee) (sum_nonneg (fun i _ => pow_nonneg (hu i) 3)) (by positivity))

/-- Each unordered nonconstant three-term progression is counted once. -/
noncomputable def intervalEdges (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact ((range n).powersetCard 3).filter (fun e => ¬ThreeAPFree (e : Set ℕ))

private theorem interval_free (n : ℕ) (S : Finset ℕ) (sub : S ⊆ range n) :
    (∀ e ∈ intervalEdges n, ¬e ⊆ S) ↔ ThreeAPFree (S : Set ℕ) := by
  classical
  constructor
  · intro free a ha b hb c hc h
    by_contra ne
    have ac : a ≠ c := by omega
    have bc : b ≠ c := by omega
    let e : Finset ℕ := {a,b,c}
    have es : e ⊆ S := by
      intro i hi
      simp only [e,mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl|rfl
      · exact ha
      · exact hb
      · exact hc
    have sz : e.card=3 := by simp [e,ne,ac,bc]
    have bad : ¬ ThreeAPFree (e : Set ℕ) := by
      intro hf
      exact ne (hf (a:=a) (b:=b) (c:=c) (by simp [e]) (by simp [e]) (by simp [e]) h)
    exact free e (mem_filter.mpr ⟨mem_powersetCard.mpr ⟨es.trans sub,sz⟩,bad⟩) es
  · intro hf e he es
    exact (mem_filter.mp he).2 (hf.mono es)

/-- For the actual Mathlib Roth number, the cubic program has this exact attained minimum. -/
theorem interval_minimum (n : ℕ) (hn : 0<n) :
    IsLeast {x : ℝ | ∃ w : ℕ → ℝ, (∀ i, 0≤w i) ∧
      (∑ i ∈ range n, w i)=1 ∧ x=cost (range n) (intervalEdges n) w}
      (1 / (rothNumberNat n : ℝ)^2) := by
  classical
  let r := rothNumberNat n
  obtain ⟨S,sub,hs,free⟩ := rothNumberNat_spec n
  have one : 1 ≤ r := by
    have sf : ThreeAPFree (↑({0}:Finset ℕ) : Set ℕ) := by simp
    exact sf.le_rothNumberNat _ (by simpa using hn) (by simp)
  have hr : (0:ℝ)<r := by exact_mod_cast Nat.zero_lt_of_lt one
  have sr : (S.card:ℝ)=r := by exact_mod_cast hs
  let w : ℕ → ℝ := fun i => if i ∈ S then 1/(r:ℝ) else 0
  have hw (i : ℕ) : 0≤w i := by simp only [w]; split <;> positivity
  constructor
  · refine ⟨w,hw,?_,?_⟩
    · simp only [w, sum_ite_mem, inter_eq_right.mpr sub, sum_const, nsmul_eq_mul, sr]
      field_simp
    · have zero : (∑ e ∈ intervalEdges n, ∏ i ∈ e, w i)=0 := by
        apply sum_eq_zero
        intro e he
        have h := (interval_free n S sub).mpr free e he
        obtain ⟨i,hi,ni⟩ := Finset.not_subset.mp h
        exact prod_eq_zero hi (by simp [w,ni])
      unfold cost
      rw [zero,mul_zero,add_zero]
      change 1/(r:ℝ)^2 = ∑ i ∈ range n, (if i∈S then 1/(r:ℝ) else 0)^3
      simp only [ite_pow, zero_pow (by decide : 3≠0), sum_ite_mem, inter_eq_right.mpr sub,
        sum_const, nsmul_eq_mul, sr]
      field_simp
  · rintro x ⟨v,hv,h1,rfl⟩
    have h := rank_inequality (range n) (intervalEdges n)
      (fun e he => (mem_powersetCard.mp (mem_filter.mp he).1).2) r (fun T hT hfree =>
        ((interval_free n T hT).mp hfree).le_rothNumberNat T (fun i hi => mem_range.mp (hT hi)) rfl) v hv
    rw [h1,one_pow] at h
    exact (div_le_iff₀ (sq_pos_of_pos hr)).mpr (by simpa only [mul_comm] using h)

#print axioms interval_minimum

#print axioms round_to_free
#print axioms rank_inequality

#print axioms schur_cost
#print axioms compress
#print axioms sharp_single_edge
end Erdos142CubicRank
