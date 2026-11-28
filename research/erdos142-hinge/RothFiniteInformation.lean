import RothDigitCuts
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset
namespace Erdos142DigitInformation

def count {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) (y : β) : ℝ :=
  ((s.filter (fun x => f x=y)).card : ℝ)

noncomputable def fiberLog {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) : ℝ :=
  ∑ x ∈ s, Real.log (count s f (f x))

private theorem count_pos {α β : Type*} [DecidableEq β] {s : Finset α} (f : α → β)
    {x : α} (hx : x ∈ s) : 0<count s f (f x) := by
  unfold count
  have h : 0<(s.filter (fun y => f y=f x)).card := card_pos.mpr ⟨x,mem_filter.mpr ⟨hx,rfl⟩⟩
  exact_mod_cast h

private theorem total {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β) :
    ∑ y ∈ s.image f, count s f y=s.card := by
  have e := sum_comp (s:=s) (fun _ : β => (1:ℝ)) f
  simpa [count,nsmul_eq_mul] using e.symm

/-- Discrete entropy subadditivity in unnormalized fiber-log coordinates. -/
theorem subadditivity {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (s : Finset α)
    (f : α → β) (g : α → γ) :
    fiberLog s f+fiberLog s g ≤ (s.card:ℝ)*Real.log s.card+fiberLog s (fun x => (f x,g x)) := by
  classical
  by_cases empty : s=∅
  · simp [empty,fiberLog]
  have mp : (0:ℝ)<s.card := by exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
  let pair (x : α) := (f x,g x)
  let cost (p : β × γ) := count s f p.1 * count s g p.2 /
    ((s.card:ℝ)*count s pair p)
  have avg : ∑ x ∈ s, cost (pair x) ≤ s.card := calc
    _ = ∑ p ∈ s.image pair, count s pair p * cost p := by
      simpa [count,nsmul_eq_mul] using (sum_comp (s:=s) cost pair)
    _ = ∑ p ∈ s.image pair, (count s f p.1 * count s g p.2) / s.card := by
      apply sum_congr rfl
      intro p hp
      obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
      have positive := count_pos pair hx
      dsimp only [cost]
      field_simp
    _ ≤ ∑ p ∈ (s.image f) ×ˢ (s.image g), (count s f p.1 * count s g p.2) / s.card := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hp
        exact mem_product.mpr ⟨mem_image_of_mem _ hx,mem_image_of_mem _ hx⟩
      · intros
        unfold count
        positivity
    _ = s.card := by
      rw [← sum_div,sum_product]
      simp_rw [← mul_sum]
      rw [← sum_mul,total,total,mul_div_cancel_right₀ _ mp.ne']
  have term (x : α) (hx : x ∈ s) :
      Real.log (count s f (f x))+Real.log (count s g (g x))-Real.log s.card-
        Real.log (count s pair (pair x)) ≤ cost (pair x)-1 := by
    have a := count_pos f hx
    have b := count_pos g hx
    have c := count_pos pair hx
    have pos : 0<cost (pair x) := div_pos (mul_pos a b) (mul_pos mp c)
    have l := Real.log_le_sub_one_of_pos pos
    change Real.log ((count s f (f x)*count s g (g x))/(s.card*count s pair (pair x))) ≤ _ at l
    rw [Real.log_div (mul_pos a b).ne' (mul_pos mp c).ne',Real.log_mul a.ne' b.ne',
      Real.log_mul mp.ne' c.ne'] at l
    linarith
  have l := sum_le_sum term
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,mul_one] at l
  change (∑ x ∈ s, Real.log (count s f (f x)))+(∑ x ∈ s, Real.log (count s g (g x))) ≤
    (s.card:ℝ)*Real.log s.card+∑ x ∈ s, Real.log (count s pair (pair x))
  linarith

private theorem digit_rebuild (x a w : ℕ) :
    x%a+a*((x/a)%w)+(a*w)*(x/(a*w))=x := by
  rw [← Nat.div_div_eq_div_mul]
  calc
    _ = x%a+a*((x/a)%w+w*(x/a/w)) := by ring
    _ = x := by rw [Nat.mod_add_div,Nat.mod_add_div]

/-- Once the exterior digits are fixed, the middle digit values form a free set. -/
theorem outside_count (s : Finset ℕ) (free : ThreeAPFree (↑s : Set ℕ))
    {a w : ℕ} (_ha : 0<a) (hw : 0<w) (r q : ℕ) :
    count s (fun x => (x%a,x/(a*w))) (r,q) ≤ rothNumberNat w := by
  classical
  let C := s.filter (fun x => (x%a,x/(a*w))=(r,q))
  let digit (x : ℕ) := (x/a)%w
  have rebuild {x : ℕ} (hx : x ∈ C) : r+a*digit x+(a*w)*q=x := by
    obtain ⟨hr,hq⟩ := Prod.mk.inj (mem_filter.mp hx).2
    simpa only [digit,hr,hq] using digit_rebuild x a w
  have inj : Set.InjOn digit (↑C : Set ℕ) := by
    intro x hx y hy e
    rw [← rebuild hx,← rebuild hy,e]
  have fr : ThreeAPFree (↑(C.image digit) : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro u hu v hv z hz eq
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hu
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hv
    obtain ⟨b,hb,rfl⟩ := mem_image.mp hz
    have scaled := congrArg (fun l : ℕ => a*l) eq
    simp only [Nat.mul_add] at scaled
    have eq' : x+b=y+y := by linarith only [scaled,rebuild hx,rebuild hy,rebuild hb]
    exact congrArg digit (threeAPFree_iff_eq_right.mp free (mem_filter.mp hx).1
      (mem_filter.mp hy).1 (mem_filter.mp hb).1 eq')
  have bound := fr.le_rothNumberNat (C.image digit) (fun x h => by
    obtain ⟨y,_,rfl⟩ := mem_image.mp h
    exact Nat.mod_lt _ hw) rfl
  rw [card_image_of_injOn inj] at bound
  change (C.card:ℝ)≤rothNumberNat w
  exact_mod_cast bound

/-- Mutual information multiplied by the number of uniform sample points. -/
noncomputable def info (s : Finset ℕ) (a : ℕ) : ℝ :=
  s.card*Real.log s.card-fiberLog s (fun x => x%a)-fiberLog s (fun x => x/a)

theorem block_step (s : Finset ℕ) (free : ThreeAPFree (↑s : Set ℕ))
    {a w : ℕ} (ha : 0<a) (hw : 0<w) :
    fiberLog s (fun x => x%a) ≤ info s (a*w) + s.card*Real.log (rothNumberNat w) +
      fiberLog s (fun x => x%(a*w)) := by
  let f (x : ℕ) := x%a
  let g (x : ℕ) := x/(a*w)
  have sub := subadditivity s f g
  have cap : fiberLog s (fun x => (f x,g x)) ≤ s.card*Real.log (rothNumberNat w) := by
    unfold fiberLog
    have term (x : ℕ) (hx : x ∈ s) := Real.log_le_log (count_pos (fun x => (f x,g x)) hx)
      (outside_count s free ha hw (f x) (g x))
    simpa only [sum_const,nsmul_eq_mul] using sum_le_sum term
  dsimp only [f,g] at sub cap
  unfold info
  linarith

noncomputable def cutSum (s : Finset ℕ) (a : ℕ) : List ℕ → ℝ
  | [] => 0
  | w::ws => info s (a*w)+cutSum s (a*w) ws

theorem telescope (s : Finset ℕ) (free : ThreeAPFree (↑s : Set ℕ)) (ws : List ℕ)
    (pos : ∀ w ∈ ws, 0<w) (a : ℕ) (ha : 0<a) :
    fiberLog s (fun x => x%a) ≤ cutSum s a ws +
      s.card*(ws.map (fun w => Real.log (rothNumberNat w))).sum +
      fiberLog s (fun x => x%(a*ws.prod)) := by
  induction ws generalizing a with
  | nil => simp [cutSum]
  | cons w ws ih =>
    have hw := pos w (by simp)
    have h := ih (fun y hy => pos y (List.mem_cons_of_mem _ hy)) (a*w) (Nat.mul_pos ha hw)
    have loc := block_step s free ha hw
    simp only [cutSum,List.map_cons,List.sum_cons,List.prod_cons,← Nat.mul_assoc]
    linarith

private theorem mod_end (s : Finset ℕ) {n : ℕ} (fit : s ⊆ range n) :
    fiberLog s (fun x => x%n)=0 := by
  unfold fiberLog
  apply sum_eq_zero
  intro x hx
  have one : s.filter (fun y => y%n=x%n)={x} := by
    ext y
    constructor
    · intro h
      obtain ⟨hy,e⟩ := mem_filter.mp h
      rw [Nat.mod_eq_of_lt (mem_range.mp (fit hy)),Nat.mod_eq_of_lt (mem_range.mp (fit hx))] at e
      simpa using e
    · intro h
      have e := mem_singleton.mp h
      subst y
      exact mem_filter.mpr ⟨hx,rfl⟩
  simp [count,one]

private theorem log_constant {α β : Type*} [DecidableEq β] (s : Finset α) (f : α → β)
    (v : β) (h : ∀ x ∈ s, f x=v) : fiberLog s f=s.card*Real.log s.card := by
  unfold fiberLog
  have val (x : α) (hx : x ∈ s) : count s f (f x)=s.card := by
    unfold count
    rw [filter_eq_self.mpr (fun y hy => (h y hy).trans (h x hx).symm)]
  simpa only [sum_const,nsmul_eq_mul] using sum_congr rfl (fun x hx => congrArg Real.log (val x hx))

theorem endpoint (s : Finset ℕ) {n : ℕ} (fit : s ⊆ range n) : info s n=0 := by
  rw [info,mod_end _ fit,log_constant s (fun x => x/n) 0 (fun x hx => Nat.div_eq_of_lt (mem_range.mp (fit hx)))]
  ring

/-- Multicut inequality for uniform measure on any finite progression-free
    set, over arbitrary positive radices. The final cut contributes zero. -/
theorem information_multicut (s : Finset ℕ) (free : ThreeAPFree (↑s : Set ℕ)) (ws : List ℕ)
    (pos : ∀ w ∈ ws, 0<w) (fit : s ⊆ range ws.prod) :
    s.card*Real.log s.card ≤ cutSum s 1 ws + s.card*(ws.map (fun w => Real.log (rothNumberNat w))).sum := by
  have t := telescope s free ws pos 1 (by decide)
  rw [one_mul,mod_end s fit,add_zero,log_constant s (fun x => x%1) 0 (fun x _ => Nat.mod_one x)] at t
  exact t

#print axioms subadditivity
#print axioms outside_count
#print axioms endpoint
#print axioms information_multicut
end Erdos142DigitInformation
