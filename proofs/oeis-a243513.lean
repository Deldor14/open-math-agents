import OMAStatements.S_oeis_a243513
import Mathlib

namespace Deldor14.FiveWords
open OMA.S_oeis_a243513
open scoped BigOperators

private abbrev Letter := Fin 5
private structure State where
  used : Fin 6
  pen : Option Letter
  last : Option Letter
deriving Fintype, DecidableEq

private def triple (a b : Option Letter) (x : Letter) : Prop :=
  ∀ u v : Letter, a = some u → b = some v → u ≠ v → x ≠ u ∧ x ≠ v

private instance (a b : Option Letter) (x : Letter) : Decidable (triple a b x) :=
  inferInstanceAs (Decidable (∀ u v : Letter, a = some u → b = some v → u ≠ v → x ≠ u ∧ x ≠ v))

private def allowed (s : State) (x : Letter) : Prop := x.val ≤ s.used.val ∧ triple s.pen s.last x
private instance (s : State) (x : Letter) : Decidable (allowed s x) :=
  inferInstanceAs (Decidable (_ ∧ _))
private def step (s : State) (x : Letter) : State :=
  ⟨⟨max s.used.val (x.val+1), by have := s.used.isLt; have := x.isLt; omega⟩,s.last,some x⟩
private def empty : State := ⟨0,none,none⟩

private def valid (s : State) {n : ℕ} (w : Fin n → Letter) : Prop :=
  (∀ i, (w i).val ≤ s.used.val ∨ ∃ j, j < i ∧ (w j).val + 1 = (w i).val) ∧
  (∀ i, i.val=0 → triple s.pen s.last (w i)) ∧
  (∀ i j, i.val=0 → j.val=1 → triple s.last (some (w i)) (w j)) ∧
  (∀ i j k : Fin n, j.val=i.val+1 → k.val=j.val+1 →
    triple (some (w i)) (some (w j)) (w k))

private theorem fromEmpty {n : ℕ} (w : Fin n → Letter) : valid empty w ↔ validWord w := by
  constructor
  · rintro ⟨h,_,_,t⟩
    refine ⟨fun i hi => ?_,fun i j k hij hjk hd => t i j k hij hjk _ _ rfl rfl hd⟩
    rcases h i with hi' | hi'
    · simp [empty] at hi'
      omega
    · exact hi'
  · rintro ⟨h,t⟩
    refine ⟨fun i => ?_,by simp [empty,triple],by simp [empty,triple],?_⟩
    · by_cases z : (w i).val=0
      · exact Or.inl (by simp [z,empty])
      · exact Or.inr (h i (by omega))
    · intro i j k hj hk u v hu hv hd
      cases hu
      cases hv
      exact t i j k hj hk hd

private theorem consValid {n : ℕ} (s : State) (x : Letter) (w : Fin n → Letter) :
    valid s (Fin.cons x w) ↔ allowed s x ∧ valid (step s x) w := by
  constructor
  · rintro ⟨h,f,g,t⟩
    have hx : x.val ≤ s.used.val := by
      rcases h 0 with h0 | ⟨j,hj,_⟩
      · simpa using h0
      · exact False.elim (Fin.not_lt_zero j hj)
    refine ⟨⟨hx,by simpa using f 0 rfl⟩,fun i => ?_,fun i hi => ?_,fun i j hi hj => ?_,
      fun i j k hi hj => ?_⟩
    · rcases h i.succ with ht | ⟨j,hj,he⟩
      · exact Or.inl (le_trans (by simpa using ht) (le_max_left _ _))
      · revert hj he
        refine Fin.cases ?_ (fun j => ?_) j
        · intro _ he
          simp only [Fin.cons_zero,Fin.cons_succ] at he
          exact Or.inl (he ▸ le_max_right _ _)
        · intro hj he
          exact Or.inr ⟨j,Fin.succ_lt_succ_iff.mp hj,by simpa using he⟩
    · simpa [step] using g 0 i.succ rfl (by simp [hi])
    · simpa [step] using t 0 i.succ j.succ (by simp [hi]) (by simp [hi,hj])
    · simpa using t i.succ j.succ k.succ (by simp [hi]) (by simp [hj])
  · rintro ⟨⟨hx,ht⟩,h,f,g,t⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact Or.inl (by simpa using hx)
      · rcases h i with hi | ⟨j,hj,he⟩
        · change (w i).val ≤ max s.used.val (x.val+1) at hi
          by_cases h0 : (w i).val ≤ s.used.val
          · exact Or.inl (by simpa using h0)
          · exact Or.inr ⟨0,(by exact Nat.zero_lt_succ _),by simpa using (show x.val+1=(w i).val by omega)⟩
        · exact Or.inr ⟨j.succ,Fin.succ_lt_succ_iff.mpr hj,by simpa using he⟩
    · intro i hi
      have e : i=0 := Fin.ext hi
      simpa [e] using ht
    · intro i j hi hj
      have ei : i=0 := Fin.ext hi
      subst i
      revert hj
      refine Fin.cases (by simp) (fun j hj => ?_) j
      have hj0 : j.val=0 := by simpa using hj
      simpa [step] using f j hj0
    · intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · intro j
        refine Fin.cases (by simp) (fun j => ?_) j
        intro k
        refine Fin.cases (by simp) (fun k hj hk => ?_) k
        have h0 : j.val=0 := by simpa using hj
        have h1 : k.val=1 := by simp at hk; omega
        simpa [step] using g j k h0 h1
      · intro j
        refine Fin.cases (by simp) (fun j => ?_) j
        intro k
        refine Fin.cases (by simp) (fun k hj hk => ?_) k
        exact (by simpa using t i j k (by simpa using hj) (by simpa using hk))

private noncomputable def ways (s : State) (n : ℕ) : ℕ := by
  classical
  exact ∑ w : Fin n → Letter, if valid s w then 1 else 0

private theorem initWays (s : State) : ways s 0 = 1 := by
  classical
  simp [ways, valid]

private theorem extendWays (s : State) (n : ℕ) : ways s (n+1) =
    ∑ x : Letter, if allowed s x then ways (step s x) n else 0 := by
  classical
  unfold ways
  let e := Fin.consEquiv (n:=n) (fun _ => Letter)
  rw [← e.sum_comp (fun w => if valid s w then (1:ℕ) else 0)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : allowed s x
  · simp [e,Fin.consEquiv,consValid,hx]
  · simp [e,Fin.consEquiv,consValid,hx]

private inductive Phase
  | start | zeros | two | three | many | bad
  deriving DecidableEq
open Phase

private def phase (s : State) : Phase :=
  match s.used.val, s.pen,s.last with
  | 0, none, none => start
  | 1, a, some b => if b=0 ∧ (a=none ∨ a=some 0) then zeros else bad
  | m, some a, some b =>
    if a.val < m ∧ b.val < m ∧ a ≠ b then
      if m=2 then two else if m=3 then three else many
    else bad
  | _,_,_ => bad
private def transition (s : State) (x : Letter) : Phase := if allowed s x then phase (step s x) else bad

private def row : Phase → List Phase
  | start => [zeros,bad,bad,bad,bad]
  | zeros => [zeros,two,bad,bad,bad]
  | two => [three,bad,bad,bad,bad]
  | three => [three,many,bad,bad,bad]
  | many => [many,many,many,bad,bad]
  | bad => []

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem table (m : Fin 6) (a b : Option Letter) :
    let s : State := ⟨m,a,b⟩
    phase s ≠ bad → (List.ofFn (transition s)).Perm (row (phase s)) ∧
      ∀ x, allowed s x → phase (step s x) ≠ bad := by
  revert m a b
  decide +kernel

private def paths : ℕ → Phase → ℕ
  | 0, p => if p=bad then 0 else 1
  | n+1,p => ((row p).map (paths n)).sum

private theorem pathsBad (n : ℕ) : paths n bad=0 := by
  cases n <;> rfl

private theorem interpret (s : State) (n : ℕ) (hs : phase s ≠ bad) :
    ways s n = paths n (phase s) := by
  induction n generalizing s with
  | zero => simp [initWays,paths,hs]
  | succ n ih =>
    have tbl := table s.used s.pen s.last hs
    rw [extendWays]
    calc
      _ = ∑ x : Letter, paths n (transition s x) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : allowed s x
        · simpa only [hx,if_true,transition] using ih (step s x) (tbl.2 x hx)
        · simp [hx,transition,pathsBad]
      _ = ((List.ofFn (transition s)).map (paths n)).sum := by
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      _ = paths (n+1) (phase s) := (tbl.1.map (paths n)).sum_eq

private theorem rStart (n : ℕ) : paths (n+1) start=paths n zeros := by simp [paths,row,pathsBad]
private theorem rZeros (n : ℕ) : paths (n+1) zeros=paths n zeros+paths n two := by simp [paths,row,pathsBad]
private theorem rTwo (n : ℕ) : paths (n+1) two=paths n three := by simp [paths,row,pathsBad]
private theorem rThree (n : ℕ) : paths (n+1) three=paths n three+paths n many := by simp [paths,row,pathsBad]
private theorem rMany (n : ℕ) : paths (n+1) many=3*paths n many := by simp [paths,row,pathsBad]; omega

private theorem actual (n : ℕ) : count n = paths (n+1) zeros := by
  classical
  have eq : count n = ways empty (n+2) := by
    rw [count,Nat.card_eq_fintype_card,Fintype.card_subtype,ways,Finset.sum_boole]
    congr 1
    ext w
    simp [fromEmpty]
  rw [eq,interpret empty (n+2) (by decide)]
  exact rStart (n+1)

private theorem powers (n : ℕ) : paths n many = 3^n ∧ 2 * paths n three = 3^n+1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    obtain ⟨hm,ht⟩ := ih
    rw [rMany,rThree,hm,pow_succ]
    omega

private theorem closed (n : ℕ) : 4 * count (n+1) = 7 + 3^(n+1) + 2*(n+1) := by
  rw [actual]
  induction n with
  | zero => decide
  | succ n ih =>
    have h := (powers (n+1)).2
    rw [rZeros (n+1+1),rTwo (n+1),pow_succ]
    omega

open PowerSeries
private theorem gf : series * ((1-X)^2*(1-3*X)) = X*(3-10*X+6*X^2) := by
  have left : series*((1-X)^2*(1-3*X))=
      series-(C 5*series)*X+(C 7*series)*X^2-(C 3*series)*X^3 := by simp only [map_ofNat]; ring
  have right : (X*(3-10*X+6*X^2):PowerSeries ℚ)=C 3*X-C 10*X^2+C 6*X^3 := by simp only [map_ofNat]; ring
  rw [left,right]
  apply PowerSeries.ext
  intro n
  have sh (f : PowerSeries ℚ) : coeff n (f*X)=if 1≤n then coeff (n-1) f else 0 := by
    simpa using coeff_mul_X_pow' f 1 n
  simp only [map_add,map_sub,sh,coeff_mul_X_pow',coeff_C_mul,coeff_X_pow,coeff_C,series,coeff_mk]
  have formula (j : ℕ) : 4*(count (j+1):ℚ)=7+3^(j+1)+2*((j:ℚ)+1) := by exact_mod_cast closed j
  by_cases h : n<4
  · have h₁ := formula 0
    have h₂ := formula 1
    have h₃ := formula 2
    norm_num at h₁ h₂ h₃
    interval_cases n <;> norm_num <;> linarith
  · obtain ⟨k,rfl⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
    simp [show k+4-1=k+3 by omega,show k+4-2=k+2 by omega,show k+4-3=k+1 by omega]
    have h₁ := formula k
    have h₂ := formula (k+1)
    have h₃ := formula (k+2)
    have h₄ := formula (k+3)
    push_cast at h₁ h₂ h₃ h₄
    simp only [pow_succ] at h₁ h₂ h₃ h₄
    linarith

theorem result : type_of% @OMA.S_oeis_a243513.main := by
  refine ⟨?_,gf⟩
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
  exact closed k

end Deldor14.FiveWords
theorem OMA.solution : type_of% @OMA.S_oeis_a243513.main := Deldor14.FiveWords.result
