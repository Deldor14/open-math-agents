import RothGrowth

open Finset Real
namespace Erdos142FutureRecords

noncomputable def score (n : ℕ) : ℝ := (rothNumberNat n : ℝ)/Real.sqrt n

def record (n : ℕ) := ∀ m≥n, score n ≤ score m

private theorem third {m : ℕ} (large : 13≤m/3) : 9*score (m/3) ≤ 8*score m := by
  let k := m/3
  have kp : 0<k := by dsimp [k]; omega
  have mp : 0<m := by omega
  have gl := Erdos142Growth.glue k k m kp le_rfl (by dsimp [k]; omega)
  have prod : 81*m≤256*k := by dsimp [k]; omega
  have rad : (0:ℝ)<Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast kp)
  have ram : (0:ℝ)<Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast mp)
  have dom : 9*Real.sqrt m ≤ 16*Real.sqrt k := by
    have b : (81:ℝ)*m≤256*k := by exact_mod_cast prod
    nlinarith [Real.sq_sqrt (show 0≤(m:ℝ) by positivity),
      Real.sq_sqrt (show 0≤(k:ℝ) by positivity),
      sq_nonneg (9*Real.sqrt m+16*Real.sqrt k)]
  have g : 2*(rothNumberNat k:ℝ)≤rothNumberNat m := by exact_mod_cast (show 2*rothNumberNat k≤rothNumberNat m by omega)
  change 9*((rothNumberNat k:ℝ)/Real.sqrt k) ≤ 8*((rothNumberNat m:ℝ)/Real.sqrt m)
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ rad ram]
  nlinarith only [mul_le_mul_of_nonneg_right dom (show 0≤(rothNumberNat k:ℝ) by positivity),
    mul_le_mul_of_nonneg_right g rad.le]

theorem finite_descent {n : ℕ} (hn : 13≤n) (m : ℕ) (hm : n≤m) :
    ∃ u ∈ Ico n (3*n), score u ≤ score m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases last : m<3*n
    · exact ⟨m,mem_Ico.mpr ⟨hm,last⟩,le_rfl⟩
    · have kn : n≤m/3 := by omega
      obtain ⟨u,hu,low⟩ := ih (m/3) (by omega) kn
      have d := third (hn.trans kn)
      have p : 0≤score (m/3) := by dsimp [score]; positivity
      exact ⟨u,hu,by linarith⟩

theorem finite_test (n : ℕ) (hn : 13≤n) :
    record n ↔ ∀ u ∈ Ico n (3*n), score n ≤ score u := by
  constructor
  · intro h u hu
    exact h u (mem_Ico.mp hu).1
  · intro h m hm
    obtain ⟨u,hu,low⟩ := finite_descent hn m hm
    exact (h u hu).trans low

private theorem attained (n : ℕ) (hn : 13≤n) :
    ∃ a ∈ Ico n (3*n), ∀ m≥n, score a ≤ score m := by
  have ne : (Ico n (3*n)).Nonempty := ⟨n,mem_Ico.mpr ⟨le_rfl,by omega⟩⟩
  obtain ⟨a,ha,least⟩ := exists_min_image _ score ne
  refine ⟨a,ha,?_⟩
  intro m hm
  obtain ⟨u,hu,low⟩ := finite_descent hn m hm
  exact (least u hu).trans low

private noncomputable def base (n : ℕ) := if h : 13≤n then (attained n h).choose else n
private noncomputable def envelope (n : ℕ) := score (base n)

private theorem here {n : ℕ} (h : 13≤n) :
    base n ∈ Ico n (3*n) ∧ ∀ m≥n, envelope n≤score m := by
  simpa [base,envelope,h] using (attained n h).choose_spec

private theorem rise {n : ℕ} (hn : 13≤n) : 9*envelope n ≤ 8*envelope (3*n) := by
  let a := base (3*n)
  have am := (mem_Ico.mp (here (show 13≤3*n by omega)).1).1
  have k : n≤a/3 := by dsimp [a]; omega
  have b := (here hn).2 _ k
  have c := third (hn.trans k)
  change 9*envelope n ≤ 8*score a
  linarith

private theorem initial {n : ℕ} (hn : 13≤n) :
    (rothNumberNat n:ℝ) ≤ 2*Real.sqrt n*envelope n := by
  let a := base n
  obtain ⟨na,an⟩ := mem_Ico.mp (here hn).1
  have pos : (0:ℝ)<Real.sqrt a := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<a by omega))
  have p : (0:ℝ)<Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<n by omega))
  have b : Real.sqrt a≤2*Real.sqrt n := by
    have z : (a:ℝ)≤4*n := by exact_mod_cast (show a≤4*n by omega)
    nlinarith [Real.sq_sqrt (show 0≤(a:ℝ) by positivity),Real.sq_sqrt (show 0≤(n:ℝ) by positivity)]
  have g : (rothNumberNat n:ℝ) ≤ rothNumberNat a := by exact_mod_cast rothNumberNat.monotone na
  change _ ≤ (2*Real.sqrt n)*((rothNumberNat a:ℝ)/Real.sqrt a)
  rw [← mul_div_assoc,le_div_iff₀ pos]
  nlinarith only [mul_le_mul_of_nonneg_left b (show 0≤(rothNumberNat n:ℝ) by positivity),
    mul_le_mul_of_nonneg_left g (show 0≤2*Real.sqrt n by positivity)]

private noncomputable def bump (j : ℕ) : ℕ := by
  classical
  exact if record j then 1 else 0

private theorem increment {n j : ℕ} (hn : 13≤n) (nj : n≤j) :
    Real.sqrt n*envelope (j+1) ≤ Real.sqrt n*envelope j+bump j := by
  classical
  have hj := hn.trans nj
  have eq := here hj
  have sn : (0:ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  by_cases rec : record j
  · have eqj : envelope j=score j := le_antisymm (eq.2 j le_rfl)
      (rec _ (mem_Ico.mp eq.1).1)
    rw [eqj,show bump j=1 by simp [bump,rec]]
    have lim := (here (show 13≤j+1 by omega)).2 (j+1) le_rfl
    have g := rothNumberNat_add_le j 1
    have g' : (rothNumberNat (j+1):ℝ)≤rothNumberNat j+1 := by
      exact_mod_cast (g.trans (Nat.add_le_add_left (rothNumberNat_le 1) _))
    have p : (0:ℝ)<Real.sqrt j := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<j by omega))
    have pp : (0:ℝ)<Real.sqrt (j+1:ℕ) := Real.sqrt_pos.mpr (by positivity)
    have sq : Real.sqrt (j:ℝ)≤Real.sqrt (j+1:ℕ) := Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ j)
    have small : Real.sqrt (n:ℝ)≤Real.sqrt (j:ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast nj)
    have s : score (j+1)≤score j+1/Real.sqrt j := by
      dsimp only [score]
      rw [← add_div]
      exact div_le_div₀ (by positivity) g' p sq
    have capped := mul_le_mul_of_nonneg_left (lim.trans s) sn
    have one : Real.sqrt n*(1/Real.sqrt j)≤1 := by rw [← mul_div_assoc,mul_one,div_le_one p]; exact small
    push_cast
    linarith [mul_add (Real.sqrt n) (score j) (1/Real.sqrt j)]
  · have later : j+1≤base j := by
      by_contra! f
      have same : base j=j := by have := (mem_Ico.mp eq.1).1; omega
      exact rec (by intro m hm; simpa [envelope,same] using eq.2 m hm)
    have cap := (here (show 13≤j+1 by omega)).2 (base j) later
    rw [show bump j=0 by simp [bump,rec]]
    simpa [envelope] using mul_le_mul_of_nonneg_left cap sn

/-- At least R(n)/16 distinct lengths j in [n,3n) satisfy the future
    square-root growth bound for every m >= j. The finite set uses offsets. -/
theorem record_count (n : ℕ) (hn : 13≤n) :
    ∃ S ⊆ range (2*n), rothNumberNat n≤16*S.card ∧ ∀ i ∈ S, record (n+i) := by
  classical
  let S (k : ℕ) := (range k).filter (fun i => record (n+i))
  have sum (k : ℕ) : Real.sqrt n*envelope (n+k) ≤ Real.sqrt n*envelope n+(S k).card := by
    induction k with
    | zero => simp [S]
    | succ k ih =>
      have step := increment hn (show n≤n+k by omega)
      have card : (S (k+1)).card=(S k).card+bump (n+k) := by
        simp only [S,range_add_one,filter_insert]
        by_cases h : record (n+k) <;> simp [h,bump]
      rw [card,Nat.cast_add]
      rw [Nat.add_succ]
      linarith
  have t := sum (2*n)
  rw [show n+2*n=3*n by omega] at t
  have r := mul_le_mul_of_nonneg_left (rise hn) (Real.sqrt_nonneg n)
  have i := initial hn
  refine ⟨S (2*n),filter_subset _ _,?_,fun _ h => (mem_filter.mp h).2⟩
  exact_mod_cast (show (rothNumberNat n:ℝ)≤16*(S (2*n)).card by linarith)

#print axioms finite_test
#print axioms record_count
end Erdos142FutureRecords
