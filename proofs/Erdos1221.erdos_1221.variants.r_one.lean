import FormalConjectures.ErdosProblems.«1221»

-- Problem: Erdős Problem 1221 — r one
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/1221.lean:183 (declaration Erdos1221.erdos_1221.variants.r_one)
-- Credit: @Deldor14 (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Filter Erdos1221

namespace GapBig

theorem unrolled_eq (a : ℕ → ℝ) {n k : ℕ} (m : ℕ) (hk : k < n) :
    unrolled a n (k + m * n) = sortedPoint a n ⟨k, hk⟩ + m := by
  have hn : 0 < n := by omega
  unfold unrolled
  rw [dif_pos hn]
  have h1 : (k + m * n) % n = k := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have h2 : (k + m * n) / n = m := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk, zero_add]
  have h3 : sortedPoint a n ⟨(k + m * n) % n, Nat.mod_lt _ hn⟩ = sortedPoint a n ⟨k, hk⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]

theorem unrolled_eq' (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n j = sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ + ((j / n : ℕ) : ℝ) := by
  unfold unrolled
  rw [dif_pos hn]

theorem unrolled_add (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n (j + n) = unrolled a n j + 1 := by
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have h1 : (j + n) % n = j % n := Nat.add_mod_right j n
  have h2 : (j + n) / n = j / n + 1 := Nat.add_div_right j hn
  have h3 : sortedPoint a n ⟨(j + n) % n, Nat.mod_lt _ hn⟩ =
      sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]; push_cast; ring

theorem sum_shift_telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) (c : G) (n : ℕ)
    (hf : ∀ j, f (j + n) = f j + c) (r : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + r) - f i) = r • c := by
  induction r with
  | zero => simp
  | succ k ih =>
    have e : ∑ i ∈ Finset.range n, (f (i + (k + 1)) - f i) =
        ∑ i ∈ Finset.range n, (f (i + k) - f i) +
          ∑ i ∈ Finset.range n, ((fun i => f (i + k)) (i + 1) - (fun i => f (i + k)) i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only
      rw [show i + 1 + k = i + (k + 1) by omega]
      abel
    rw [e, ih, Finset.sum_range_sub (fun i => f (i + k))]
    simp only [zero_add]
    rw [show n + k = k + n by omega, hf, succ_nsmul]
    abel

theorem sum_rSpan (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∑ i ∈ Finset.range n, rSpan a n r i = r := by
  unfold rSpan
  rw [sum_shift_telescope (unrolled a n) 1 n (unrolled_add a hn) r]
  simp

theorem sortedPoint_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    (n : ℕ) : StrictMono (sortedPoint a n) := by
  apply Monotone.strictMono_of_injective (Tuple.monotone_sort (pts a n))
  intro x y hxy
  have h : pts a n (Tuple.sort (pts a n) x) = pts a n (Tuple.sort (pts a n) y) := hxy
  have h2 := ha h
  have h3 : Tuple.sort (pts a n) x = Tuple.sort (pts a n) y := Fin.ext h2
  exact (Tuple.sort (pts a n)).injective h3

theorem sortedPoint_mem (a : ℕ → ℝ) (n : ℕ) (k : Fin n) :
    0 ≤ sortedPoint a n k ∧ sortedPoint a n k < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem unrolled_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) : StrictMono (unrolled a n) := by
  intro j j' hjj
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have hq : j / n ≤ j' / n := Nat.div_le_div_right hjj.le
  rcases hq.lt_or_eq with hlt | heq
  · have h1 := (sortedPoint_mem a n ⟨j % n, Nat.mod_lt _ hn⟩).2
    have h2 := (sortedPoint_mem a n ⟨j' % n, Nat.mod_lt _ hn⟩).1
    have h3 : ((j / n : ℕ) : ℝ) + 1 ≤ ((j' / n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  · have hm : j % n < j' % n := by
      have e1 := Nat.div_add_mod j n
      have e2 := Nat.div_add_mod j' n
      rw [heq] at e1
      omega
    have := sortedPoint_strictMono a ha n (show (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) < ⟨j' % n, Nat.mod_lt _ hn⟩ from hm)
    rw [heq]
    linarith

/-- forward range description -/
theorem unrolled_mem (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∃ t < n, ∃ m : ℕ, unrolled a n j = Int.fract (a t) + m := by
  rw [unrolled_eq' a hn]
  refine ⟨(Tuple.sort (pts a n) ⟨j % n, Nat.mod_lt _ hn⟩ : ℕ), Fin.is_lt _, j / n, rfl⟩

/-- backward range description -/
theorem mem_unrolled (a : ℕ → ℝ) {n t : ℕ} (ht : t < n) (m : ℕ) :
    ∃ j, unrolled a n j = Int.fract (a t) + m := by
  set k := (Tuple.sort (pts a n)).symm ⟨t, ht⟩ with hk
  refine ⟨k + m * n, ?_⟩
  rw [unrolled_eq a m k.is_lt]
  congr 1
  show pts a n (Tuple.sort (pts a n) ⟨k, k.is_lt⟩) = _
  have : (⟨(k : ℕ), k.is_lt⟩ : Fin n) = k := rfl
  rw [this, hk, Equiv.apply_symm_apply]
  rfl

theorem span_transfer {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {i i' r : ℕ} (hii : v i' = u i)
    (hin : ∀ k, u i < v k → v k < u (i + r) → ∃ j, u j = v k) :
    v (i' + r) = u (i + r) := by
  obtain ⟨i'', hi''⟩ := hsub (i + r)
  have hle : i' ≤ i'' := by
    rw [← hv.le_iff_le, hii, hi'']; exact hu.monotone (by omega)
  have key : (Finset.Icc i' i'').image v = (Finset.Icc i (i + r)).image u := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨k, ⟨hk1, hk2⟩, rfl⟩
      have l1 : u i ≤ v k := hii ▸ hv.monotone hk1
      have l2 : v k ≤ u (i + r) := hi'' ▸ hv.monotone hk2
      obtain ⟨j, hj⟩ : ∃ j, u j = v k := by
        rcases l1.lt_or_eq with l1 | l1
        · rcases l2.lt_or_eq with l2 | l2
          · exact hin k l1 l2
          · exact ⟨_, l2.symm⟩
        · exact ⟨_, l1⟩
      refine ⟨j, ⟨?_, ?_⟩, hj⟩
      · rw [← hu.le_iff_le, hj]; exact l1
      · rw [← hu.le_iff_le, hj]; exact l2
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      obtain ⟨k, hk⟩ := hsub j
      refine ⟨k, ⟨?_, ?_⟩, hk⟩
      · rw [← hv.le_iff_le, hk, hii]; exact hu.monotone hj1
      · rw [← hv.le_iff_le, hk, hi'']; exact hu.monotone hj2
  have hc := congrArg Finset.card key
  rw [Finset.card_image_of_injective _ hv.injective,
    Finset.card_image_of_injective _ hu.injective] at hc
  simp only [Nat.card_Icc] at hc
  have : i'' = i' + r := by omega
  rw [this] at hi''; exact hi''

/-- A new point `t` lies strictly inside the `r`-arc of index `i` at time `n`. -/
def Inside (a : ℕ → ℝ) (n r i t : ℕ) : Prop :=
  ∃ m : ℤ, unrolled a n i < Int.fract (a t) + m ∧ Int.fract (a t) + m < unrolled a n (i + r)

theorem card_inside_le (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) (r t : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range n)
    (hin : ∀ i ∈ S, Inside a n r i t) : S.card ≤ r := by
  set z := Int.fract (a t)
  set f : ℕ → ℤ := fun j => ⌈unrolled a n j - z⌉ with hf
  have hper : ∀ j, f (j + n) = f j + 1 := by
    intro j
    simp only [hf]
    rw [unrolled_add a hn, show unrolled a n j + 1 - z = (unrolled a n j - z) + 1 by ring,
      Int.ceil_add_one]
  have htel := sum_shift_telescope f 1 n hper r
  have hmono : StrictMono (unrolled a n) := unrolled_strictMono a ha hn
  have hnn : ∀ i, 0 ≤ f (i + r) - f i := by
    intro i
    have : f i ≤ f (i + r) := by
      simp only [hf]
      apply Int.ceil_mono
      have := hmono.monotone (show i ≤ i + r by omega)
      linarith
    omega
  have h1 : ∀ i ∈ S, (1 : ℤ) ≤ f (i + r) - f i := by
    intro i hi
    obtain ⟨m, hm1, hm2⟩ := hin i hi
    have e1 : f i ≤ m := by
      simp only [hf]; rw [Int.ceil_le]; linarith
    have e2 : m < f (i + r) := by
      simp only [hf]; rw [Int.lt_ceil]; linarith
    omega
  have : (S.card : ℤ) ≤ r := by
    calc (S.card : ℤ) = ∑ i ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ S, (f (i + r) - f i) := Finset.sum_le_sum h1
      _ ≤ ∑ i ∈ Finset.range n, (f (i + r) - f i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => hnn i)
      _ = r := by rw [htel]; simp
  exact_mod_cast this

theorem unrolled_add_mul (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    unrolled a n (j + m * n) = unrolled a n j + m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) * n = (j + k * n) + n by ring, unrolled_add a hn, ih]
    push_cast; ring

theorem rSpan_le_maxSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i ≤ maxSpan a N r := by
  have e : rSpan a N r i = rSpan a N r (i % N) := by
    unfold rSpan
    have hi : i = i % N + (i / N) * N := by
      have := Nat.mod_add_div i N; rw [mul_comm] at this; omega
    conv_lhs => rw [hi, show i % N + i / N * N + r = (i % N + r) + i / N * N by ring]
    rw [unrolled_add_mul a hN, unrolled_add_mul a hN]
    ring
  rw [e]
  unfold maxSpan
  exact le_ciSup (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddAbove (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem survive (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n N r i : ℕ} (hn : 0 < n) (hnN : n ≤ N)
    (hno : ∀ t, n ≤ t → t < N → ¬ Inside a n r i t) :
    rSpan a n r i ≤ maxSpan a N r := by
  have hN : 0 < N := by omega
  have hu := unrolled_strictMono a ha hn
  have hv := unrolled_strictMono a ha hN
  have hsub : ∀ j, ∃ k, unrolled a N k = unrolled a n j := by
    intro j
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn j
    obtain ⟨k, hk⟩ := mem_unrolled a (show t < N by omega) m
    exact ⟨k, by rw [hk, hm]⟩
  obtain ⟨i', hi'⟩ := hsub i
  have hin : ∀ k, unrolled a n i < unrolled a N k → unrolled a N k < unrolled a n (i + r) →
      ∃ j, unrolled a n j = unrolled a N k := by
    intro k h1 h2
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hN k
    by_cases htn : t < n
    · obtain ⟨j, hj⟩ := mem_unrolled a htn m
      exact ⟨j, by rw [hj, hm]⟩
    · exfalso
      apply hno t (by omega) ht
      refine ⟨(m : ℤ), ?_, ?_⟩
      · push_cast; rw [← hm]; exact h1
      · push_cast; rw [← hm]; exact h2
  have key := span_transfer hu hv hsub hi' hin
  have : rSpan a n r i = rSpan a N r i' := by
    unfold rSpan; rw [key, hi']
  rw [this]
  exact rSpan_le_maxSpan a hN r i'

theorem rearrange (h : ℕ → ℝ) (hh : Antitone h) (r : ℕ) (s : ℕ → ℕ) :
    ∀ (S : Finset ℕ), (∀ k, (S.filter (fun i => s i < k)).card ≤ r * k) →
      ∑ i ∈ S, h (s i) ≤ ∑ j ∈ Finset.range S.card, h (j / r) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image s hne
    have h4 : 0 < S.card := Finset.card_pos.mpr hne
    have hq : (S.card - 1) / r ≤ s i0 := by
      by_contra hlt
      push Not at hlt
      have h1 := hS ((S.card - 1) / r)
      have h2 : S.filter (fun i => s i < (S.card - 1) / r) = S := by
        apply Finset.filter_true_of_mem
        intro i hi; exact lt_of_le_of_lt (hmax i hi) hlt
      rw [h2] at h1
      have h3 : r * ((S.card - 1) / r) ≤ S.card - 1 := Nat.mul_div_le _ _
      omega
    have hsub : S.erase i0 ⊂ S := Finset.erase_ssubset hi0
    have ih' := ih _ hsub (fun k => le_trans (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.erase_subset _ _))) (hS k))
    rw [Finset.card_erase_of_mem hi0] at ih'
    rw [← Finset.add_sum_erase S _ hi0]
    have hc : S.card = (S.card - 1) + 1 := by omega
    rw [hc, Finset.sum_range_succ]
    have := hh hq
    linarith

theorem one_div_le_log_sub {x : ℝ} (hx : 1 < x) : 1 / x ≤ Real.log x - Real.log (x - 1) := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (show 0 < (x - 1) / x by apply div_pos <;> linarith)
  rw [Real.log_div (by linarith) hx0.ne'] at h
  have : (x - 1) / x - 1 = -(1 / x) := by rw [sub_div, div_self hx0.ne']; ring
  linarith

theorem harmonic_bound {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    ∑ j ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) ≤
      r * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1)) := by
  set B : ℝ := (r : ℝ) * ((n : ℝ) - 1) with hB
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hB0 : 0 < B := by rw [hB]; apply mul_pos <;> linarith
  have step1 : ∀ j ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) ≤
      r * ((fun j : ℕ => Real.log (B + j)) (j + 1) - (fun j : ℕ => Real.log (B + j)) j) := by
    intro j _
    simp only
    push_cast
    have hj : j + 1 ≤ r * (j / r) + r := by
      have := Nat.div_add_mod j r; have := Nat.mod_lt j (show 0 < r by omega); omega
    have hj' : (j : ℝ) + 1 ≤ r * ((j / r : ℕ) : ℝ) + r := by exact_mod_cast hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hq0 : (0 : ℝ) ≤ ((j / r : ℕ) : ℝ) := Nat.cast_nonneg _
    have hpos : 0 < (n : ℝ) + ((j / r : ℕ) : ℝ) := by linarith
    have hx : 1 < B + ((j : ℝ) + 1) := by linarith
    have h2 := one_div_le_log_sub hx
    rw [show B + ((j : ℝ) + 1) - 1 = B + j by ring] at h2
    have h3 : (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) ≤ r * (1 / (B + ((j : ℝ) + 1))) := by
      rw [mul_one_div, div_le_div_iff₀ hpos (by linarith)]
      rw [hB]; nlinarith
    calc _ ≤ r * (1 / (B + ((j : ℝ) + 1))) := h3
      _ ≤ _ := by apply mul_le_mul_of_nonneg_left h2; linarith
  have hsum := Finset.sum_range_sub (fun j : ℕ => Real.log (B + j)) n
  simp only [Nat.cast_zero, add_zero] at hsum
  have hn1 : (n : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hr0 : (r : ℝ) ≠ 0 := by intro h; linarith
  have hR : (1 + 1 / ((n : ℝ) - 1)) * (B * (1 + 1 / (r : ℝ))) = n * (r + 1) := by
    rw [hB]; field_simp; ring
  have hy0 : 0 < (B + n) / (B * (1 + 1 / (r : ℝ))) := by
    apply div_pos (by linarith); apply mul_pos hB0; positivity
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [Real.log_div (by linarith) (by positivity), Real.log_mul hB0.ne' (by positivity)] at hlog
  have hy1 : (B + n) / (B * (1 + 1 / (r : ℝ))) ≤ 1 + 1 / ((n : ℝ) - 1) := by
    rw [div_le_iff₀ (by positivity), hR, hB]; nlinarith
  calc _ ≤ ∑ j ∈ Finset.range n,
        r * ((fun j : ℕ => Real.log (B + j)) (j + 1) - (fun j : ℕ => Real.log (B + j)) j) :=
        Finset.sum_le_sum step1
    _ = r * (Real.log (B + n) - Real.log B) := by rw [← Finset.mul_sum, hsum]
    _ ≤ _ := by apply mul_le_mul_of_nonneg_left _ (by linarith); linarith

theorem main (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k)) {r : ℕ} (hr : 1 ≤ r)
    {L : ℝ} (hL : 0 < L) {n0 : ℕ} (hM : ∀ N, n0 ≤ N → (N : ℝ) * maxSpan a N r < L)
    {n : ℕ} (hn : 2 ≤ n) (hn0 : n0 ≤ n) :
    1 ≤ L * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1)) := by
  classical
  have hn1 : 0 < n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  let P : ℕ → ℕ → Prop := fun i s => ∀ t, n ≤ t → t < n + s → ¬ Inside a n r i t
  let s : ℕ → ℕ := fun i => Nat.findGreatest (P i) n
  have hP : ∀ i, P i (s i) := fun i =>
    Nat.findGreatest_spec (Nat.zero_le n) (fun t h1 h2 => absurd h2 (by omega))
  have hlen : ∀ i, rSpan a n r i ≤ L / ((n : ℝ) + (s i : ℝ)) := by
    intro i
    have h1 := survive a ha hn1 (show n ≤ n + s i by omega) (hP i)
    have h2 := hM (n + s i) (by omega)
    push_cast at h2
    have hpos : (0 : ℝ) < (n : ℝ) + (s i : ℝ) :=
      add_pos_of_pos_of_nonneg hnpos (Nat.cast_nonneg _)
    rw [le_div_iff₀ hpos]
    calc rSpan a n r i * ((n : ℝ) + (s i : ℝ)) ≤ maxSpan a (n + s i) r * ((n : ℝ) + (s i : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 hpos.le
      _ = ((n : ℝ) + (s i : ℝ)) * maxSpan a (n + s i) r := mul_comm _ _
      _ ≤ L := h2.le
  have hcount : ∀ k, ((Finset.range n).filter (fun i => s i < k)).card ≤ r * k := by
    intro k
    by_cases hk : n < k
    · calc _ ≤ (Finset.range n).card := Finset.card_filter_le _ _
        _ = n := Finset.card_range n
        _ ≤ r * k := by nlinarith
    · push Not at hk
      have hsub : (Finset.range n).filter (fun i => s i < k) ⊆
          (Finset.range k).biUnion
            (fun d => (Finset.range n).filter (fun i => Inside a n r i (n + d))) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        refine ⟨s i, hi.2, hi.1, ?_⟩
        have hnot := Nat.findGreatest_is_greatest (P := P i)
          (show s i < s i + 1 by omega) (show s i + 1 ≤ n by omega)
        by_contra hcon
        apply hnot
        intro t ht1 ht2
        by_cases htt : t < n + s i
        · exact hP i t ht1 htt
        · have : t = n + s i := by omega
          rw [this]; exact hcon
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ d ∈ Finset.range k,
            ((Finset.range n).filter (fun i => Inside a n r i (n + d))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.range k, r := Finset.sum_le_sum (fun d _ =>
            card_inside_le a ha hn1 r (n + d) _ (Finset.filter_subset _ _)
              (fun i hi => (Finset.mem_filter.mp hi).2))
        _ = r * k := by simp [mul_comm]
  have hsum := sum_rSpan a hn1 r
  have hh : Antitone (fun k : ℕ => L / ((n : ℝ) + k)) := by
    intro x y hxy
    apply div_le_div_of_nonneg_left hL.le (add_pos_of_pos_of_nonneg hnpos (Nat.cast_nonneg _))
    simp only [add_le_add_iff_left, Nat.cast_le]; exact hxy
  have hre := rearrange _ hh r s (Finset.range n) hcount
  rw [Finset.card_range] at hre
  have hhar := harmonic_bound hn hr
  have e : ∑ j ∈ Finset.range n, L / ((n : ℝ) + ((j / r : ℕ) : ℝ)) =
      L * ∑ j ∈ Finset.range n, (1 : ℝ) / ((n : ℝ) + ((j / r : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_one_div]
  have h1 : (r : ℝ) ≤ ∑ i ∈ Finset.range n, L / ((n : ℝ) + (s i : ℝ)) := by
    rw [← hsum]; apply Finset.sum_le_sum; intro i _; exact hlen i
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h2 : (r : ℝ) ≤ L * (r * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) := by
    calc (r : ℝ) ≤ _ := h1
      _ ≤ _ := hre
      _ = _ := e
      _ ≤ _ := mul_le_mul_of_nonneg_left hhar hL.le
  have h3 : (r : ℝ) * 1 ≤ r * (L * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) := by
    linarith [show L * (r * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) =
      r * (L * (Real.log (1 + 1 / (r : ℝ)) + 1 / ((n : ℝ) - 1))) by ring]
  exact le_of_mul_le_mul_left h3 hr'

end GapBig

lemma big_ge (r : ℕ) (hr : 1 ≤ r) :
    ENNReal.ofReal (1 / Real.log (1 + 1 / (r : ℝ))) ≤ bigLambda r := by
  unfold bigLambda
  apply le_iInf₂
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1, hx2⟩ := exists_between hcon
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  set L := x.toReal
  have hxL : x = ENNReal.ofReal L := (ENNReal.ofReal_toReal hxtop).symm
  rw [hxL] at hx1 hx2
  have hL : 0 < L := by
    have := lt_of_le_of_lt zero_le hx1
    exact ENNReal.ofReal_pos.mp this
  have hLc : L < 1 / Real.log (1 + 1 / (r : ℝ)) := (ENNReal.ofReal_lt_ofReal_iff'.mp hx2).1
  have hev := Filter.eventually_lt_of_limsup_lt hx1
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  have hM : ∀ N, n0 ≤ N → (N : ℝ) * maxSpan a N r < L := fun N hN =>
    (ENNReal.ofReal_lt_ofReal_iff hL).mp (hn0 N hN)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogpos : 0 < Real.log (1 + 1 / (r : ℝ)) := by
    apply Real.log_pos; have := one_div_pos.mpr hr0; linarith
  have hgap : 0 < 1 - L * Real.log (1 + 1 / (r : ℝ)) := by
    rw [lt_div_iff₀ hlogpos] at hLc; linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (L / (1 - L * Real.log (1 + 1 / (r : ℝ))))
  obtain ⟨n, hn⟩ : ∃ n, n = max (max n0 2) (m + 2) := ⟨_, rfl⟩
  have hn2 : 2 ≤ n := by omega
  have hnn0 : n0 ≤ n := by omega
  have hnm : m + 2 ≤ n := by omega
  have key := GapBig.main a ha hr hL hM hn2 hnn0
  have hn1 : (m : ℝ) + 1 ≤ (n : ℝ) - 1 := by
    have : ((m + 2 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    rw [Nat.cast_add] at this
    norm_num at this
    linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have h5 : L * (1 / ((n : ℝ) - 1)) <
      1 - L * Real.log (1 + 1 / (r : ℝ)) := by
    rw [mul_one_div, div_lt_iff₀ hpos]
    rw [div_lt_iff₀ hgap] at hm
    nlinarith [mul_le_mul_of_nonneg_left hn1 hgap.le]
  rw [mul_add] at key
  linarith

open Filter Erdos1221

namespace GapSmall

theorem unrolled_eq (a : ℕ → ℝ) {n k : ℕ} (m : ℕ) (hk : k < n) :
    unrolled a n (k + m * n) = sortedPoint a n ⟨k, hk⟩ + m := by
  have hn : 0 < n := by omega
  unfold unrolled
  rw [dif_pos hn]
  have h1 : (k + m * n) % n = k := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have h2 : (k + m * n) / n = m := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk, zero_add]
  have h3 : sortedPoint a n ⟨(k + m * n) % n, Nat.mod_lt _ hn⟩ = sortedPoint a n ⟨k, hk⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]

theorem unrolled_eq' (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n j = sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ + ((j / n : ℕ) : ℝ) := by
  unfold unrolled
  rw [dif_pos hn]

theorem unrolled_add (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n (j + n) = unrolled a n j + 1 := by
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have h1 : (j + n) % n = j % n := Nat.add_mod_right j n
  have h2 : (j + n) / n = j / n + 1 := Nat.add_div_right j hn
  have h3 : sortedPoint a n ⟨(j + n) % n, Nat.mod_lt _ hn⟩ =
      sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]; push_cast; ring

theorem sum_shift_telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) (c : G) (n : ℕ)
    (hf : ∀ j, f (j + n) = f j + c) (r : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + r) - f i) = r • c := by
  induction r with
  | zero => simp
  | succ k ih =>
    have e : ∑ i ∈ Finset.range n, (f (i + (k + 1)) - f i) =
        ∑ i ∈ Finset.range n, (f (i + k) - f i) +
          ∑ i ∈ Finset.range n, ((fun i => f (i + k)) (i + 1) - (fun i => f (i + k)) i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only
      rw [show i + 1 + k = i + (k + 1) by omega]
      abel
    rw [e, ih, Finset.sum_range_sub (fun i => f (i + k))]
    simp only [zero_add]
    rw [show n + k = k + n by omega, hf, succ_nsmul]
    abel

theorem sum_rSpan (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∑ i ∈ Finset.range n, rSpan a n r i = r := by
  unfold rSpan
  rw [sum_shift_telescope (unrolled a n) 1 n (unrolled_add a hn) r]
  simp

theorem sortedPoint_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    (n : ℕ) : StrictMono (sortedPoint a n) := by
  apply Monotone.strictMono_of_injective (Tuple.monotone_sort (pts a n))
  intro x y hxy
  have h : pts a n (Tuple.sort (pts a n) x) = pts a n (Tuple.sort (pts a n) y) := hxy
  have h2 := ha h
  have h3 : Tuple.sort (pts a n) x = Tuple.sort (pts a n) y := Fin.ext h2
  exact (Tuple.sort (pts a n)).injective h3

theorem sortedPoint_mem (a : ℕ → ℝ) (n : ℕ) (k : Fin n) :
    0 ≤ sortedPoint a n k ∧ sortedPoint a n k < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem unrolled_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) : StrictMono (unrolled a n) := by
  intro j j' hjj
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have hq : j / n ≤ j' / n := Nat.div_le_div_right hjj.le
  rcases hq.lt_or_eq with hlt | heq
  · have h1 := (sortedPoint_mem a n ⟨j % n, Nat.mod_lt _ hn⟩).2
    have h2 := (sortedPoint_mem a n ⟨j' % n, Nat.mod_lt _ hn⟩).1
    have h3 : ((j / n : ℕ) : ℝ) + 1 ≤ ((j' / n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  · have hm : j % n < j' % n := by
      have e1 := Nat.div_add_mod j n
      have e2 := Nat.div_add_mod j' n
      rw [heq] at e1
      omega
    have := sortedPoint_strictMono a ha n (show (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) < ⟨j' % n, Nat.mod_lt _ hn⟩ from hm)
    rw [heq]
    linarith

/-- forward range description -/
theorem unrolled_mem (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∃ t < n, ∃ m : ℕ, unrolled a n j = Int.fract (a t) + m := by
  rw [unrolled_eq' a hn]
  refine ⟨(Tuple.sort (pts a n) ⟨j % n, Nat.mod_lt _ hn⟩ : ℕ), Fin.is_lt _, j / n, rfl⟩

/-- backward range description -/
theorem mem_unrolled (a : ℕ → ℝ) {n t : ℕ} (ht : t < n) (m : ℕ) :
    ∃ j, unrolled a n j = Int.fract (a t) + m := by
  set k := (Tuple.sort (pts a n)).symm ⟨t, ht⟩ with hk
  refine ⟨k + m * n, ?_⟩
  rw [unrolled_eq a m k.is_lt]
  congr 1
  show pts a n (Tuple.sort (pts a n) ⟨k, k.is_lt⟩) = _
  have : (⟨(k : ℕ), k.is_lt⟩ : Fin n) = k := rfl
  rw [this, hk, Equiv.apply_symm_apply]
  rfl

theorem unrolled_add_mul (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    unrolled a n (j + m * n) = unrolled a n j + m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) * n = (j + k * n) + n by ring, unrolled_add a hn, ih]
    push_cast; ring

theorem rearrange (h : ℕ → ℝ) (hh : Antitone h) (r : ℕ) (s : ℕ → ℕ) :
    ∀ (S : Finset ℕ), (∀ k, (S.filter (fun i => s i < k)).card ≤ r * k) →
      ∑ i ∈ S, h (s i) ≤ ∑ j ∈ Finset.range S.card, h (j / r) := by
  intro S
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hS
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨i0, hi0, hmax⟩ := S.exists_max_image s hne
    have h4 : 0 < S.card := Finset.card_pos.mpr hne
    have hq : (S.card - 1) / r ≤ s i0 := by
      by_contra hlt
      push Not at hlt
      have h1 := hS ((S.card - 1) / r)
      have h2 : S.filter (fun i => s i < (S.card - 1) / r) = S := by
        apply Finset.filter_true_of_mem
        intro i hi; exact lt_of_le_of_lt (hmax i hi) hlt
      rw [h2] at h1
      have h3 : r * ((S.card - 1) / r) ≤ S.card - 1 := Nat.mul_div_le _ _
      omega
    have hsub : S.erase i0 ⊂ S := Finset.erase_ssubset hi0
    have ih' := ih _ hsub (fun k => le_trans (Finset.card_le_card
      (Finset.filter_subset_filter _ (Finset.erase_subset _ _))) (hS k))
    rw [Finset.card_erase_of_mem hi0] at ih'
    rw [← Finset.add_sum_erase S _ hi0]
    have hc : S.card = (S.card - 1) + 1 := by omega
    rw [hc, Finset.sum_range_succ]
    have := hh hq
    linarith


theorem card_ho_le (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) (R : ℕ) (z : ℝ) (S : Finset ℕ) (hS : S ⊆ Finset.range n)
    (hin : ∀ i ∈ S, ∃ m : ℤ, unrolled a n i ≤ z + m ∧ z + m < unrolled a n (i + R)) :
    S.card ≤ R := by
  set f : ℕ → ℤ := fun j => ⌈unrolled a n j - z⌉ with hf
  have hper : ∀ j, f (j + n) = f j + 1 := by
    intro j
    simp only [hf]
    rw [unrolled_add a hn, show unrolled a n j + 1 - z = (unrolled a n j - z) + 1 by ring,
      Int.ceil_add_one]
  have htel := sum_shift_telescope f 1 n hper R
  have hmono : StrictMono (unrolled a n) := unrolled_strictMono a ha hn
  have hnn : ∀ i, 0 ≤ f (i + R) - f i := by
    intro i
    have : f i ≤ f (i + R) := by
      simp only [hf]
      apply Int.ceil_mono
      have := hmono.monotone (show i ≤ i + R by omega)
      linarith
    omega
  have h1 : ∀ i ∈ S, (1 : ℤ) ≤ f (i + R) - f i := by
    intro i hi
    obtain ⟨m, hm1, hm2⟩ := hin i hi
    have e1 : f i ≤ m := by
      simp only [hf]; rw [Int.ceil_le]; linarith
    have e2 : m < f (i + R) := by
      simp only [hf]; rw [Int.lt_ceil]; linarith
    omega
  have : (S.card : ℤ) ≤ R := by
    calc (S.card : ℤ) = ∑ i ∈ S, (1 : ℤ) := by simp
      _ ≤ ∑ i ∈ S, (f (i + R) - f i) := Finset.sum_le_sum h1
      _ ≤ ∑ i ∈ Finset.range n, (f (i + R) - f i) :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun i _ _ => hnn i)
      _ = R := by rw [htel]; simp
  exact_mod_cast this

theorem lift {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {A j0 : ℕ} (h0 : v A = u j0) (w : ℕ)
    (hw : ∀ k, A < k → k ≤ A + w → ∃ j, u j = v k) : v (A + w) = u (j0 + w) := by
  induction w with
  | zero => simpa using h0
  | succ w ih =>
    have ih' := ih (fun k h1 h2 => hw k h1 (by omega))
    obtain ⟨j, hj⟩ := hw (A + (w + 1)) (by omega) le_rfl
    obtain ⟨k', hk'⟩ := hsub (j0 + (w + 1))
    have h1 : j0 + w < j := by
      rw [← hu.lt_iff_lt, hj, ← ih']; exact hv (by omega)
    have h2 : A + w < k' := by
      rw [← hv.lt_iff_lt, hk', ih']; exact hu (by omega)
    have h3 : j ≤ j0 + (w + 1) := by
      rw [← hu.le_iff_le, hj, ← hk']; exact hv.monotone (by omega)
    have : j = j0 + (w + 1) := by omega
    rw [← hj, this]

theorem rSpan_mod (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i = rSpan a N r (i % N) := by
  unfold rSpan
  have hi : i = i % N + (i / N) * N := by
    have := Nat.mod_add_div i N; rw [mul_comm] at this; omega
  conv_lhs => rw [hi, show i % N + i / N * N + r = (i % N + r) + i / N * N by ring]
  rw [unrolled_add_mul a hN, unrolled_add_mul a hN]
  ring

theorem minSpan_le_rSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    minSpan a N r ≤ rSpan a N r i := by
  rw [rSpan_mod a hN]
  unfold minSpan
  exact ciInf_le (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddBelow
    (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem log_succ_sub_le {y : ℝ} (hy : 0 < y) : Real.log (y + 1) - Real.log y ≤ 1 / y := by
  have h := Real.log_le_sub_one_of_pos (show 0 < (y + 1) / y by positivity)
  rw [Real.log_div (by linarith) hy.ne'] at h
  have : (y + 1) / y - 1 = 1 / y := by rw [add_div, div_self hy.ne']; ring
  linarith

theorem harmonic_lower {N r : ℕ} (hN : 1 ≤ N) (hr : 1 ≤ r) :
    (r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ)) ≤
      ∑ j ∈ Finset.range N, (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
  set R : ℝ := (r : ℝ) + 1 with hR
  set C : ℝ := R * ((N : ℝ) + 1) with hC
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have step1 : ∀ j ∈ Finset.range N,
      R * ((fun j : ℕ => Real.log (C - j)) j - (fun j : ℕ => Real.log (C - j)) (j + 1)) ≤
      (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
    intro j hj
    rw [Finset.mem_range] at hj
    simp only
    push_cast
    have hj1 : j + 1 ≤ (r + 1) * (j / (r + 1)) + (r + 1) := by
      have := Nat.div_add_mod j (r + 1); have := Nat.mod_lt j (show 0 < r + 1 by omega)
      omega
    have hj2 : j / (r + 1) ≤ j := Nat.div_le_self _ _
    have hj1' : (j : ℝ) + 1 ≤ R * ((j / (r + 1) : ℕ) : ℝ) + R := by
      rw [hR]; exact_mod_cast hj1
    have hj2' : ((j / (r + 1) : ℕ) : ℝ) ≤ j := by exact_mod_cast hj2
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have hpos : 0 < (N : ℝ) - ((j / (r + 1) : ℕ) : ℝ) := by linarith
    have hy : 0 < C - ((j : ℝ) + 1) := by
      rw [hC, hR]; nlinarith
    have h2 := log_succ_sub_le hy
    rw [show C - ((j : ℝ) + 1) + 1 = C - j by ring] at h2
    have h3 : R * (1 / (C - ((j : ℝ) + 1))) ≤ (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
      rw [mul_one_div, div_le_div_iff₀ hy hpos]
      rw [hC]; nlinarith
    calc R * (Real.log (C - j) - Real.log (C - ((j : ℝ) + 1)))
        ≤ R * (1 / (C - ((j : ℝ) + 1))) := by
          apply mul_le_mul_of_nonneg_left h2; rw [hR]; linarith
      _ ≤ _ := h3
  have hsum := Finset.sum_range_sub (fun j : ℕ => Real.log (C - j)) N
  simp only [Nat.cast_zero, sub_zero] at hsum
  have hsum' : ∑ j ∈ Finset.range N,
      ((fun j : ℕ => Real.log (C - j)) j - (fun j : ℕ => Real.log (C - j)) (j + 1)) =
      Real.log C - Real.log (C - N) := by
    rw [show Real.log C - Real.log (C - N) = -(Real.log (C - N) - Real.log C) by ring,
      ← hsum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl; intro j _; push_cast; ring
  have hr0 : (r : ℝ) ≠ 0 := by intro h; linarith
  have hCN : 0 < C - N := by rw [hC, hR]; nlinarith
  have hC0 : 0 < C := by linarith
  have hq : 0 < 1 + 1 / (r : ℝ) := by positivity
  have hy0 : 0 < (C - N) * (1 + 1 / (r : ℝ)) / C := by positivity
  have hlog := Real.log_le_sub_one_of_pos hy0
  rw [Real.log_div (by positivity) hC0.ne', Real.log_mul hCN.ne' hq.ne'] at hlog
  have hy1 : (C - N) * (1 + 1 / (r : ℝ)) / C - 1 ≤ 1 / (N : ℝ) := by
    have e : (C - N) * (1 + 1 / (r : ℝ)) / C - 1 = 1 / ((r : ℝ) * ((N : ℝ) + 1)) := by
      rw [hC, hR]; field_simp; ring
    rw [e]
    apply one_div_le_one_div_of_le (by linarith)
    nlinarith
  calc R * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ))
      ≤ R * (Real.log C - Real.log (C - N)) := by
        apply mul_le_mul_of_nonneg_left _ (by rw [hR]; linarith); linarith
    _ = ∑ j ∈ Finset.range N,
        R * ((fun j : ℕ => Real.log (C - j)) j - (fun j : ℕ => Real.log (C - j)) (j + 1)) := by
        rw [← Finset.mul_sum, hsum']
    _ ≤ _ := Finset.sum_le_sum step1

theorem main (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k)) {r : ℕ} (hr : 1 ≤ r)
    {L : ℝ} (hL : 0 < L) {n0 : ℕ} (hn0 : 1 ≤ n0)
    (hm : ∀ t, n0 ≤ t → L < (t : ℝ) * minSpan a t r)
    {N : ℕ} (hN : 2 * n0 ≤ N) :
    L * ((r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ))) ≤ r := by
  classical
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  -- points of the arc
  let P : ℕ → ℕ → Prop := fun i b =>
    ∀ w, w ≤ r → ∃ t < b, ∃ m : ℕ, unrolled a N (i + w) = Int.fract (a t) + m
  have hPN : ∀ i, ∃ b, P i b := fun i => ⟨N, fun w _ => unrolled_mem a hN0 (i + w)⟩
  let b : ℕ → ℕ := fun i => max n0 (Nat.find (hPN i))
  let s : ℕ → ℕ := fun i => N - b i
  have hbN : ∀ i, b i ≤ N := by
    intro i
    exact max_le (by omega) (Nat.find_min' (hPN i) (fun w _ => unrolled_mem a hN0 (i + w)))
  have hb0 : ∀ i, n0 ≤ b i := fun i => le_max_left _ _
  -- each span is at least L / b i
  have hlen : ∀ i, L / (b i : ℝ) ≤ rSpan a N r i := by
    intro i
    have hb1 : 0 < b i := by have := hb0 i; omega
    have hP : P i (b i) := by
      intro w hw
      obtain ⟨t, ht, m, hm'⟩ := Nat.find_spec (hPN i) w hw
      exact ⟨t, lt_of_lt_of_le ht (le_max_right _ _), m, hm'⟩
    have hu := unrolled_strictMono a ha hb1
    have hv := unrolled_strictMono a ha hN0
    have hsub : ∀ j, ∃ k, unrolled a N k = unrolled a (b i) j := by
      intro j
      obtain ⟨t, ht, m, hm'⟩ := unrolled_mem a hb1 j
      obtain ⟨k, hk⟩ := mem_unrolled a (show t < N by have := hbN i; omega) m
      exact ⟨k, by rw [hk, hm']⟩
    have hin : ∀ w, w ≤ r → ∃ j, unrolled a (b i) j = unrolled a N (i + w) := by
      intro w hw
      obtain ⟨t, ht, m, hm'⟩ := hP w hw
      obtain ⟨j, hj⟩ := mem_unrolled a ht m
      exact ⟨j, by rw [hj, hm']⟩
    obtain ⟨j0, hj0⟩ := hin 0 (Nat.zero_le _)
    rw [add_zero] at hj0
    have key := lift hu hv hsub hj0.symm r (fun k h1 h2 => by
      obtain ⟨j, hj⟩ := hin (k - i) (by omega)
      exact ⟨j, by rw [hj, show i + (k - i) = k by omega]⟩)
    have e : rSpan a N r i = rSpan a (b i) r j0 := by
      unfold rSpan; rw [key, hj0]
    rw [e]
    have h1 := minSpan_le_rSpan a hb1 r j0
    have h2 := hm (b i) (hb0 i)
    have hbpos : (0 : ℝ) < (b i : ℝ) := by exact_mod_cast hb1
    rw [div_le_iff₀ hbpos]
    nlinarith
  -- counting
  have hcount : ∀ k, ((Finset.range N).filter (fun i => s i < k)).card ≤ (r + 1) * k := by
    intro k
    by_cases hk : N - n0 < k
    · calc _ ≤ (Finset.range N).card := Finset.card_filter_le _ _
        _ = N := Finset.card_range N
        _ ≤ (r + 1) * k := by
          have : 2 * (N - n0) ≥ N := by omega
          nlinarith
    · push Not at hk
      have hsub : (Finset.range N).filter (fun i => s i < k) ⊆
          (Finset.range k).biUnion (fun d => (Finset.range N).filter (fun i =>
            ∃ m : ℤ, unrolled a N i ≤ Int.fract (a (N - k + d)) + m ∧
              Int.fract (a (N - k + d)) + m < unrolled a N (i + (r + 1)))) := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_range] at hi
        simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
        have hsi : s i = N - b i := rfl
        have hbk : N - k < b i := by have := hbN i; omega
        have hfind : N - k < Nat.find (hPN i) := by
          rcases le_or_gt (Nat.find (hPN i)) (N - k) with h | h
          · exfalso
            have : b i ≤ N - k := max_le (by omega) h
            omega
          · exact h
        have hnot : ¬ P i (N - k) := Nat.find_min (hPN i) hfind
        obtain ⟨w, hw, hw2⟩ : ∃ w, w ≤ r ∧ ∀ t, t < N - k → ∀ m : ℕ,
            unrolled a N (i + w) ≠ Int.fract (a t) + m := by
          by_contra hc
          apply hnot
          intro w hw
          by_contra hc2
          exact hc ⟨w, hw, fun t ht m heq => hc2 ⟨t, ht, m, heq⟩⟩
        obtain ⟨t, ht, m, hm'⟩ := unrolled_mem a hN0 (i + w)
        have htk : N - k ≤ t := by
          by_contra hcon
          exact hw2 t (by omega) m hm'
        refine ⟨t - (N - k), by omega, hi.1, ?_⟩
        rw [show N - k + (t - (N - k)) = t by omega]
        refine ⟨(m : ℤ), ?_, ?_⟩
        · push_cast; rw [← hm']
          exact (unrolled_strictMono a ha hN0).monotone (by omega)
        · push_cast; rw [← hm']
          exact (unrolled_strictMono a ha hN0) (by omega)
      calc _ ≤ _ := Finset.card_le_card hsub
        _ ≤ ∑ d ∈ Finset.range k, ((Finset.range N).filter (fun i =>
            ∃ m : ℤ, unrolled a N i ≤ Int.fract (a (N - k + d)) + m ∧
              Int.fract (a (N - k + d)) + m < unrolled a N (i + (r + 1)))).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ d ∈ Finset.range k, (r + 1) := Finset.sum_le_sum (fun d _ =>
            card_ho_le a ha hN0 (r + 1) _ _ (Finset.filter_subset _ _)
              (fun i hi => (Finset.mem_filter.mp hi).2))
        _ = (r + 1) * k := by simp [mul_comm]
  -- rearrangement
  have hh : Antitone (fun k : ℕ => -(L / ((N : ℝ) - ((min k (N - 1) : ℕ) : ℝ)))) := by
    intro x y hxy
    simp only [neg_le_neg_iff]
    have h1 : min x (N - 1) ≤ min y (N - 1) := min_le_min_right _ hxy
    have h2 : min y (N - 1) ≤ N - 1 := min_le_right _ _
    have h1' : ((min x (N - 1) : ℕ) : ℝ) ≤ ((min y (N - 1) : ℕ) : ℝ) := by exact_mod_cast h1
    have h2' : ((min y (N - 1) : ℕ) : ℝ) + 1 ≤ N := by
      have : min y (N - 1) + 1 ≤ N := by omega
      exact_mod_cast this
    apply div_le_div_of_nonneg_left hL.le (by linarith) (by linarith)
  have hre := rearrange _ hh (r + 1) s (Finset.range N) hcount
  rw [Finset.card_range] at hre
  have es : ∀ i, ((N : ℝ) - ((min (s i) (N - 1) : ℕ) : ℝ)) = (b i : ℝ) := by
    intro i
    have h1 : min (s i) (N - 1) = N - b i := by
      have := hb0 i; have := hbN i; simp only [s]; omega
    rw [h1, Nat.cast_sub (hbN i)]; ring
  have ej : ∀ j ∈ Finset.range N, ((min (j / (r + 1)) (N - 1) : ℕ) : ℝ) =
      ((j / (r + 1) : ℕ) : ℝ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have : j / (r + 1) ≤ N - 1 := le_trans (Nat.div_le_self _ _) (by omega)
    rw [min_eq_left this]
  simp only [Finset.sum_neg_distrib, neg_le_neg_iff] at hre
  have h1 : ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) ≤
      ∑ i ∈ Finset.range N, L / (b i : ℝ) := by
    have e1 : ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) =
        ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((min (j / (r + 1)) (N - 1) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl; intro j hj; rw [ej j hj]
    have e2 : ∑ i ∈ Finset.range N, L / (b i : ℝ) =
        ∑ i ∈ Finset.range N, L / ((N : ℝ) - ((min (s i) (N - 1) : ℕ) : ℝ)) := by
      apply Finset.sum_congr rfl; intro i _; rw [es i]
    rw [e1, e2]; exact hre
  have h2 : ∑ i ∈ Finset.range N, L / (b i : ℝ) ≤ r := by
    rw [← sum_rSpan a hN0 r]
    exact Finset.sum_le_sum (fun i _ => hlen i)
  have h3 := harmonic_lower (show 1 ≤ N by omega) hr
  have e : ∑ j ∈ Finset.range N, L / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) =
      L * ∑ j ∈ Finset.range N, (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_one_div]
  calc L * ((r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ)))
      ≤ L * ∑ j ∈ Finset.range N, (1 : ℝ) / ((N : ℝ) - ((j / (r + 1) : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left h3 hL.le
    _ = _ := e.symm
    _ ≤ _ := h1
    _ ≤ _ := h2

end GapSmall

lemma small_le (r : ℕ) (hr : 1 ≤ r) :
    smallLambda r ≤ ENNReal.ofReal ((r : ℝ) / ((r : ℝ) + 1) * (1 / Real.log (1 + 1 / (r : ℝ)))) := by
  unfold smallLambda
  apply iSup₂_le
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1, hx2⟩ := exists_between hcon
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  set L := x.toReal
  have hxL : x = ENNReal.ofReal L := (ENNReal.ofReal_toReal hxtop).symm
  rw [hxL] at hx1 hx2
  have hcL := ENNReal.ofReal_lt_ofReal_iff'.mp hx1
  have hL : 0 < L := hcL.2
  have hev := Filter.eventually_lt_of_lt_liminf hx2
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  have hm : ∀ t, max n0 1 ≤ t → L < (t : ℝ) * minSpan a t r := fun t ht =>
    (ENNReal.ofReal_lt_ofReal_iff'.mp (hn0 t (le_trans (le_max_left _ _) ht))).1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogpos : 0 < Real.log (1 + 1 / (r : ℝ)) := by
    apply Real.log_pos; have := one_div_pos.mpr hr0; linarith
  -- L * (r+1) * log > r
  have hgap : 0 < L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - r := by
    have h := hcL.1
    have e : (r : ℝ) / ((r : ℝ) + 1) * (1 / Real.log (1 + 1 / (r : ℝ))) =
        r / (((r : ℝ) + 1) * Real.log (1 + 1 / (r : ℝ))) := by
      field_simp
    rw [e, div_lt_iff₀ (by positivity)] at h
    linarith
  obtain ⟨m, hmm⟩ := exists_nat_gt (L * (r + 1 : ℝ) /
    (L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - r))
  obtain ⟨N, hN⟩ : ∃ N, N = max (2 * max n0 1) (m + 1) := ⟨_, rfl⟩
  have hN1 : 2 * max n0 1 ≤ N := by omega
  have hNm : m + 1 ≤ N := by omega
  have key := GapSmall.main a ha hr hL (le_max_right n0 1) hm hN1
  have hNr : (m : ℝ) + 1 ≤ N := by exact_mod_cast hNm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hNpos : (0 : ℝ) < N := by linarith
  have h5 : L * (r + 1 : ℝ) * (1 / (N : ℝ)) <
      L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - r := by
    rw [mul_one_div, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hgap] at hmm
    nlinarith [mul_le_mul_of_nonneg_left hNr hgap.le]
  have e : L * ((r + 1 : ℝ) * (Real.log (1 + 1 / (r : ℝ)) - 1 / (N : ℝ))) =
      L * ((r + 1 : ℝ) * Real.log (1 + 1 / (r : ℝ))) - L * (r + 1 : ℝ) * (1 / (N : ℝ)) := by ring
  rw [e] at key
  linarith

open Filter Erdos1221

namespace GapMu

theorem unrolled_eq (a : ℕ → ℝ) {n k : ℕ} (m : ℕ) (hk : k < n) :
    unrolled a n (k + m * n) = sortedPoint a n ⟨k, hk⟩ + m := by
  have hn : 0 < n := by omega
  unfold unrolled
  rw [dif_pos hn]
  have h1 : (k + m * n) % n = k := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hk]
  have h2 : (k + m * n) / n = m := by
    rw [Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hk, zero_add]
  have h3 : sortedPoint a n ⟨(k + m * n) % n, Nat.mod_lt _ hn⟩ = sortedPoint a n ⟨k, hk⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]

theorem unrolled_eq' (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n j = sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ + ((j / n : ℕ) : ℝ) := by
  unfold unrolled
  rw [dif_pos hn]

theorem unrolled_add (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    unrolled a n (j + n) = unrolled a n j + 1 := by
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have h1 : (j + n) % n = j % n := Nat.add_mod_right j n
  have h2 : (j + n) / n = j / n + 1 := Nat.add_div_right j hn
  have h3 : sortedPoint a n ⟨(j + n) % n, Nat.mod_lt _ hn⟩ =
      sortedPoint a n ⟨j % n, Nat.mod_lt _ hn⟩ := by
    congr 1; exact Fin.ext h1
  rw [h3, h2]; push_cast; ring

theorem sum_shift_telescope {G : Type*} [AddCommGroup G] (f : ℕ → G) (c : G) (n : ℕ)
    (hf : ∀ j, f (j + n) = f j + c) (r : ℕ) :
    ∑ i ∈ Finset.range n, (f (i + r) - f i) = r • c := by
  induction r with
  | zero => simp
  | succ k ih =>
    have e : ∑ i ∈ Finset.range n, (f (i + (k + 1)) - f i) =
        ∑ i ∈ Finset.range n, (f (i + k) - f i) +
          ∑ i ∈ Finset.range n, ((fun i => f (i + k)) (i + 1) - (fun i => f (i + k)) i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only
      rw [show i + 1 + k = i + (k + 1) by omega]
      abel
    rw [e, ih, Finset.sum_range_sub (fun i => f (i + k))]
    simp only [zero_add]
    rw [show n + k = k + n by omega, hf, succ_nsmul]
    abel

theorem sum_rSpan (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (r : ℕ) :
    ∑ i ∈ Finset.range n, rSpan a n r i = r := by
  unfold rSpan
  rw [sum_shift_telescope (unrolled a n) 1 n (unrolled_add a hn) r]
  simp

theorem sortedPoint_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    (n : ℕ) : StrictMono (sortedPoint a n) := by
  apply Monotone.strictMono_of_injective (Tuple.monotone_sort (pts a n))
  intro x y hxy
  have h : pts a n (Tuple.sort (pts a n) x) = pts a n (Tuple.sort (pts a n) y) := hxy
  have h2 := ha h
  have h3 : Tuple.sort (pts a n) x = Tuple.sort (pts a n) y := Fin.ext h2
  exact (Tuple.sort (pts a n)).injective h3

theorem sortedPoint_mem (a : ℕ → ℝ) (n : ℕ) (k : Fin n) :
    0 ≤ sortedPoint a n k ∧ sortedPoint a n k < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem unrolled_strictMono (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {n : ℕ} (hn : 0 < n) : StrictMono (unrolled a n) := by
  intro j j' hjj
  rw [unrolled_eq' a hn, unrolled_eq' a hn]
  have hq : j / n ≤ j' / n := Nat.div_le_div_right hjj.le
  rcases hq.lt_or_eq with hlt | heq
  · have h1 := (sortedPoint_mem a n ⟨j % n, Nat.mod_lt _ hn⟩).2
    have h2 := (sortedPoint_mem a n ⟨j' % n, Nat.mod_lt _ hn⟩).1
    have h3 : ((j / n : ℕ) : ℝ) + 1 ≤ ((j' / n : ℕ) : ℝ) := by exact_mod_cast hlt
    linarith
  · have hm : j % n < j' % n := by
      have e1 := Nat.div_add_mod j n
      have e2 := Nat.div_add_mod j' n
      rw [heq] at e1
      omega
    have := sortedPoint_strictMono a ha n (show (⟨j % n, Nat.mod_lt _ hn⟩ : Fin n) < ⟨j' % n, Nat.mod_lt _ hn⟩ from hm)
    rw [heq]
    linarith

/-- forward range description -/
theorem unrolled_mem (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j : ℕ) :
    ∃ t < n, ∃ m : ℕ, unrolled a n j = Int.fract (a t) + m := by
  rw [unrolled_eq' a hn]
  refine ⟨(Tuple.sort (pts a n) ⟨j % n, Nat.mod_lt _ hn⟩ : ℕ), Fin.is_lt _, j / n, rfl⟩

/-- backward range description -/
theorem mem_unrolled (a : ℕ → ℝ) {n t : ℕ} (ht : t < n) (m : ℕ) :
    ∃ j, unrolled a n j = Int.fract (a t) + m := by
  set k := (Tuple.sort (pts a n)).symm ⟨t, ht⟩ with hk
  refine ⟨k + m * n, ?_⟩
  rw [unrolled_eq a m k.is_lt]
  congr 1
  show pts a n (Tuple.sort (pts a n) ⟨k, k.is_lt⟩) = _
  have : (⟨(k : ℕ), k.is_lt⟩ : Fin n) = k := rfl
  rw [this, hk, Equiv.apply_symm_apply]
  rfl

theorem unrolled_add_mul (a : ℕ → ℝ) {n : ℕ} (hn : 0 < n) (j m : ℕ) :
    unrolled a n (j + m * n) = unrolled a n j + m := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [show j + (k + 1) * n = (j + k * n) + n by ring, unrolled_add a hn, ih]
    push_cast; ring


theorem lift {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {A j0 : ℕ} (h0 : v A = u j0) (w : ℕ)
    (hw : ∀ k, A < k → k ≤ A + w → ∃ j, u j = v k) : v (A + w) = u (j0 + w) := by
  induction w with
  | zero => simpa using h0
  | succ w ih =>
    have ih' := ih (fun k h1 h2 => hw k h1 (by omega))
    obtain ⟨j, hj⟩ := hw (A + (w + 1)) (by omega) le_rfl
    obtain ⟨k', hk'⟩ := hsub (j0 + (w + 1))
    have h1 : j0 + w < j := by
      rw [← hu.lt_iff_lt, hj, ← ih']; exact hv (by omega)
    have h2 : A + w < k' := by
      rw [← hv.lt_iff_lt, hk', ih']; exact hu (by omega)
    have h3 : j ≤ j0 + (w + 1) := by
      rw [← hu.le_iff_le, hj, ← hk']; exact hv.monotone (by omega)
    have : j = j0 + (w + 1) := by omega
    rw [← hj, this]

theorem skip {u v : ℕ → ℝ} (hu : StrictMono u) (hv : StrictMono v)
    (hsub : ∀ j, ∃ k, v k = u j) {k j : ℕ} (h0 : v k = u j)
    (hnew : ∀ j', u j' ≠ v (k + 1)) (h2 : ∃ j', u j' = v (k + 2)) :
    v (k + 2) = u (j + 1) := by
  obtain ⟨j', hj'⟩ := h2
  have e1 : j < j' := by
    rw [← hu.lt_iff_lt, hj', ← h0]; exact hv (by omega)
  obtain ⟨k', hk'⟩ := hsub (j + 1)
  have e2 : k < k' := by
    rw [← hv.lt_iff_lt, hk', h0]; exact hu (by omega)
  have e3 : k' ≠ k + 1 := by
    intro h; rw [h] at hk'; exact hnew _ hk'.symm
  have e4 : j' ≤ j + 1 := by
    rw [← hu.le_iff_le, hj', ← hk']; exact hv.monotone (by omega)
  have : j' = j + 1 := by omega
  rw [← hj', this]

theorem rSpan_mod (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i = rSpan a N r (i % N) := by
  unfold rSpan
  have hi : i = i % N + (i / N) * N := by
    have := Nat.mod_add_div i N; rw [mul_comm] at this; omega
  conv_lhs => rw [hi, show i % N + i / N * N + r = (i % N + r) + i / N * N by ring]
  rw [unrolled_add_mul a hN, unrolled_add_mul a hN]
  ring

theorem minSpan_le_rSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    minSpan a N r ≤ rSpan a N r i := by
  rw [rSpan_mod a hN]
  unfold minSpan
  exact ciInf_le (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddBelow
    (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem rSpan_le_maxSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r i : ℕ) :
    rSpan a N r i ≤ maxSpan a N r := by
  rw [rSpan_mod a hN]
  unfold maxSpan
  exact le_ciSup (Set.finite_range (fun j : Fin N => rSpan a N r j)).bddAbove
    (⟨i % N, Nat.mod_lt _ hN⟩ : Fin N)

theorem minSpan_pos (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k))
    {N r : ℕ} (hN : 0 < N) (hr : 1 ≤ r) : 0 < minSpan a N r := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun j : Fin N => rSpan a N r j)
  unfold minSpan
  rw [← hi]
  unfold rSpan
  have := unrolled_strictMono a ha hN (show (i : ℕ) < i + r by omega)
  linarith

theorem le_N_maxSpan (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (r : ℕ) :
    (r : ℝ) ≤ N * maxSpan a N r := by
  rw [← sum_rSpan a hN r]
  calc ∑ i ∈ Finset.range N, rSpan a N r i ≤ ∑ i ∈ Finset.range N, maxSpan a N r :=
        Finset.sum_le_sum (fun i _ => rSpan_le_maxSpan a hN r i)
    _ = N * maxSpan a N r := by simp

theorem unrolled_lt (a : ℕ → ℝ) {N : ℕ} (hN : 0 < N) (k : ℕ) : unrolled a N k < k + 1 := by
  rw [unrolled_eq' a hN]
  have h1 := (sortedPoint_mem a N ⟨k % N, Nat.mod_lt _ hN⟩).2
  have h2 : ((k / N : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.div_le_self k N
  linarith

theorem fract_eq_of_add {x y : ℝ} {m m' : ℕ} (h : Int.fract x + m = Int.fract y + m') :
    Int.fract x = Int.fract y := by
  have := congrArg Int.fract h
  rwa [Int.fract_add_natCast, Int.fract_add_natCast, Int.fract_fract, Int.fract_fract] at this

/-- One step: the new point creates `r + 1` new `r`-spans whose total is the total of `r` old
`r`-spans. -/
theorem step (a : ℕ → ℝ) (ha : Function.Injective fun k ↦ Int.fract (a k)) {n r : ℕ}
    (hr : 1 ≤ r) (hn : 2 * r ≤ n) :
    ((r : ℝ) + 1) * minSpan a (n + 1) r ≤ r * maxSpan a n r := by
  have hn0 : 0 < n := by omega
  have hn1 : 0 < n + 1 := by omega
  have hu := unrolled_strictMono a ha hn0
  have hv := unrolled_strictMono a ha hn1
  have hsub : ∀ j, ∃ k, unrolled a (n + 1) k = unrolled a n j := by
    intro j
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn0 j
    obtain ⟨k, hk⟩ := mem_unrolled a (show t < n + 1 by omega) m
    exact ⟨k, by rw [hk, hm]⟩
  obtain ⟨K, hK⟩ := mem_unrolled a (show n < n + 1 by omega) r
  have hKr : r ≤ K := by
    by_contra h
    have h1 := unrolled_lt a hn1 K
    have h2 : (K : ℝ) + 1 ≤ r := by exact_mod_cast (show K + 1 ≤ r by omega)
    have h3 := Int.fract_nonneg (a n)
    linarith
  obtain ⟨A, hA⟩ : ∃ A, A = K - r := ⟨_, rfl⟩
  have hAK : K = A + r := by omega
  have hnew : ∀ j, unrolled a n j ≠ unrolled a (n + 1) K := by
    intro j hj
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn0 j
    rw [hm, hK] at hj
    have := ha (fract_eq_of_add hj)
    omega
  have hold : ∀ k, A ≤ k → k ≤ A + 2 * r → k ≠ K → ∃ j, unrolled a n j = unrolled a (n + 1) k := by
    intro k hk1 hk2 hkK
    obtain ⟨t, ht, m, hm⟩ := unrolled_mem a hn1 k
    by_cases htn : t < n
    · obtain ⟨j, hj⟩ := mem_unrolled a htn m
      exact ⟨j, by rw [hj, hm]⟩
    · exfalso
      have htn' : t = n := by omega
      rw [htn'] at hm
      rcases le_or_gt r m with hmr | hmr
      · have e := unrolled_add_mul a hn1 K (m - r)
        rw [hK, Nat.cast_sub hmr] at e
        have e2 : unrolled a (n + 1) (K + (m - r) * (n + 1)) = unrolled a (n + 1) k := by
          rw [e, hm]; ring
        have := hv.injective e2
        rcases Nat.eq_zero_or_pos (m - r) with h0 | h0
        · rw [h0] at this; omega
        · have : (n + 1) ≤ (m - r) * (n + 1) := Nat.le_mul_of_pos_left _ h0
          omega
      · have e := unrolled_add_mul a hn1 k (r - m)
        rw [hm, Nat.cast_sub hmr.le] at e
        have e2 : unrolled a (n + 1) (k + (r - m) * (n + 1)) = unrolled a (n + 1) K := by
          rw [e, hK]; ring
        have := hv.injective e2
        have h0 : 0 < r - m := by omega
        have : (n + 1) ≤ (r - m) * (n + 1) := Nat.le_mul_of_pos_left _ h0
        omega
  obtain ⟨j0, hj0⟩ := hold A le_rfl (by omega) (by omega)
  have h1 : ∀ w, w ≤ r - 1 → unrolled a (n + 1) (A + w) = unrolled a n (j0 + w) := fun w hw =>
    lift hu hv hsub hj0.symm w (fun k hk1 hk2 => hold k (by omega) (by omega) (by omega))
  have h2 : unrolled a (n + 1) (A + r + 1) = unrolled a n (j0 + r) := by
    have e1 := h1 (r - 1) le_rfl
    rw [show A + (r - 1) = A + r - 1 by omega] at e1
    have e := skip hu hv hsub e1 (by rw [show A + r - 1 + 1 = K by omega]; exact hnew)
      (hold (A + r - 1 + 2) (by omega) (by omega) (by omega))
    rw [show A + r - 1 + 2 = A + r + 1 by omega, show j0 + (r - 1) + 1 = j0 + r by omega] at e
    exact e
  have h3 : ∀ w, w ≤ r - 1 →
      unrolled a (n + 1) (A + r + 1 + w) = unrolled a n (j0 + r + w) := fun w hw =>
    lift hu hv hsub h2 w (fun k hk1 hk2 => hold k (by omega) (by omega) (by omega))
  -- the sum of the r + 1 new spans
  have hS : ∑ w ∈ Finset.range (r + 1), rSpan a (n + 1) r (A + w) =
      ∑ w ∈ Finset.range r, rSpan a n r (j0 + w) := by
    unfold rSpan
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    have e1 : ∑ w ∈ Finset.range (r + 1), unrolled a (n + 1) (A + w + r) =
        ∑ w ∈ Finset.range r, unrolled a n (j0 + w + r) + unrolled a (n + 1) K := by
      rw [Finset.sum_range_succ']
      congr 1
      · apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mem_range] at hw
        rw [show A + (w + 1) + r = A + r + 1 + w by ring, h3 w (by omega),
          show j0 + r + w = j0 + w + r by ring]
      · rw [hAK]; ring_nf
    have e2 : ∑ w ∈ Finset.range (r + 1), unrolled a (n + 1) (A + w) =
        ∑ w ∈ Finset.range r, unrolled a n (j0 + w) + unrolled a (n + 1) K := by
      rw [Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro w hw
        rw [Finset.mem_range] at hw
        exact h1 w (by omega)
      · rw [hAK]
    rw [e1, e2]; ring
  have hlow : ((r : ℝ) + 1) * minSpan a (n + 1) r ≤
      ∑ w ∈ Finset.range (r + 1), rSpan a (n + 1) r (A + w) := by
    calc ((r : ℝ) + 1) * minSpan a (n + 1) r =
        ∑ w ∈ Finset.range (r + 1), minSpan a (n + 1) r := by simp
      _ ≤ _ := Finset.sum_le_sum (fun w _ => minSpan_le_rSpan a hn1 r (A + w))
  have hup : ∑ w ∈ Finset.range r, rSpan a n r (j0 + w) ≤ r * maxSpan a n r := by
    calc ∑ w ∈ Finset.range r, rSpan a n r (j0 + w) ≤
        ∑ w ∈ Finset.range r, maxSpan a n r :=
          Finset.sum_le_sum (fun w _ => rSpan_le_maxSpan a hn0 r (j0 + w))
      _ = r * maxSpan a n r := by simp
  linarith

end GapMu

lemma mu_ge (r : ℕ) (hr : 1 ≤ r) :
    ENNReal.ofReal (1 + 1 / (r : ℝ)) ≤ mu r := by
  unfold mu
  apply le_iInf₂
  intro a ha
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1, hx2⟩ := exists_between hcon
  have hxtop : x ≠ ⊤ := ne_top_of_lt hx2
  set c := x.toReal
  have hxc : x = ENNReal.ofReal c := (ENNReal.ofReal_toReal hxtop).symm
  rw [hxc] at hx1 hx2
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  have hc1 : c < 1 + 1 / (r : ℝ) := (ENNReal.ofReal_lt_ofReal_iff'.mp hx2).1
  have hev := Filter.eventually_lt_of_limsup_lt hx1
  rw [Filter.eventually_atTop] at hev
  obtain ⟨n0, hn0⟩ := hev
  have hratio : ∀ n, max n0 1 ≤ n → maxSpan a n r < c * minSpan a n r := by
    intro n hn
    have hnpos : 0 < n := by omega
    have hmpos := GapMu.minSpan_pos a ha hnpos hr
    have h := hn0 n (by omega)
    rw [← ENNReal.ofReal_div_of_pos hmpos] at h
    have h' := (ENNReal.ofReal_lt_ofReal_iff'.mp h).1
    rwa [div_lt_iff₀ hmpos] at h'
  obtain ⟨n1, hn1⟩ : ∃ n1, n1 = max (max n0 1) (2 * r) := ⟨_, rfl⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = c * r / (r + 1) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hρ1 : ρ < 1 := by
    rw [hρ, div_lt_one (by positivity)]
    have h := mul_lt_mul_of_pos_right hc1 hr0
    have e : (1 + 1 / (r : ℝ)) * r = r + 1 := by field_simp
    linarith
  have hdecay : ∀ n, n1 ≤ n → maxSpan a (n + 1) r ≤ ρ * maxSpan a n r := by
    intro n hn
    have h1 := hratio (n + 1) (by omega)
    have h2 := GapMu.step a ha hr (show 2 * r ≤ n by omega)
    have h3 : c * minSpan a (n + 1) r ≤ ρ * maxSpan a n r := by
      rw [hρ, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
    linarith
  have hiter : ∀ k, maxSpan a (n1 + k) r ≤ ρ ^ k * maxSpan a n1 r := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc maxSpan a (n1 + (k + 1)) r = maxSpan a ((n1 + k) + 1) r := by rw [add_assoc]
        _ ≤ ρ * maxSpan a (n1 + k) r := hdecay _ (by omega)
        _ ≤ ρ * (ρ ^ k * maxSpan a n1 r) := mul_le_mul_of_nonneg_left ih hρ0
        _ = ρ ^ (k + 1) * maxSpan a n1 r := by ring
  have ht : Tendsto (fun k : ℕ => ((n1 : ℝ) + k) * ρ ^ k * maxSpan a n1 r) atTop
      (nhds 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one hρ0 hρ1
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
    have h3 := ((h2.const_mul (n1 : ℝ)).add h1).mul_const (maxSpan a n1 r)
    simp only [mul_zero, zero_add, zero_mul] at h3
    refine h3.congr (fun k => by ring)
  have hev2 := ht.eventually (gt_mem_nhds hr0)
  rw [Filter.eventually_atTop] at hev2
  obtain ⟨k, hk⟩ := hev2
  have h4 := hk k le_rfl
  have h5 := GapMu.le_N_maxSpan a (show 0 < n1 + k by omega) r
  have h6 := hiter k
  have hpos : (0 : ℝ) ≤ ((n1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
  have h7 := mul_le_mul_of_nonneg_left h6 hpos
  push_cast at h5 h7
  nlinarith

open Filter Erdos1221 Real

noncomputable section

namespace Witness

open Classical ENNReal

noncomputable def log2 (x : ℝ) : ℝ := Real.log x / Real.log 2

noncomputable def ex (k : ℕ) : ℝ := log2 (2 * (k : ℝ) + 1)

lemma log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

lemma log2_lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) : log2 x < log2 y := by
  rw [log2, log2, div_lt_div_iff_of_pos_right log_two_pos]
  exact Real.log_lt_log hx hxy

lemma log2_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log2 x ≤ log2 y ↔ x ≤ y := by
  rw [log2, log2, div_le_div_iff_of_pos_right log_two_pos, Real.log_le_log_iff hx hy]

lemma log2_sub {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : log2 x - log2 y = log2 (x / y) := by
  rw [log2, log2, log2, ← sub_div, Real.log_div hx.ne' hy.ne']

lemma log2_two : log2 2 = 1 := by
  rw [log2, div_self log_two_pos.ne']

lemma log2_mul_two_pow (o v : ℕ) (ho : 0 < o) :
    log2 ((o : ℝ) * (2 : ℝ) ^ v) = log2 (o : ℝ) + v := by
  rw [log2, Real.log_mul (by exact_mod_cast ho.ne') (by positivity), Real.log_pow, log2]
  field_simp [log_two_pos.ne']

lemma cast_odd_mul_pow (o v : ℕ) : ((o * 2 ^ v : ℕ) : ℝ) = (o : ℝ) * (2 : ℝ) ^ v := by
  norm_cast

def oddPart (m : ℕ) : ℕ := m / 2 ^ padicValNat 2 m

lemma oddPart_mul (m : ℕ) : m = 2 ^ padicValNat 2 m * oddPart m :=
  (Nat.mul_div_cancel' (pow_padicValNat_dvd (p := 2) (n := m))).symm

lemma oddPart_pos {m : ℕ} (hm : 0 < m) : 0 < oddPart m := by
  have h := oddPart_mul m
  rw [h] at hm
  exact Nat.pos_of_mul_pos_left hm

lemma oddPart_le (m : ℕ) : oddPart m ≤ m := Nat.div_le_self _ _

lemma oddPart_odd {m : ℕ} (hm : 0 < m) : Odd (oddPart m) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hdv
  obtain ⟨k, hk⟩ := hdv
  refine pow_succ_padicValNat_not_dvd (p := 2) hm.ne' ⟨k, ?_⟩
  calc
    m = 2 ^ padicValNat 2 m * oddPart m := oddPart_mul m
    _ = 2 ^ padicValNat 2 m * (2 * k) := by rw [hk]
    _ = 2 ^ (padicValNat 2 m + 1) * k := by rw [← mul_assoc, ← pow_succ]

lemma oddPart_eq_two_mul_add_one {m : ℕ} (hm : 0 < m) :
    oddPart m = 2 * ((oddPart m - 1) / 2) + 1 := by
  obtain ⟨k, hk⟩ := oddPart_odd hm
  have hkdiv : (2 * k + 1 - 1) / 2 = k := by
    rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  omega

lemma oddPart_inj {n a b : ℕ} (ha0 : n ≤ a) (ha : a < 2 * n) (hb0 : n ≤ b) (hb : b < 2 * n)
    (h : oddPart a = oddPart b) : a = b := by
  have ha1 : 0 < a := by omega
  have hb1 : 0 < b := by omega
  have ea := oddPart_mul a
  have eb := oddPart_mul b
  rcases le_total (padicValNat 2 a) (padicValNat 2 b) with hle | hle
  · obtain ⟨d, hd⟩ := Nat.le.dest hle
    have hb_eq : b = a * 2 ^ d := by
      calc
        b = 2 ^ padicValNat 2 b * oddPart b := eb
        _ = 2 ^ (padicValNat 2 a + d) * oddPart a := by rw [← hd, h]
        _ = 2 ^ padicValNat 2 a * 2 ^ d * oddPart a := by rw [pow_add]
        _ = 2 ^ padicValNat 2 a * oddPart a * 2 ^ d := by
          rw [mul_assoc, mul_comm (2 ^ d), mul_assoc]
        _ = a * 2 ^ d := by rw [← ea]
    have hd0 : d = 0 := by
      by_contra hdpos
      have hd1 : 1 ≤ d := by omega
      have hbge : a * 2 ≤ b := by
        calc
          a * 2 = a * 2 ^ 1 := by simp
          _ ≤ a * 2 ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hd1)
          _ = b := by rw [← hb_eq]
      have : 2 * n ≤ b := by
        calc
          2 * n ≤ 2 * a := Nat.mul_le_mul_left _ ha0
          _ = a * 2 := by ring
          _ ≤ b := hbge
      omega
    exact (by simpa [hd0] using hb_eq : b = a).symm
  · obtain ⟨d, hd⟩ := Nat.le.dest hle
    have ha_eq : a = b * 2 ^ d := by
      calc
        a = 2 ^ padicValNat 2 a * oddPart a := ea
        _ = 2 ^ (padicValNat 2 b + d) * oddPart b := by rw [← hd, h.symm]
        _ = 2 ^ padicValNat 2 b * 2 ^ d * oddPart b := by rw [pow_add]
        _ = 2 ^ padicValNat 2 b * oddPart b * 2 ^ d := by
          rw [mul_assoc, mul_comm (2 ^ d), mul_assoc]
        _ = b * 2 ^ d := by rw [← eb]
    have hd0 : d = 0 := by
      by_contra hdpos
      have hd1 : 1 ≤ d := by omega
      have hage : b * 2 ≤ a := by
        calc
          b * 2 = b * 2 ^ 1 := by simp
          _ ≤ b * 2 ^ d := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hd1)
          _ = a := by rw [← ha_eq]
      have : 2 * n ≤ a := by
        calc
          2 * n ≤ 2 * b := Nat.mul_le_mul_left _ hb0
          _ = b * 2 := by ring
          _ ≤ a := hage
      omega
    simpa [hd0] using ha_eq

lemma ex_inj : Function.Injective fun k ↦ Int.fract (ex k) := by
  intro a b h
  obtain ⟨z, hz⟩ := Int.fract_eq_fract.mp h
  have hlog : Real.log (2 * (a : ℝ) + 1) - Real.log (2 * (b : ℝ) + 1) =
      (z : ℝ) * Real.log 2 := by
    have hz' : log2 (2 * (a : ℝ) + 1) - log2 (2 * (b : ℝ) + 1) = (z : ℝ) := by
      simpa [ex] using hz
    simp only [log2] at hz'
    field_simp [log_two_pos.ne'] at hz'
    linarith
  have hratio : (2 * (a : ℝ) + 1) / (2 * (b : ℝ) + 1) = (2 : ℝ) ^ (z : ℝ) := by
    have hexp := congrArg Real.exp hlog
    rw [Real.exp_sub, Real.exp_log (by positivity), Real.exp_log (by positivity)] at hexp
    rw [show (z : ℝ) * Real.log 2 = Real.log 2 * (z : ℝ) by ring] at hexp
    rwa [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at hexp
  rw [Real.rpow_intCast] at hratio
  rcases lt_trichotomy z 0 with hz0 | rfl | hz0
  · have hzint : z = - (z.natAbs : ℤ) := by
      have : (z.natAbs : ℤ) = -z := by
        simpa [Int.natCast_natAbs] using (abs_of_neg hz0)
      exact (neg_eq_iff_eq_neg.mp this.symm)
    rw [hzint, zpow_neg, zpow_natCast] at hratio
    have habs : (2 * (a : ℝ) + 1) * (2 : ℝ) ^ z.natAbs = 2 * (b : ℝ) + 1 := by
      field_simp at hratio
      simpa [mul_comm] using hratio
    have hnat : (2 * a + 1) * 2 ^ z.natAbs = 2 * b + 1 := by exact_mod_cast habs
    have hevenPow : Even (2 ^ z.natAbs) :=
      even_two.pow_of_ne_zero (Int.natAbs_ne_zero.mpr hz0.ne)
    have heven : Even ((2 * a + 1) * 2 ^ z.natAbs) := hevenPow.mul_left _
    have hodd : Odd ((2 * a + 1) * 2 ^ z.natAbs) := by
      rw [hnat]
      exact ⟨b, rfl⟩
    exact (Nat.not_even_iff_odd.mpr hodd heven).elim
  · rw [zpow_zero] at hratio
    have h1 : (2 * (a : ℝ) + 1) / (2 * (b : ℝ) + 1) = 1 := hratio
    have h2 : (2 * (a : ℝ) + 1) = 2 * (b : ℝ) + 1 := by
      field_simp at h1
      exact h1
    have : 2 * a + 1 = 2 * b + 1 := by exact_mod_cast h2
    omega
  · have hzint : (z.natAbs : ℤ) = z := by
      simp [Int.natCast_natAbs, abs_of_nonneg hz0.le]
    rw [← hzint, zpow_natCast] at hratio
    have habs : (2 * (a : ℝ) + 1) = (2 * (b : ℝ) + 1) * (2 : ℝ) ^ z.natAbs := by
      field_simp at hratio
      exact hratio
    have hnat : 2 * a + 1 = (2 * b + 1) * 2 ^ z.natAbs := by exact_mod_cast habs
    have hevenPow : Even (2 ^ z.natAbs) :=
      even_two.pow_of_ne_zero (Int.natAbs_ne_zero.mpr hz0.ne')
    have heven : Even ((2 * b + 1) * 2 ^ z.natAbs) := hevenPow.mul_left _
    have hodd : Odd ((2 * b + 1) * 2 ^ z.natAbs) := by
      rw [← hnat]
      exact ⟨a, rfl⟩
    exact (Nat.not_even_iff_odd.mpr hodd heven).elim

def lift (n : ℕ) (i : Fin n) : ℝ := log2 ((n + i.val : ℕ) : ℝ)

lemma lift_le (n : ℕ) {i j : Fin n} (hij : i ≤ j) : lift n i ≤ lift n j := by
  have hnat : n + i.val ≤ n + j.val := by omega
  have hposi : 0 < n + i.val := by omega
  have hposj : 0 < n + j.val := by omega
  exact (log2_le (by exact_mod_cast hposi) (by exact_mod_cast hposj)).2 (by exact_mod_cast hnat)

lemma lift_lt (n : ℕ) {i j : Fin n} (hij : i < j) : lift n i < lift n j := by
  have hnat : n + i.val < n + j.val := by omega
  have hposi : 0 < n + i.val := by omega
  exact log2_lt (by exact_mod_cast hposi) (by exact_mod_cast hnat)

lemma span_lt_one (n : ℕ) (hn : 0 < n) :
    lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩ < 1 := by
  have hpos : 0 < 2 * n - 1 := by omega
  unfold lift
  have h0 : (⟨0, hn⟩ : Fin n).val = 0 := rfl
  have hlast : (⟨n - 1, by omega⟩ : Fin n).val = n - 1 := rfl
  rw [h0, hlast, Nat.add_zero]
  have hsum : (n + (n - 1) : ℕ) = 2 * n - 1 := by omega
  rw [hsum]
  rw [log2_sub (by exact_mod_cast hpos) (by exact_mod_cast hn), ← log2_two]
  refine log2_lt (div_pos (by exact_mod_cast hpos) (by exact_mod_cast hn)) ?_
  rw [div_lt_iff₀ (by exact_mod_cast hn)]
  norm_cast
  omega

def g (n : ℕ) (hn : 0 < n) (i : Fin n) : ℝ :=
  lift n i - Int.floor (lift n ⟨0, hn⟩)

lemma g_sub (n : ℕ) (hn : 0 < n) (i j : Fin n) :
    g n hn i - g n hn j = lift n i - lift n j := by
  unfold g
  ring

lemma g_zero (n : ℕ) (hn : 0 < n) :
    g n hn ⟨0, hn⟩ = Int.fract (lift n ⟨0, hn⟩) := by
  unfold g Int.fract
  rfl

lemma g_nonneg (n : ℕ) (hn : 0 < n) (i : Fin n) : 0 ≤ g n hn i := by
  have h0 : 0 ≤ g n hn ⟨0, hn⟩ := by
    rw [g_zero]
    exact Int.fract_nonneg _
  have hdiff : 0 ≤ g n hn i - g n hn ⟨0, hn⟩ := by
    rw [g_sub]
    exact sub_nonneg.mpr (lift_le n (Fin.mk_le_mk.mpr (Nat.zero_le _)))
  linarith

lemma g_lt_two (n : ℕ) (hn : 0 < n) (i : Fin n) : g n hn i < 2 := by
  have hle : lift n i ≤ lift n ⟨n - 1, by omega⟩ :=
    lift_le n (Fin.mk_le_mk.mpr (by omega))
  have hspan := span_lt_one n hn
  have hf : Int.fract (lift n ⟨0, hn⟩) < 1 := Int.fract_lt_one _
  have hupper : g n hn i ≤ lift n ⟨n - 1, by omega⟩ - Int.floor (lift n ⟨0, hn⟩) := by
    unfold g
    linarith
  have hrewrite : lift n ⟨n - 1, by omega⟩ - Int.floor (lift n ⟨0, hn⟩) =
      (lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩) + Int.fract (lift n ⟨0, hn⟩) := by
    unfold Int.fract
    ring
  linarith

lemma fract_of_g (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Int.fract (lift n i) = g n hn i - (if 1 ≤ g n hn i then 1 else 0) := by
  have hfr : Int.fract (lift n i) = Int.fract (g n hn i) := by
    simp [g, Int.fract_sub_intCast]
  rw [hfr]
  by_cases h : 1 ≤ g n hn i
  · have hfloor : Int.floor (g n hn i) = 1 := by
      rw [Int.floor_eq_iff]
      constructor
      · exact_mod_cast h
      · exact_mod_cast g_lt_two n hn i
    simp [h, Int.fract, hfloor]
  · have hlt : g n hn i < 1 := lt_of_not_ge h
    simp [h, Int.fract_eq_self.mpr ⟨g_nonneg n hn i, hlt⟩]

def gOf (n : ℕ) (hn : 0 < n) (i : ℕ) : ℝ :=
  if h : i < n then g n hn ⟨i, h⟩ else 0

lemma gOf_eq (n : ℕ) (hn : 0 < n) {i : ℕ} (hi : i < n) : gOf n hn i = g n hn ⟨i, hi⟩ := by
  simp [gOf, hi]

def cut (n : ℕ) (hn : 0 < n) : ℕ :=
  if h : ∃ i, i < n ∧ 1 ≤ gOf n hn i then Nat.find h else n

lemma cut_of_exists (n : ℕ) (hn : 0 < n) (hex : ∃ i, i < n ∧ 1 ≤ gOf n hn i) :
    cut n hn = Nat.find hex := by
  simp [cut, hex]

lemma cut_of_not (n : ℕ) (hn : 0 < n) (hnot : ¬ ∃ i, i < n ∧ 1 ≤ gOf n hn i) :
    cut n hn = n := by
  simp [cut, hnot]

lemma cut_le (n : ℕ) (hn : 0 < n) : cut n hn ≤ n := by
  by_cases hex : ∃ i, i < n ∧ 1 ≤ gOf n hn i
  · rw [cut_of_exists n hn hex]
    exact le_of_lt (Nat.find_spec hex).1
  · rw [cut_of_not n hn hex]

lemma g_lt_one_of_lt_cut (n : ℕ) (hn : 0 < n) {i : ℕ} (hi : i < cut n hn) (hin : i < n) :
    g n hn ⟨i, hin⟩ < 1 := by
  rw [← gOf_eq n hn hin]
  by_cases hle : 1 ≤ gOf n hn i
  · have hex : ∃ j, j < n ∧ 1 ≤ gOf n hn j := ⟨i, hin, hle⟩
    have hlefind : Nat.find hex ≤ i := Nat.find_le ⟨hin, hle⟩
    rw [← cut_of_exists n hn hex] at hlefind
    omega
  · exact lt_of_not_ge hle

lemma cut_pos (n : ℕ) (hn : 0 < n) : 1 ≤ cut n hn := by
  by_contra hlt
  have h0 : cut n hn = 0 := by omega
  by_cases hex : ∃ i, i < n ∧ 1 ≤ gOf n hn i
  · rw [cut_of_exists n hn hex] at h0
    have hspec := Nat.find_spec hex
    have hone : 1 ≤ g n hn ⟨0, hn⟩ := by
      simpa [gOf_eq n hn hn, h0] using hspec.2
    have hlt1 : g n hn ⟨0, hn⟩ < 1 := by
      rw [g_zero]
      exact Int.fract_lt_one _
    linarith
  · rw [cut_of_not n hn hex] at h0
    omega

lemma g_ge_one_of_cut_le (n : ℕ) (hn : 0 < n) {i : ℕ} (hi : cut n hn ≤ i) (hin : i < n) :
    1 ≤ g n hn ⟨i, hin⟩ := by
  have hex : ∃ j, j < n ∧ 1 ≤ gOf n hn j := by
    by_contra hnot
    have : cut n hn = n := cut_of_not n hn hnot
    omega
  have hfind : cut n hn = Nat.find hex := cut_of_exists n hn hex
  have hlt : Nat.find hex < n := (Nat.find_spec hex).1
  have hbase : 1 ≤ g n hn ⟨Nat.find hex, hlt⟩ := by
    simpa [gOf_eq n hn hlt] using (Nat.find_spec hex).2
  have hle : g n hn ⟨Nat.find hex, hlt⟩ ≤ g n hn ⟨i, hin⟩ := by
    rw [← sub_nonneg, g_sub]
    exact sub_nonneg.mpr (lift_le n (Fin.mk_le_mk.mpr (by
      rw [← hfind]
      omega)))
  linarith

def tauVal (n p i : ℕ) : ℕ := if i < n - p then p + i else i - (n - p)

lemma tauVal_lt {n p i : ℕ} (hp : p ≤ n) (hi : i < n) : tauVal n p i < n := by
  unfold tauVal
  by_cases h : i < n - p
  · simp [h]
    omega
  · simp [h]
    omega

def tau (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨tauVal n (cut n hn) i.val, tauVal_lt (cut_le n hn) i.isLt⟩

lemma tau_high {n : ℕ} (hn : 0 < n) {i : Fin n} (hi : i.val < n - cut n hn) :
    (tau n hn i).val = cut n hn + i.val := by
  simp [tau, tauVal, hi]

lemma tau_low {n : ℕ} (hn : 0 < n) {i : Fin n} (hi : n - cut n hn ≤ i.val) :
    (tau n hn i).val = i.val - (n - cut n hn) := by
  simp [tau, tauVal, hi]

lemma high_iff (n : ℕ) (hn : 0 < n) (i : Fin n) :
    i.val < n - cut n hn ↔ 1 ≤ g n hn (tau n hn i) := by
  constructor
  · intro hi
    have hval := tau_high hn hi
    have hlt : cut n hn + i.val < n := by
      have := tauVal_lt (cut_le n hn) i.isLt
      simp [tau, tauVal, hi] at this
      exact this
    rw [← hval] at hlt
    have : cut n hn ≤ (tau n hn i).val := by omega
    exact g_ge_one_of_cut_le n hn this (tau n hn i).isLt
  · intro hg
    by_contra hge
    have hlow : n - cut n hn ≤ i.val := by omega
    have hval := tau_low hn hlow
    have hlt : i.val - (n - cut n hn) < cut n hn := by
      have hle : i.val < n := i.isLt
      omega
    rw [← hval] at hlt
    have hglt := g_lt_one_of_lt_cut n hn hlt (tau n hn i).isLt
    linarith

lemma exIndex_lt (n : ℕ) (hn : 0 < n) (i : Fin n) :
    (oddPart (n + i.val) - 1) / 2 < n := by
  have hm : 0 < n + i.val := by omega
  obtain ⟨k, hk⟩ := oddPart_odd hm
  have hlt : oddPart (n + i.val) < 2 * n := by
    have hle := oddPart_le (n + i.val)
    have : n + i.val < 2 * n := by omega
    omega
  have hklt : k < n := by
    have : 2 * k + 1 < 2 * n := by rwa [← hk]
    omega
  have : (oddPart (n + i.val) - 1) / 2 = k := by
    rw [hk, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  omega

def exIndex (n : ℕ) (hn : 0 < n) (i : Fin n) : Fin n :=
  ⟨(oddPart (n + i.val) - 1) / 2, exIndex_lt n hn i⟩

lemma oddPart_eq_exIndex (n : ℕ) (hn : 0 < n) (i : Fin n) :
    oddPart (n + i.val) = 2 * (exIndex n hn i).val + 1 := by
  have hm : 0 < n + i.val := by omega
  simpa [exIndex] using oddPart_eq_two_mul_add_one hm

lemma exIndex_inj (n : ℕ) (hn : 0 < n) : Function.Injective (exIndex n hn) := by
  intro i j h
  apply Fin.ext
  have hi := oddPart_eq_exIndex n hn i
  have hj := oddPart_eq_exIndex n hn j
  have hodd : oddPart (n + i.val) = oddPart (n + j.val) := by rw [hi, hj, h]
  have := oddPart_inj (n := n) (a := n + i.val) (b := n + j.val)
    (by omega) (by omega) (by omega) (by omega) hodd
  omega

lemma fract_lift_ex (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Int.fract (lift n i) = Int.fract (ex (exIndex n hn i : ℕ)) := by
  have hm : 0 < n + i.val := by omega
  have hval := oddPart_mul (n + i.val)
  have hpos := oddPart_pos hm
  have hlog : log2 ((n + i.val : ℕ) : ℝ) =
      log2 (oddPart (n + i.val) : ℝ) + padicValNat 2 (n + i.val) := by
    have hcast : ((n + i.val : ℕ) : ℝ) =
        (oddPart (n + i.val) : ℝ) * (2 : ℝ) ^ padicValNat 2 (n + i.val) := by
      conv_lhs => rw [hval, Nat.mul_comm]
      exact cast_odd_mul_pow _ _
    rw [hcast]
    exact log2_mul_two_pow _ _ hpos
  have hk := oddPart_eq_exIndex n hn i
  have hnat : ((2 * (exIndex n hn i).val + 1 : ℕ) : ℝ) =
      2 * ((exIndex n hn i).val : ℝ) + 1 := by norm_cast
  rw [lift, hlog, Int.fract_add_natCast, hk, ex, hnat]

lemma pts_exIndex (n : ℕ) (hn : 0 < n) (i : Fin n) :
    pts ex n (exIndex n hn i) = Int.fract (lift n i) := by
  unfold pts
  exact (fract_lift_ex n hn i).symm

def repr (n : ℕ) (hn : 0 < n) (i : Fin n) : ℝ :=
  g n hn (tau n hn i) - (if i.val < n - cut n hn then 1 else 0)

lemma repr_eq_fract (n : ℕ) (hn : 0 < n) (i : Fin n) :
    Int.fract (lift n (tau n hn i)) = repr n hn i := by
  rw [fract_of_g n hn, repr]
  congr 1
  simp [high_iff n hn i]

lemma repr_mono (n : ℕ) (hn : 0 < n) : Monotone (repr n hn) := by
  intro a b hab
  rcases eq_or_lt_of_le hab with rfl | hab
  · rfl
  · by_cases ha : a.val < n - cut n hn <;> by_cases hb : b.val < n - cut n hn
    · have hta : (tau n hn a).val = cut n hn + a.val := tau_high hn ha
      have htb : (tau n hn b).val = cut n hn + b.val := tau_high hn hb
      have habv : (a : ℕ) < b := Fin.val_fin_lt.mpr hab
      have hlt : tau n hn a < tau n hn b := by
        rw [← Fin.val_fin_lt]
        simp [tau, tauVal, ha, hb]
        omega
      have hg : g n hn (tau n hn a) < g n hn (tau n hn b) := by
        rw [← sub_pos, g_sub]
        exact sub_pos.mpr (lift_lt n hlt)
      simp [repr, ha, hb]
      linarith
    · have hta : (tau n hn a).val = cut n hn + a.val := tau_high hn ha
      have hlast : cut n hn + a.val ≤ n - 1 := by
        have := a.isLt
        omega
      have hgle : g n hn (tau n hn a) ≤ g n hn ⟨n - 1, by omega⟩ := by
        rw [← sub_nonneg, g_sub]
        apply sub_nonneg.mpr
        apply lift_le n
        rw [← Fin.val_fin_le]
        simp [tau, tauVal, ha]
        omega
      have hclose : g n hn ⟨n - 1, by omega⟩ - 1 < g n hn ⟨0, hn⟩ := by
        have hdiff : g n hn ⟨n - 1, by omega⟩ - g n hn ⟨0, hn⟩ < 1 := by
          rw [g_sub]
          exact span_lt_one n hn
        linarith
      have hlow : n - cut n hn ≤ b.val := by omega
      have htb : (tau n hn b).val = b.val - (n - cut n hn) := tau_low hn hlow
      have h0le : g n hn ⟨0, hn⟩ ≤ g n hn (tau n hn b) := by
        rw [← sub_nonneg, g_sub]
        apply sub_nonneg.mpr
        apply lift_le n
        rw [← Fin.val_fin_le]
        simp [tau, tauVal, hb]
      simp [repr, ha, hb]
      linarith
    · have : b.val < a.val := by omega
      exact absurd hab (not_lt_of_ge (by omega))
    · have hlowA : n - cut n hn ≤ a.val := by omega
      have hlowB : n - cut n hn ≤ b.val := by omega
      have hta := tau_low hn hlowA
      have htb := tau_low hn hlowB
      have habv : (a : ℕ) < b := Fin.val_fin_lt.mpr hab
      have hlt : tau n hn a < tau n hn b := by
        rw [← Fin.val_fin_lt]
        simp [tau, tauVal, ha, hb, hlowA, hlowB]
        omega
      have hg : g n hn (tau n hn a) < g n hn (tau n hn b) := by
        rw [← sub_pos, g_sub]
        exact sub_pos.mpr (lift_lt n hlt)
      simp [repr, ha, hb]
      linarith

lemma tau_inj (n : ℕ) (hn : 0 < n) : Function.Injective (tau n hn) := by
  intro a b h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [tau, tauVal] at hval
  by_cases ha : a.val < n - cut n hn <;> by_cases hb : b.val < n - cut n hn <;>
    simp [ha, hb] at hval
  · omega
  · have : cut n hn + a.val ≥ cut n hn := by omega
    have : b.val - (n - cut n hn) < cut n hn := by
      have := b.isLt
      omega
    omega
  · have : cut n hn + b.val ≥ cut n hn := by omega
    have : a.val - (n - cut n hn) < cut n hn := by
      have := a.isLt
      omega
    omega
  · omega

lemma sorted_repr (n : ℕ) (hn : 0 < n) : sortedPoint ex n = repr n hn := by
  let f : Fin n → ℝ := fun i => Int.fract (lift n i)
  let hbij : Function.Bijective (exIndex n hn) :=
    ⟨exIndex_inj n hn, (Finite.injective_iff_surjective).mp (exIndex_inj n hn)⟩
  let phi : Equiv.Perm (Fin n) :=
    { toFun := exIndex n hn
      invFun := Function.surjInv hbij.2
      left_inv := Function.leftInverse_surjInv hbij
      right_inv := Function.rightInverse_surjInv hbij.2 }
  have hcomp : pts ex n ∘ phi = f := by
    ext i
    have hphi : phi i = exIndex n hn i := by
      dsimp [phi]
    simpa [f, hphi] using pts_exIndex n hn i
  have hsort := Tuple.comp_perm_comp_sort_eq_comp_sort (f := pts ex n) (σ := phi)
  have hsorted : f ∘ Tuple.sort f = sortedPoint ex n := by
    simpa [hcomp, sortedPoint] using hsort
  let hbijτ : Function.Bijective (tau n hn) :=
    ⟨tau_inj n hn, (Finite.injective_iff_surjective).mp (tau_inj n hn)⟩
  let tauE : Equiv.Perm (Fin n) :=
    { toFun := tau n hn
      invFun := Function.surjInv hbijτ.2
      left_inv := Function.leftInverse_surjInv hbijτ
      right_inv := Function.rightInverse_surjInv hbijτ.2 }
  have hrepr : f ∘ tauE = repr n hn := by
    ext i
    exact repr_eq_fract n hn i
  have hmono : Monotone (f ∘ tauE) := by
    simpa [hrepr] using repr_mono n hn
  have htau := (Tuple.comp_sort_eq_comp_iff_monotone (f := f) (σ := tauE)).mpr hmono
  ext i
  rw [← congrFun hsorted i, ← congrFun htau i, congrFun hrepr i]

def firstReal (n : ℕ) : ℝ := log2 (((n + 1 : ℕ) : ℝ) / (n : ℝ))

def closeReal (n : ℕ) : ℝ := log2 (((2 * n : ℕ) : ℝ) / ((2 * n - 1 : ℕ) : ℝ))

lemma lift_succ_sub (n : ℕ) (hn : 0 < n) (j : ℕ) (hj : j + 1 < n) :
    lift n ⟨j + 1, by omega⟩ - lift n ⟨j, by omega⟩ = firstReal (n + j) := by
  unfold lift firstReal
  have hjv : (⟨j, by omega⟩ : Fin n).val = j := rfl
  have hjs : (⟨j + 1, by omega⟩ : Fin n).val = j + 1 := rfl
  rw [hjv, hjs]
  have hsum : (n + (j + 1) : ℕ) = n + j + 1 := by omega
  rw [hsum]
  have hposj : 0 < n + j := by omega
  have hpos1 : 0 < n + j + 1 := by omega
  exact log2_sub (by exact_mod_cast hpos1) (by exact_mod_cast hposj)

lemma close_eq (n : ℕ) (hn : 0 < n) :
    1 - (lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩) = closeReal n := by
  have hpos : 0 < 2 * n - 1 := by omega
  unfold lift closeReal
  have h0 : (⟨0, hn⟩ : Fin n).val = 0 := rfl
  have hlast : (⟨n - 1, by omega⟩ : Fin n).val = n - 1 := rfl
  rw [h0, hlast, Nat.add_zero]
  have hsum : (n + (n - 1) : ℕ) = 2 * n - 1 := by omega
  rw [hsum, log2_sub (by exact_mod_cast hpos) (by exact_mod_cast hn), ← log2_two]
  rw [log2_sub (by norm_num) (div_pos (by exact_mod_cast hpos) (by exact_mod_cast hn))]
  congr 1
  field_simp
  norm_cast

lemma ratio_anti {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    firstReal b ≤ firstReal a := by
  unfold firstReal
  have hb : 0 < b := by omega
  have hposb : (0 : ℝ) < ((b + 1 : ℕ) : ℝ) / b :=
    div_pos (by exact_mod_cast (show 0 < b + 1 by omega)) (by exact_mod_cast hb)
  have hposa : (0 : ℝ) < ((a + 1 : ℕ) : ℝ) / a :=
    div_pos (by exact_mod_cast (show 0 < a + 1 by omega)) (by exact_mod_cast ha)
  rw [log2_le hposb hposa, div_le_div_iff₀ (by exact_mod_cast hb) (by exact_mod_cast ha)]
  have hnat : (b + 1) * a ≤ (a + 1) * b := by
    calc
      (b + 1) * a = a * b + a := by ring
      _ ≤ a * b + b := Nat.add_le_add_left hab _
      _ = (a + 1) * b := by ring
  exact_mod_cast hnat

lemma ratio_in_range {n m : ℕ} (hn : 0 < n) (hm0 : n ≤ m) (hm1 : m < 2 * n) :
    closeReal n ≤ firstReal m ∧ firstReal m ≤ firstReal n := by
  refine ⟨?_, ratio_anti hn hm0⟩
  have hmle : m ≤ 2 * n - 1 := by omega
  have : firstReal (2 * n - 1) ≤ firstReal m := ratio_anti (by omega) hmle
  have hclose : closeReal n = firstReal (2 * n - 1) := by
    unfold closeReal firstReal
    have hnum : ((2 * n : ℕ) : ℝ) = (((2 * n - 1) + 1 : ℕ) : ℝ) := by
      norm_cast
      omega
    rw [hnum]
  linarith

lemma rSpan_of_lt (n : ℕ) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n) :
    rSpan ex n 1 i =
      sortedPoint ex n ⟨i.val + 1, h⟩ - sortedPoint ex n i := by
  have h1 := GapBig.unrolled_eq ex (0 : ℕ) h
  have h0 := GapBig.unrolled_eq ex (0 : ℕ) i.isLt
  have e1 : unrolled ex n ((i : ℕ) + 1) = sortedPoint ex n ⟨(i : ℕ) + 1, h⟩ := by
    simpa using h1
  have e0 : unrolled ex n (i : ℕ) = sortedPoint ex n i := by
    simpa using h0
  rw [rSpan, e0, e1]

lemma rSpan_of_last (n : ℕ) (hn : 0 < n) :
    rSpan ex n 1 (n - 1) =
      sortedPoint ex n ⟨0, hn⟩ + 1 - sortedPoint ex n ⟨n - 1, by omega⟩ := by
  have h0 := GapBig.unrolled_eq ex (1 : ℕ) hn
  have h1 := GapBig.unrolled_eq ex (0 : ℕ) (by omega : n - 1 < n)
  have e0 : unrolled ex n n = sortedPoint ex n ⟨0, hn⟩ + 1 := by
    simpa using h0
  have e1 : unrolled ex n (n - 1) = sortedPoint ex n ⟨n - 1, by omega⟩ := by
    simpa using h1
  have hn1 : (n - 1) + 1 = n := by omega
  rw [rSpan, hn1, e0, e1]

lemma repr_succ_sub (n : ℕ) (hn : 0 < n) (i : Fin n) (h : i.val + 1 < n) :
    ∃ m, n ≤ m ∧ m < 2 * n ∧
      repr n hn ⟨i.val + 1, h⟩ - repr n hn i = firstReal m := by
  by_cases ha : i.val < n - cut n hn
  · by_cases hb : i.val + 1 < n - cut n hn
    · refine ⟨n + cut n hn + i.val, by omega, ?_, ?_⟩
      · have htau : cut n hn + i.val < n := by omega
        omega
      · have hta := tau_high hn ha
        have htb := tau_high hn (by omega : (⟨i.val + 1, h⟩ : Fin n).val < n - cut n hn)
        simp only [repr, ha, hb, if_true, if_false, sub_zero]
        have hidx : (tau n hn ⟨i.val + 1, h⟩).val = (tau n hn i).val + 1 := by
          simp [tau, tauVal, ha, hb]
          omega
        have hlt : (tau n hn i).val + 1 < n := by
          simpa [hidx] using (tau n hn ⟨i.val + 1, h⟩).isLt
        calc
          (g n hn (tau n hn ⟨i.val + 1, h⟩) - 1) - (g n hn (tau n hn i) - 1) =
              g n hn (tau n hn ⟨i.val + 1, h⟩) - g n hn (tau n hn i) := by ring
          _ = lift n ⟨(tau n hn i).val + 1, hlt⟩ - lift n ⟨(tau n hn i).val, by omega⟩ := by
            rw [g_sub]
            rw [show tau n hn ⟨i.val + 1, h⟩ = ⟨(tau n hn i).val + 1, hlt⟩ from
              Fin.ext (by simpa [hidx])]
          _ = firstReal (n + (tau n hn i).val) := lift_succ_sub n hn _ hlt
          _ = firstReal (n + cut n hn + i.val) := by
            congr 1
            omega
    · have hcross : i.val + 1 = n - cut n hn := by omega
      refine ⟨2 * n - 1, by omega, by omega, ?_⟩
      have hi1 : (⟨i.val + 1, h⟩ : Fin n).val = n - cut n hn := hcross
      have hta := tau_high hn ha
      have htb := tau_low hn (by omega : n - cut n hn ≤ (⟨i.val + 1, h⟩ : Fin n).val)
      simp only [repr, ha, hi1, show ¬ i.val + 1 < n - cut n hn from hb, if_true, if_false,
        sub_zero]
      have htauLast : (tau n hn i).val = n - 1 := by
        rw [hta]
        omega
      have htau0 : (tau n hn ⟨i.val + 1, h⟩).val = 0 := by
        rw [htb, hi1]
        omega
      calc
        g n hn (tau n hn ⟨i.val + 1, h⟩) - (g n hn (tau n hn i) - 1) =
            g n hn ⟨0, hn⟩ - (g n hn ⟨n - 1, by omega⟩ - 1) := by
          rw [show tau n hn ⟨i.val + 1, h⟩ = ⟨0, hn⟩ from Fin.ext htau0]
          rw [show tau n hn i = ⟨n - 1, by omega⟩ from Fin.ext htauLast]
        _ = 1 - (g n hn ⟨n - 1, by omega⟩ - g n hn ⟨0, hn⟩) := by ring
        _ = 1 - (lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩) := by rw [g_sub]
        _ = closeReal n := close_eq n hn
        _ = firstReal (2 * n - 1) := by
          unfold closeReal firstReal
          have hnum : ((2 * n : ℕ) : ℝ) = (((2 * n - 1) + 1 : ℕ) : ℝ) := by
            norm_cast
            omega
          rw [hnum]
  · have hlow : n - cut n hn ≤ i.val := by omega
    have hlow1 : n - cut n hn ≤ i.val + 1 := by omega
    refine ⟨n + (i.val - (n - cut n hn)), ?_, ?_, ?_⟩
    · omega
    · have : i.val - (n - cut n hn) < n := by omega
      omega
    · have hta := tau_low hn hlow
      have htb := tau_low hn (by omega : n - cut n hn ≤ (⟨i.val + 1, h⟩ : Fin n).val)
      have hnot1 : ¬ i.val + 1 < n - cut n hn := by omega
      simp only [repr, if_neg ha, if_neg hnot1, sub_zero]
      have hidx : (tau n hn ⟨i.val + 1, h⟩).val = (tau n hn i).val + 1 := by
        rw [hta, htb]
        have hsub : i.val + 1 - (n - cut n hn) = i.val - (n - cut n hn) + 1 := by
          omega
        -- the Fin values are those subtractions
        simp [hsub]
      have hlt : (tau n hn i).val + 1 < n := by
        simpa [hidx] using (tau n hn ⟨i.val + 1, h⟩).isLt
      calc
        g n hn (tau n hn ⟨i.val + 1, h⟩) - g n hn (tau n hn i) =
            lift n ⟨(tau n hn i).val + 1, hlt⟩ - lift n ⟨(tau n hn i).val, by omega⟩ := by
          rw [g_sub]
          rw [show tau n hn ⟨i.val + 1, h⟩ = ⟨(tau n hn i).val + 1, hlt⟩ from
            Fin.ext (by simpa [hidx])]
        _ = firstReal (n + (tau n hn i).val) := lift_succ_sub n hn _ hlt
        _ = firstReal (n + (i.val - (n - cut n hn))) := by simp [hta]

lemma repr_wrap (n : ℕ) (hn : 0 < n) :
    ∃ m, n ≤ m ∧ m < 2 * n ∧
      repr n hn ⟨0, hn⟩ + 1 - repr n hn ⟨n - 1, by omega⟩ = firstReal m := by
  by_cases hcut : cut n hn = n
  · refine ⟨2 * n - 1, by omega, by omega, ?_⟩
    have hm : n - cut n hn = 0 := by omega
    simp only [repr, hm, Nat.not_lt_zero, if_false, sub_zero]
    have h0 : (tau n hn ⟨0, hn⟩).val = 0 := by simp [tau, tauVal, hm]
    have h1 : (tau n hn ⟨n - 1, by omega⟩).val = n - 1 := by simp [tau, tauVal, hm]
    calc
      g n hn (tau n hn ⟨0, hn⟩) + 1 - g n hn (tau n hn ⟨n - 1, by omega⟩) =
          g n hn ⟨0, hn⟩ + 1 - g n hn ⟨n - 1, by omega⟩ := by
        rw [show tau n hn ⟨0, hn⟩ = ⟨0, hn⟩ from Fin.ext h0]
        rw [show tau n hn ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ from Fin.ext h1]
      _ = 1 - (g n hn ⟨n - 1, by omega⟩ - g n hn ⟨0, hn⟩) := by ring
      _ = 1 - (lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩) := by rw [g_sub]
      _ = closeReal n := close_eq n hn
      _ = firstReal (2 * n - 1) := by
        unfold closeReal firstReal
        have hnum : ((2 * n : ℕ) : ℝ) = (((2 * n - 1) + 1 : ℕ) : ℝ) := by
          norm_cast
          omega
        rw [hnum]
  · have hpos : 1 ≤ cut n hn := cut_pos n hn
    have hmpos : 0 < n - cut n hn := by have := cut_le n hn; omega
    refine ⟨n + cut n hn - 1, by omega, by omega, ?_⟩
    have h0high : (0 : ℕ) < n - cut n hn := hmpos
    have hlastlow : n - cut n hn ≤ n - 1 := by omega
    simp only [repr, h0high, show ¬ n - 1 < n - cut n hn from by omega, if_true, if_false,
      sub_zero]
    have htau0 : (tau n hn ⟨0, hn⟩).val = cut n hn := by
      simp [tau, tauVal, h0high]
    have htaul : (tau n hn ⟨n - 1, by omega⟩).val = cut n hn - 1 := by
      simp [tau, tauVal, show ¬ n - 1 < n - cut n hn from by omega]
      omega
    have hlt : cut n hn - 1 + 1 < n := by omega
    calc
      (g n hn (tau n hn ⟨0, hn⟩) - 1) + 1 - g n hn (tau n hn ⟨n - 1, by omega⟩) =
          (g n hn ⟨cut n hn, by omega⟩ - 1) + 1 - g n hn ⟨cut n hn - 1, by omega⟩ := by
        rw [show tau n hn ⟨0, hn⟩ = ⟨cut n hn, by omega⟩ from Fin.ext htau0]
        rw [show tau n hn ⟨n - 1, by omega⟩ = ⟨cut n hn - 1, by omega⟩ from Fin.ext htaul]
      _ = g n hn ⟨cut n hn, by omega⟩ - g n hn ⟨cut n hn - 1, by omega⟩ := by ring
      _ = g n hn ⟨cut n hn - 1 + 1, hlt⟩ - g n hn ⟨cut n hn - 1, by omega⟩ := by
        have hsucc : (⟨cut n hn - 1 + 1, hlt⟩ : Fin n) = ⟨cut n hn, by omega⟩ := by
          apply Fin.ext
          simp
          omega
        rw [hsucc]
      _ = lift n ⟨cut n hn - 1 + 1, hlt⟩ - lift n ⟨cut n hn - 1, by omega⟩ := by rw [g_sub]
      _ = firstReal (n + (cut n hn - 1)) := lift_succ_sub n hn _ hlt
      _ = firstReal (n + cut n hn - 1) := by
        congr 1
        omega

lemma rSpan_is_first (n : ℕ) (hn : 0 < n) (i : Fin n) :
    ∃ m, n ≤ m ∧ m < 2 * n ∧ rSpan ex n 1 i = firstReal m := by
  by_cases hlast : i.val + 1 < n
  · obtain ⟨m, hm0, hm1, hm⟩ := repr_succ_sub n hn i hlast
    refine ⟨m, hm0, hm1, ?_⟩
    rw [rSpan_of_lt n hn i hlast, sorted_repr n hn]
    exact hm
  · have hidx : i.val = n - 1 := by omega
    obtain ⟨m, hm0, hm1, hm⟩ := repr_wrap n hn
    refine ⟨m, hm0, hm1, ?_⟩
    rw [show (i : ℕ) = n - 1 from hidx, rSpan_of_last n hn, sorted_repr n hn]
    exact hm

lemma exists_first (n : ℕ) (hn : 0 < n) : ∃ i : Fin n, rSpan ex n 1 i = firstReal n := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨⟨0, by decide⟩, ?_⟩
    have hr := rSpan_of_last 1 (by decide)
    simp at hr
    rw [hr]
    ring
    unfold firstReal
    simp [log2_two]
  by_cases hcut : cut n hn = n
  · have hlt : 0 + 1 < n := by omega
    refine ⟨⟨0, hn⟩, ?_⟩
    rw [rSpan_of_lt n hn ⟨0, hn⟩ hlt, sorted_repr n hn]
    have hm : n - cut n hn = 0 := by omega
    simp only [repr, hm, Nat.not_lt_zero, if_false, sub_zero]
    have h0 : (tau n hn ⟨0, hn⟩).val = 0 := by simp [tau, tauVal, hm]
    have h1 : (tau n hn ⟨1, hlt⟩).val = 1 := by simp [tau, tauVal, hm]
    calc
      g n hn (tau n hn ⟨1, hlt⟩) - g n hn (tau n hn ⟨0, hn⟩) =
          g n hn ⟨1, hlt⟩ - g n hn ⟨0, hn⟩ := by
        rw [show tau n hn ⟨1, hlt⟩ = ⟨1, hlt⟩ from Fin.ext h1]
        rw [show tau n hn ⟨0, hn⟩ = ⟨0, hn⟩ from Fin.ext h0]
      _ = lift n ⟨1, hlt⟩ - lift n ⟨0, hn⟩ := by rw [g_sub]
      _ = firstReal n := by
        simpa using lift_succ_sub n hn 0 hlt
  · by_cases hone : cut n hn = 1
    · refine ⟨⟨n - 1, by omega⟩, ?_⟩
      rw [rSpan_of_last n hn, sorted_repr n hn]
      -- the wrap equals firstReal (n + cut - 1) = firstReal n
      have hpos : 1 ≤ cut n hn := hone.symm ▸ by omega
      have hmpos : 0 < n - cut n hn := by have := cut_le n hn; omega
      have h0high : (0 : ℕ) < n - cut n hn := hmpos
      simp only [repr, h0high, show ¬ n - 1 < n - cut n hn from by omega, if_true, if_false, sub_zero]
      have htau0 : (tau n hn ⟨0, hn⟩).val = cut n hn := by simp [tau, tauVal, h0high]
      have htaul : (tau n hn ⟨n - 1, by omega⟩).val = cut n hn - 1 := by
        simp [tau, tauVal, show ¬ n - 1 < n - cut n hn from by omega]
        omega
      have hlt : cut n hn - 1 + 1 < n := by omega
      calc
        (g n hn (tau n hn ⟨0, hn⟩) - 1) + 1 - g n hn (tau n hn ⟨n - 1, by omega⟩) =
            g n hn ⟨1, by omega⟩ - g n hn ⟨0, hn⟩ := by
          rw [show tau n hn ⟨0, hn⟩ = ⟨1, by omega⟩ from Fin.ext (by simpa [htau0, hone])]
          rw [show tau n hn ⟨n - 1, by omega⟩ = ⟨0, hn⟩ from Fin.ext (by simpa [htaul, hone])]
          ring
        _ = lift n ⟨1, by omega⟩ - lift n ⟨0, hn⟩ := by rw [g_sub]
        _ = firstReal n := by
          have h1 : 1 < n := by
            have hne : n ≠ 1 := by
              rintro rfl
              exact hcut hone
            omega
          simpa using lift_succ_sub n hn 0 h1
    · have hge : 2 ≤ cut n hn := by have := cut_pos n hn; omega
      refine ⟨⟨n - cut n hn, by omega⟩, ?_⟩
      have hlt : n - cut n hn + 1 < n := by omega
      rw [rSpan_of_lt n hn ⟨n - cut n hn, by omega⟩ hlt, sorted_repr n hn]
      have hlow0 : n - cut n hn ≤ (⟨n - cut n hn, by omega⟩ : Fin n).val := by
        simp [Fin.val_mk]
      have hlow1 : n - cut n hn ≤ (⟨n - cut n hn + 1, hlt⟩ : Fin n).val := by
        simp [Fin.val_mk]
      have hnot0 : ¬ (⟨n - cut n hn, by omega⟩ : Fin n).val < n - cut n hn := by
        simp [Fin.val_mk]
      have hnot1 : ¬ (⟨n - cut n hn + 1, hlt⟩ : Fin n).val < n - cut n hn := by
        simp [Fin.val_mk]
      simp only [repr, if_neg hnot0, if_neg hnot1, sub_zero]
      have hta := tau_low hn hlow0
      have htb := tau_low hn hlow1
      calc
        g n hn (tau n hn ⟨n - cut n hn + 1, hlt⟩) - g n hn (tau n hn ⟨n - cut n hn, by omega⟩) =
            g n hn ⟨1, by omega⟩ - g n hn ⟨0, hn⟩ := by
          have h0 : (tau n hn ⟨n - cut n hn, by omega⟩).val = 0 := by
            rw [hta]
            simp [Fin.val_mk]
          have h1 : (tau n hn ⟨n - cut n hn + 1, hlt⟩).val = 1 := by
            rw [htb]
            simp [Fin.val_mk]
          rw [show tau n hn ⟨n - cut n hn, by omega⟩ = ⟨0, hn⟩ from Fin.ext h0]
          rw [show tau n hn ⟨n - cut n hn + 1, hlt⟩ = ⟨1, by omega⟩ from Fin.ext h1]
        _ = lift n ⟨1, by omega⟩ - lift n ⟨0, hn⟩ := by rw [g_sub]
        _ = firstReal n := by
          have hle := cut_le n hn
          have h1 : 1 < n := by omega
          simpa using lift_succ_sub n hn 0 h1

lemma exists_close (n : ℕ) (hn : 0 < n) : ∃ i : Fin n, rSpan ex n 1 i = closeReal n := by
  by_cases hcut : cut n hn = n
  · refine ⟨⟨n - 1, by omega⟩, ?_⟩
    rw [rSpan_of_last n hn, sorted_repr n hn]
    have hm : n - cut n hn = 0 := by omega
    simp only [repr, hm, Nat.not_lt_zero, if_false, sub_zero]
    have h0 : (tau n hn ⟨0, hn⟩).val = 0 := by simp [tau, tauVal, hm]
    have h1 : (tau n hn ⟨n - 1, by omega⟩).val = n - 1 := by simp [tau, tauVal, hm]
    calc
      g n hn (tau n hn ⟨0, hn⟩) + 1 - g n hn (tau n hn ⟨n - 1, by omega⟩) =
          g n hn ⟨0, hn⟩ + 1 - g n hn ⟨n - 1, by omega⟩ := by
        rw [show tau n hn ⟨0, hn⟩ = ⟨0, hn⟩ from Fin.ext h0]
        rw [show tau n hn ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ from Fin.ext h1]
      _ = 1 - (g n hn ⟨n - 1, by omega⟩ - g n hn ⟨0, hn⟩) := by ring
      _ = 1 - (lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩) := by rw [g_sub]
      _ = closeReal n := close_eq n hn
  · have hc : cut n hn < n := lt_of_le_of_ne (cut_le n hn) hcut
    have hpos : 0 < n - cut n hn := Nat.sub_pos_of_lt hc
    have hj : n - cut n hn - 1 < n := by omega
    have hlt : (n - cut n hn - 1) + 1 < n := by
      rw [Nat.sub_add_cancel hpos]
      exact Nat.sub_lt hn (cut_pos n hn)
    let i : Fin n := ⟨n - cut n hn - 1, hj⟩
    have ha : (i : ℕ) < n - cut n hn := by
      have : (i : ℕ) = n - cut n hn - 1 := by simp [i, Fin.val_mk]
      omega
    have hb : ¬ (i : ℕ) + 1 < n - cut n hn := by
      have : (i : ℕ) = n - cut n hn - 1 := by simp [i, Fin.val_mk]
      omega
    refine ⟨i, ?_⟩
    rw [rSpan_of_lt n hn i (by simpa [i, Fin.val_mk] using hlt), sorted_repr n hn]
    have hcross : (i : ℕ) + 1 = n - cut n hn := by
      have : (i : ℕ) = n - cut n hn - 1 := by simp [i, Fin.val_mk]
      omega
    have hi1 : (⟨(i : ℕ) + 1, by simpa [i, Fin.val_mk] using hlt⟩ : Fin n).val = n - cut n hn := by
      simp [Fin.val_mk, hcross]
    have hta := tau_high hn (by simpa [Fin.val_mk] using ha)
    have htb := tau_low hn (show n - cut n hn ≤
        (⟨(i : ℕ) + 1, by simpa [i, Fin.val_mk] using hlt⟩ : Fin n).val from by
      rw [Fin.val_mk]
      exact le_of_eq hcross.symm)
    simp only [repr, ha, hb, if_true, if_false, sub_zero]
    have htauLast : (tau n hn i).val = n - 1 := by
      rw [hta]
      simp [i, Fin.val_mk]
      omega
    have htau0 : (tau n hn ⟨(i : ℕ) + 1, by simpa [i, Fin.val_mk] using hlt⟩).val = 0 := by
      rw [htb]
      simp [Fin.val_mk, hcross]
    calc
      g n hn (tau n hn ⟨i.val + 1, hlt⟩) - (g n hn (tau n hn i) - 1) =
          g n hn ⟨0, hn⟩ - (g n hn ⟨n - 1, by omega⟩ - 1) := by
        rw [show tau n hn ⟨i.val + 1, hlt⟩ = ⟨0, hn⟩ from Fin.ext htau0]
        rw [show tau n hn i = ⟨n - 1, by omega⟩ from Fin.ext htauLast]
      _ = 1 - (g n hn ⟨n - 1, by omega⟩ - g n hn ⟨0, hn⟩) := by ring
      _ = 1 - (lift n ⟨n - 1, by omega⟩ - lift n ⟨0, hn⟩) := by rw [g_sub]
      _ = closeReal n := close_eq n hn

lemma rSpan_bounded (n : ℕ) (hn : 0 < n) (i : Fin n) :
    closeReal n ≤ rSpan ex n 1 i ∧ rSpan ex n 1 i ≤ firstReal n := by
  obtain ⟨m, hm0, hm1, hm⟩ := rSpan_is_first n hn i
  have h := ratio_in_range hn hm0 hm1
  have hclose : closeReal n = firstReal (2 * n - 1) := by
    unfold closeReal firstReal
    have hnum : ((2 * n : ℕ) : ℝ) = (((2 * n - 1) + 1 : ℕ) : ℝ) := by
      norm_cast
      omega
    rw [hnum]
  rw [hclose] at h
  rw [hm, hclose]
  exact h

lemma maxSpan_eq (n : ℕ) (hn : 0 < n) : maxSpan ex n 1 = firstReal n := by
  obtain ⟨i, hi⟩ := exists_first n hn
  apply le_antisymm
  · unfold maxSpan
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine ciSup_le fun j => (rSpan_bounded n hn j).2
  · unfold maxSpan
    have := le_ciSup (Set.finite_range fun j : Fin n => rSpan ex n 1 j).bddAbove i
    simpa [hi] using this

lemma minSpan_eq (n : ℕ) (hn : 0 < n) : minSpan ex n 1 = closeReal n := by
  obtain ⟨i, hi⟩ := exists_close n hn
  apply le_antisymm
  · unfold minSpan
    have := ciInf_le (Set.finite_range fun j : Fin n => rSpan ex n 1 j).bddBelow i
    simpa [hi] using this
  · unfold minSpan
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine le_ciInf fun j => (rSpan_bounded n hn j).1

lemma tendsto_n_first :
    Tendsto (fun n : ℕ => (n : ℝ) * firstReal n) atTop (nhds (1 / Real.log 2)) := by
  have hlog : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + 1 / (n : ℝ))) atTop (nhds 1) := by
    refine Real.tendsto_nat_mul_log_one_add_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    simp [Nat.ne_of_gt hn]
  refine (hlog.div_const (Real.log 2)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  unfold firstReal log2
  have hratio : ((n + 1 : ℕ) : ℝ) / n = 1 + 1 / (n : ℝ) := by
    field_simp [Nat.ne_of_gt hn]
    norm_cast
  rw [hratio]
  ring

lemma tendsto_n_close :
    Tendsto (fun n : ℕ => (n : ℝ) * closeReal n) atTop (nhds (1 / Real.log 4)) := by
  have hden : Tendsto (fun n : ℕ => 2 * (n : ℝ) - 1) atTop atTop := by
    have hmul : Tendsto (fun n : ℕ => (2 : ℝ) * n) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)
    have := hmul.atTop_add (tendsto_const_nhds (x := (-1 : ℝ)))
    simpa [sub_eq_add_neg, mul_comm] using this
  have hmul := (Real.tendsto_mul_log_one_add_div_atTop (1 : ℝ)).comp hden
  have hcoef : Tendsto (fun n : ℕ => (n : ℝ) / (2 * (n : ℝ) - 1)) atTop (nhds ((1 : ℝ) / 2)) := by
    have hrewrite : ∀ᶠ n : ℕ in atTop, (n : ℝ) / (2 * (n : ℝ) - 1) = 1 / (2 - 1 / (n : ℝ)) := by
      filter_upwards [eventually_gt_atTop 0] with n hn
      field_simp [Nat.ne_of_gt hn]
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have hsub : Tendsto (fun n : ℕ => (2 : ℝ) - 1 / n) atTop (nhds 2) := by
      simpa using (tendsto_const_nhds.sub hone :
        Tendsto (fun n : ℕ => (2 : ℝ) - 1 / (n : ℝ)) atTop (nhds (2 - 0)))
    have hinv : Tendsto (fun n : ℕ => 1 / (2 - 1 / (n : ℝ))) atTop (nhds (1 / 2)) :=
      tendsto_const_nhds.div hsub (by norm_num)
    exact hinv.congr' (Filter.EventuallyEq.symm hrewrite)
  have hprod : Tendsto (fun n : ℕ => (n : ℝ) * Real.log (1 + 1 / (2 * (n : ℝ) - 1))) atTop
      (nhds ((1 : ℝ) / 2 * 1)) := by
    have := hcoef.mul hmul
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : (2 * (n : ℝ) - 1) ≠ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [Function.comp_apply]
    calc
      (n : ℝ) / (2 * n - 1) * ((2 * n - 1) * Real.log (1 + 1 / (2 * n - 1))) =
          ((n : ℝ) / (2 * n - 1) * (2 * n - 1)) * Real.log (1 + 1 / (2 * n - 1)) := by ring
      _ = (n : ℝ) * Real.log (1 + 1 / (2 * n - 1)) := by rw [div_mul_cancel₀ _ hne]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlim : ((1 : ℝ) / 2 * 1) / Real.log 2 = 1 / Real.log 4 := by
    rw [h4]
    field_simp [log_two_pos.ne']
  rw [← hlim]
  refine (hprod.div_const (Real.log 2)).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  unfold closeReal log2
  have hratio : 1 + 1 / (2 * (n : ℝ) - 1) = ((2 * n : ℕ) : ℝ) / ((2 * n - 1 : ℕ) : ℝ) := by
    have hden : 2 * (n : ℝ) - 1 = ((2 * n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n), Nat.cast_mul]
      norm_num
    rw [hden, one_add_div]
    · have ha : ((2 * n - 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (show 2 * n - 1 ≠ 0 by omega)
      have hsucc : ((2 * n - 1 : ℕ) : ℝ) + 1 = ((2 * n : ℕ) : ℝ) := by
        norm_cast
        omega
      field_simp [ha]
      rw [← hsucc]
    · exact_mod_cast (show 2 * n - 1 ≠ 0 by omega)
  rw [← hratio]
  ring


end Witness

open ENNReal Witness

theorem OMA.solution : type_of% @Erdos1221.erdos_1221.variants.r_one := by
  have hmax : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * maxSpan ex n 1)) atTop
      (nhds (ENNReal.ofReal (1 / Real.log 2))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine tendsto_n_first.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    simp [maxSpan_eq n hn0]
  have hmin : Tendsto (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * minSpan ex n 1)) atTop
      (nhds (ENNReal.ofReal (1 / Real.log 4))) := by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    refine tendsto_n_close.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    simp [minSpan_eq n hn0]
  have hratio : Tendsto (fun n : ℕ => maxSpan ex n 1 / minSpan ex n 1) atTop (nhds 2) := by
    have hdiv := tendsto_n_first.div tendsto_n_close
      (div_pos one_pos (Real.log_pos (by norm_num))).ne'
    have hconst : (1 / Real.log 2) / (1 / Real.log 4) = 2 := by
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      rw [h4]
      field_simp [log_two_pos.ne']
    rw [hconst] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have hn0' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn0)
    rw [Pi.div_apply]
    field_simp [hn0']
    rw [maxSpan_eq n hn0, minSpan_eq n hn0]
  have hmu : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (maxSpan ex n 1) / ENNReal.ofReal (minSpan ex n 1)) atTop (nhds 2) := by
    have hcast : ENNReal.ofReal 2 = 2 := ENNReal.ofReal_ofNat 2
    rw [← hcast]
    refine ((ENNReal.continuous_ofReal.tendsto _).comp hratio).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : 0 < n := by omega
    have hpos : 0 < minSpan ex n 1 := by
      rw [minSpan_eq n hn0, closeReal, log2]
      have hgt : (1 : ℝ) < ((2 * n : ℕ) : ℝ) / ((2 * n - 1 : ℕ) : ℝ) := by
        rw [one_lt_div (by exact_mod_cast (show 0 < 2 * n - 1 by omega))]
        norm_cast
        omega
      exact div_pos (Real.log_pos hgt) log_two_pos
    simp [Function.comp_apply, ENNReal.ofReal_div_of_pos hpos]
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · have hle : bigLambda 1 ≤
          limsup (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * maxSpan ex n 1)) atTop := by
        simpa [bigLambda] using iInf₂_le ex ex_inj
      rwa [hmax.limsup_eq] at hle
    · have hge := big_ge 1 (by decide)
      have h2 : (1 : ℝ) + 1 / (1 : ℕ) = 2 := by norm_num
      rw [h2] at hge
      exact hge
  · apply le_antisymm
    · have hle := small_le 1 (by decide)
      have hsum : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
      have hdiv : (1 : ℝ) + 1 / (1 : ℕ) = 2 := by norm_num
      rw [hsum, hdiv] at hle
      have h4 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      have hconst : ((1 : ℕ) : ℝ) / 2 * (1 / Real.log 2) = 1 / Real.log 4 := by
        rw [h4]
        field_simp [log_two_pos.ne']
        norm_num
      rw [hconst] at hle
      exact hle
    · have hge : ENNReal.ofReal (1 / Real.log 4) ≤ smallLambda 1 := by
        have hliminf := hmin.liminf_eq
        unfold smallLambda
        rw [← hliminf]
        refine le_iSup₂ (f := fun a (_h : Function.Injective fun k => Int.fract (a k)) =>
          liminf (fun n : ℕ => ENNReal.ofReal ((n : ℝ) * minSpan a n 1)) atTop) ex ex_inj
      exact hge
  · apply le_antisymm
    · have hle : mu 1 ≤ limsup (fun n : ℕ =>
          ENNReal.ofReal (maxSpan ex n 1) / ENNReal.ofReal (minSpan ex n 1)) atTop := by
        simpa [mu] using iInf₂_le ex ex_inj
      rwa [hmu.limsup_eq] at hle
    · have hge := mu_ge 1 (by decide)
      have h2 : (1 : ℝ) + 1 / (1 : ℕ) = 2 := by norm_num
      rw [h2, ENNReal.ofReal_ofNat] at hge
      exact hge

end
