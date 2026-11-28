import RothSampleColumns

open Finset
namespace Erdos142DigitCuts

private theorem partition_cap (w l : ℕ) : rothNumberNat (w*l)≤l*rothNumberNat w := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Nat.mul_succ,Nat.succ_mul]
    exact (rothNumberNat_add_le _ _).trans (Nat.add_le_add_right ih _)

/-- Between successive selected cuts the radix is w times an arbitrary factor.
    This covers unequally spaced cuts with any fixed minimum binary spacing. -/
def blockList (w K first : ℕ) (lengths : List ℕ) :=
  (first,K)::lengths.map (fun l => (w*l,K))

private theorem cap_gaps (w K : ℕ) (ls : List ℕ) :
    (ls.map (fun l => K*rothNumberNat (w*l))).prod ≤
      (K*rothNumberNat w)^ls.length * ls.prod := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ]
    have small := Nat.mul_le_mul_left K (partition_cap w l)
    have both := Nat.mul_le_mul small ih
    convert both using 1
    ring

theorem separated_sample_bound (w K first q : ℕ) (ls : List ℕ) (A : Finset ℕ)
    (hw : 0<w) (hf : 0<first) (pos : ∀ l ∈ ls, 0<l)
    (fit : A ⊆ range (first*(ls.map (fun l => w*l)).prod*q))
    (free : ThreeAPFree (↑A : Set ℕ)) (g : Samples A 1 (blockList w K first ls)) :
    A.card≤K*first*q*(K*rothNumberNat w)^ls.length*ls.prod := by
  have good : ∀ p ∈ blockList w K first ls, 0<p.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl|rest
    · exact hf
    · obtain ⟨l,hl,rfl⟩ := List.mem_map.mp rest
      exact Nat.mul_pos hw (pos _ hl)
  have bound := sampled_multicut (blockList w K first ls) q A good (by
    simpa [blockList,List.map_map,Function.comp_def] using fit) free g
  simp only [blockList,List.map_cons,List.prod_cons,List.map_map,Function.comp_def] at bound
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left K (rothNumberNat_le first)) (cap_gaps w K ls)
  have both := Nat.mul_le_mul h (rothNumberNat_le q)
  calc
    A.card ≤ _ := bound
    _ ≤ (K*first*((K*rothNumberNat w)^ls.length*ls.prod))*q := both
    _ = _ := by ring

private theorem product_scale (w : ℕ) (ls : List ℕ) :
    (ls.map (fun l => w*l)).prod=w^ls.length*ls.prod := by
  induction ls with
  | nil => simp
  | cons l ls ih => simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ih]; ring

/-- If k+1 independently chosen cuts each need at most two actual sampled
    blocks, and consecutive gaps are multiples of radix 128, the occupied
    fraction is at most 2*(7/8)^k. -/
theorem two_sample_loss (first q : ℕ) (ls : List ℕ) (A : Finset ℕ)
    (hf : 0<first) (pos : ∀ l ∈ ls, 0<l)
    (fit : A ⊆ range (first*(ls.map (fun l => 128*l)).prod*q))
    (free : ThreeAPFree (↑A : Set ℕ)) (g : Samples A 1 (blockList 128 2 first ls)) :
    A.card*8^ls.length ≤ 2*(first*(ls.map (fun l => 128*l)).prod*q)*7^ls.length := by
  have bound := separated_sample_bound 128 2 first q ls A (by decide) hf pos fit free g
  have cap := Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 seven_bit_capacity) ls.length
  have b := Nat.mul_le_mul_right ls.prod (Nat.mul_le_mul_left (2*first*q) cap)
  have c := Nat.mul_le_mul_right (8^ls.length) (bound.trans b)
  rw [product_scale]
  convert c using 1
  have eq : (2*56)^ls.length*8^ls.length=128^ls.length*7^ls.length := by
    rw [← mul_pow,← mul_pow]; norm_num
  nlinarith only [congrArg (fun k : ℕ => 2*first*q*ls.prod*k) eq]

#print axioms separated_sample_bound
#print axioms two_sample_loss
end Erdos142DigitCuts
