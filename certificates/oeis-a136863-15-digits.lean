import Mathlib

/-! Finite verification of Robert Israel's conjecture in OEIS A136863.
The search goes from the least significant column to the most significant.
The completeness lemma applies to any precision and every natural number. -/
namespace Deldor14.DecimalSquares

def palette : List ℕ := [0,1,4,7]
def valid (n : ℕ) : Bool := (Nat.digits 10 n).all (fun t => palette.contains t)
def digit (n j : ℕ) := n / 10^j % 10

theorem columns (n : ℕ) (hyp : valid n=true) (j : ℕ) : digit n j ∈ palette := by
  induction j generalizing n with
  | zero =>
    by_cases z : n=0
    · subst n;decide
    have e := Nat.digits_eq_cons_digits_div (by decide : 1<10) z
    simp only [valid,e,List.all_cons,Bool.and_eq_true,List.contains_iff_mem] at hyp
    simpa [digit] using hyp.1
  | succ j ih =>
    by_cases z : n=0
    · subst n;simp [digit,palette]
    have e := Nat.digits_eq_cons_digits_div (by decide : 1<10) z
    have tail : valid (n/10)=true := by
      simp only [valid,e,List.all_cons,Bool.and_eq_true] at hyp
      exact hyp.2
    simpa only [digit,Nat.div_div_eq_div_mul,pow_succ'] using ih (n/10) tail

def prefixes : ℕ → List ℕ
  | 0 => [1]
  | k+1 => (prefixes k).flatMap (fun r => (palette.map (fun c => r+10^(k+1)*c)).filter
      (fun s => palette.contains (digit (s^2) (k+1))))

theorem complete (x : ℕ) (hx : valid x=true) (hs : valid (x^2)=true) (nz : ¬10 ∣ x) (k : ℕ) :
    x%10^(k+1) ∈ prefixes k := by
  induction k with
  | zero =>
    have h := columns x hx 0
    have q := columns (x^2) hs 0
    simp [digit,palette] at h q
    have eq : x^2%10=(x%10)^2%10 := (Nat.pow_mod x 2 10)
    rw [eq] at q
    simp only [prefixes,List.mem_singleton,pow_one]
    rcases h with e|e|e|e <;> simp_all [Nat.dvd_iff_mod_eq_zero]
  | succ k ih =>
    let P := 10^(k+1)
    let M := P*10
    have e : x%M=x%P+P*digit x (k+1) := Nat.mod_mul
    have congruence : (x%M)^2 ≡ x^2 [MOD M] := (Nat.mod_modEq x M).pow 2
    have dig : digit ((x%M)^2) (k+1)=digit (x^2) (k+1) := by
      change (_/P)%10=(_/P)%10
      rw [← Nat.mod_mul_right_div_self,← Nat.mod_mul_right_div_self (x^2)]
      exact congrArg (fun n : ℕ => n/P) congruence
    change x%10^(k+1+1) ∈ List.flatMap _ (prefixes k)
    rw [pow_succ]
    apply List.mem_flatMap.mpr
    refine ⟨x%P,ih,List.mem_filter.mpr ⟨?_,?_⟩⟩
    · exact List.mem_map.mpr ⟨_,columns x hx (k+1),e.symm⟩
    · change palette.contains (digit ((x%M)^2) (k+1))=true
      rw [dig,List.contains_iff_mem]
      exact columns (x^2) hs (k+1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem survivors :
    ((prefixes 14).filter (fun x => valid (x^2)))=[1,1071] := by
  decide +kernel

theorem verified (x : ℕ) (bound : x<10^15) (hx : valid x=true) (hs : valid (x^2)=true) (nz : ¬10 ∣ x) :
    x=1 ∨ x=1071 := by
  have h := complete x hx hs nz 14
  rw [Nat.mod_eq_of_lt bound] at h
  have z : x ∈ (prefixes 14).filter (fun v => valid (v^2)) := List.mem_filter.mpr ⟨h,hs⟩
  rw [survivors] at z
  simpa using z

#print axioms verified
end Deldor14.DecimalSquares
