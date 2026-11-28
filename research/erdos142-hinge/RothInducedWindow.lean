import RothInducedScales

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters

private theorem partition (w m : ℕ) : rothNumberNat (m*w) ≤ m*rothNumberNat w := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul,Nat.succ_mul]
    exact (rothNumberNat_add_le _ _).trans (Nat.add_le_add_right ih _)

theorem sieve_from_bound {n t N K B p : ℕ}
    (residue : ∀ b : ℕ, 0<b → ¬ b ∣ t → 3*p ≤ b*rothNumberNat ((n+t+b-1)/b))
    (length : n+t≤K*N) (density : (K+B)*rothNumberNat N < 3*p) :
    ∀ b : ℕ, 0<b → b≤B → b ∣ t := by
  intro b hb bs
  by_contra miss
  have bound := residue _ hb miss
  let parts := K/b+1
  have mod := Nat.mod_add_div K b
  have rem := Nat.mod_lt K hb
  have sz : K≤b*parts ∧ b*parts≤K+B := by
    dsimp [parts]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have inside : n+t≤b*(parts*N) := by
    rw [← Nat.mul_assoc]
    exact length.trans (Nat.mul_le_mul_right _ sz.1)
  have q : (n+t+b-1)/b ≤ parts*N := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul hb).mpr
    rw [Nat.succ_mul,Nat.mul_comm (parts*N) b]
    omega
  have cap := (rothNumberNat.monotone q).trans (partition N parts)
  have bcap := Nat.mul_le_mul_left b cap
  rw [← Nat.mul_assoc] at bcap
  have limit := Nat.mul_le_mul_right (rothNumberNat N) sz.2
  omega

/-- A sufficiently dense collection of isolated triples forces every small
    modulus to divide its common step. N is the comparison interval length. -/
theorem all_small_divide {A : Finset ℕ} {n t N K B : ℕ} (ht : 0<t)
    (fit : A ⊆ range n) (weak : Weak t A) (length : n+t≤K*N)
    (density : (K+B)*rothNumberNat N < 3*(pairs t A).card) :
    ∀ b : ℕ, 0<b → b≤B → b ∣ t :=
  sieve_from_bound (fun _ hb miss => residue_bound ht hb miss fit weak) length density

#print axioms sieve_from_bound
#print axioms all_small_divide
end Erdos142InducedTriples
