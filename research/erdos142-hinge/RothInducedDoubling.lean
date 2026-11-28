import RothInducedTriples

open Finset
namespace Erdos142InducedTriples
open Erdos142DyadicClusters

private def four : Finset ℕ := {0,1,3,4}
private theorem four_free : ∀ i ∈ four, ∀ j ∈ four, ∀ k ∈ four,
    i+k=j+j → i=k := by decide

/-- Doubling the base locations allows four free choices at each root. -/
theorem four_per_pair {A : Finset ℕ} {n t : ℕ} (ht : 0<t) (fit : A ⊆ range n)
    (weak : Weak t A) : 4*(pairs t A).card ≤ rothNumberNat (2*n+2*t) := by
  let L (p : ℕ × ℕ) := p.1+t*(p.1/t+p.2)
  have rep (x i : ℕ) : L (x,i)+x%t=2*x+t*i := by
    dsimp only [L]
    rw [Nat.mul_add]
    have := Nat.mod_add_div x t
    omega
  have project {x y z i j k : ℕ} (hx : x ∈ pairs t A) (hy : y ∈ pairs t A)
      (hz : z ∈ pairs t A) (hi : i ∈ four) (hj : j ∈ four) (hk : k ∈ four)
      (e : L (x,i)+L (z,k)=L (y,j)+L (y,j)) : x=y ∧ y=z ∧ i=k := by
    have div : (t:ℤ) ∣ (x:ℤ)+z-2*y := by
      let v (u d : ℕ) : ℤ := ↑(u/t+d)
      have eq : ((x:ℤ)+t*v x i)+(z+t*v z k)=(y+t*v y j)+(y+t*v y j) := by
        dsimp [v]
        exact_mod_cast e
      use 2*v y j-v x i-v z k
      linear_combination eq
    obtain ⟨h,dh⟩ := div
    have bound : ∀ d ∈ four, t*d≤4*t :=
      fun d hd => calc
        t*d ≤ t*4 := Nat.mul_le_mul_left _ ((by decide : ∀ i ∈ four, i≤4) d hd)
        _ = _ := Nat.mul_comm _ _
    have tx := Nat.mod_lt x ht
    have ty' := Nat.mod_lt y ht
    have tz := Nat.mod_lt z ht
    have px := rep x i
    have py := rep y j
    have pz := rep z k
    have bx := bound i hi
    have by' := bound j hj
    have bz := bound k hk
    have low : -(5*(t:ℤ)) < (x:ℤ)+z-2*y := by omega
    have high : (x:ℤ)+z-2*y < 5*(t:ℤ) := by omega
    have pos : (0:ℤ)<t := by exact_mod_cast ht
    have hh : -4≤h ∧ h≤4 := by
      constructor
      · by_contra! f
        have sz := mul_le_mul_of_nonneg_left (show h≤ -5 by omega) pos.le
        nlinarith only [dh,low,sz]
      · by_contra! f
        have sz := mul_le_mul_of_nonneg_left (show 5≤h by omega) pos.le
        nlinarith only [dh,high,sz]
    obtain ⟨rfl,rfl⟩ := strong_roots ht weak hx hy hz h hh.1 hh.2 (by simpa [mul_comm] using dh)
    have digs : t*(i+k)=t*(j+j) := by
      rw [Nat.mul_add,Nat.mul_add]
      omega
    exact ⟨rfl,rfl,four_free _ hi _ hj _ hk (Nat.eq_of_mul_eq_mul_left ht digs)⟩
  let V := (pairs t A ×ˢ four).image L
  have inj : Set.InjOn L (↑(pairs t A ×ˢ four) : Set (ℕ × ℕ)) := by
    rintro ⟨x,i⟩ xi ⟨y,j⟩ yj eq
    obtain ⟨hx,hi⟩ := mem_product.mp xi
    obtain ⟨hy,hj⟩ := mem_product.mp yj
    obtain ⟨rfl,_,rfl⟩ := project hx hy hy hi hj hj (by rw [eq])
    rfl
  have freeV : ThreeAPFree (↑V : Set ℕ) := by
    apply threeAPFree_iff_eq_right.mpr
    intro a ha b hb c hc e
    obtain ⟨⟨x,i⟩,xi,rfl⟩ := mem_image.mp ha
    obtain ⟨⟨y,j⟩,yj,rfl⟩ := mem_image.mp hb
    obtain ⟨⟨z,k⟩,zk,rfl⟩ := mem_image.mp hc
    obtain ⟨rfl,rfl,rfl⟩ := project (mem_product.mp xi).1 (mem_product.mp yj).1
      (mem_product.mp zk).1 (mem_product.mp xi).2 (mem_product.mp yj).2 (mem_product.mp zk).2 e
    rfl
  have size : V.card=(pairs t A).card*4 := by
    rw [card_image_of_injOn inj,card_product]
    rfl
  rw [Nat.mul_comm,← size]
  apply freeV.le_rothNumberNat _ _ rfl
  intro a ha
  obtain ⟨⟨x,i⟩,xi,rfl⟩ := mem_image.mp ha
  have xt := mem_range.mp (fit (mem_filter.mp (mem_product.mp xi).1).2)
  have cap := Nat.mul_le_mul_left t ((by decide : ∀ i ∈ four, i≤4) i (mem_product.mp xi).2)
  rw [Nat.mul_comm t 4] at cap
  have h := rep x i
  omega

#print axioms four_per_pair
end Erdos142InducedTriples
