import RothInducedDoubling

open Finset
namespace Erdos142HalfScale
open Erdos142InducedTriples Erdos142DyadicClusters

private def phase (g : Fin 4) (i : Fin 5) : Fin 4 :=
  ⟨(g.val+4-i.val)%4, Nat.mod_lt _ (by decide)⟩
private def jump (g : Fin 4) (i : Fin 5) : ℕ := if i.val ≤ g.val then 0 else 1
private theorem table : ∀ (g : Fin 4) (i : Fin 5),
    g.val+4*jump g i=(phase g i).val+i.val := by decide
private theorem two_digits : ∀ (g : Fin 4) (i j k : Fin 5),
    phase g i=phase g j → phase g j=phase g k →
    i.val+k.val=j.val+j.val → i=k := by decide

/-- Five tagged copies per pair across four free subsets of a half-length
    interval. The common step can have either parity. -/
theorem half_per_pair {A : Finset ℕ} {n t : ℕ} (ht : 0<t) (fit : A ⊆ range n)
    (weak : Weak t A) :
    5*(pairs t A).card ≤ 4*rothNumberNat ((n+1)/2+2*t) := by
  classical
  let q (x : ℕ) := x/(2*t)
  let r (x : ℕ) := x%(2*t)
  have dec (x : ℕ) : r x + 2*(t*q x)=x := by
    simpa [q,r,Nat.mul_assoc] using Nat.mod_add_div x (2*t)
  have small (x : ℕ) : r x<2*t := Nat.mod_lt _ (by omega)
  let g (x : ℕ) : Fin 4 := ⟨(2*r x)/t, (Nat.div_lt_iff_lt_mul ht).mpr (by have := small x; omega)⟩
  let remn (x : ℕ) := (2*r x)%t
  have srep (x : ℕ) : remn x+t*(g x).val=2*r x := Nat.mod_add_div _ _
  have rs (x : ℕ) : remn x<t := Nat.mod_lt _ ht
  let pos (x : ℕ) (i : Fin 5) := t*q x+r x+t*jump (g x) i
  have posrep (x : ℕ) (i : Fin 5) :
      4*pos x i=2*x+t*(phase (g x) i).val+t*i.val+remn x := by
    have eq := congrArg (fun h : ℕ => t*h) (table (g x) i)
    simp only [Nat.mul_add] at eq
    dsimp only [pos]
    nlinarith only [eq,srep x,dec x]
  have con (x : ℕ) (i : Fin 5) : (pos x i : ℤ)=x+(t:ℤ)*((jump (g x) i:ℤ)-(q x:ℤ)) := by
    have d : (r x:ℤ)+2*((t:ℤ)*(q x:ℤ))=x := by exact_mod_cast dec x
    dsimp only [pos]
    push_cast
    linear_combination d
  have proj {x y z : ℕ} {i j k : Fin 5} (hx : x ∈ pairs t A) (hy : y ∈ pairs t A)
      (hz : z ∈ pairs t A) (c1 : phase (g x) i=phase (g y) j)
      (c2 : phase (g y) j=phase (g z) k)
      (eq : pos x i+pos z k=pos y j+pos y j) : x=y ∧ y=z ∧ i=k := by
    have ed : (pos x i:ℤ)+pos z k=pos y j+pos y j := by exact_mod_cast eq
    rw [con,con,con] at ed
    obtain ⟨h,dh⟩ : (t:ℤ) ∣ (x:ℤ)+z-2*y := by
      use 2*((jump (g y) j:ℤ)-q y)-((jump (g x) i:ℤ)-q x)-((jump (g z) k:ℤ)-q z)
      linear_combination ed
    have px := posrep x i
    have py := posrep y j
    have pz := posrep z k
    rw [c1] at px
    rw [← c2] at pz
    have bound (u : Fin 5) : t*u.val≤4*t := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left t (show u.val≤4 by have := u.isLt; omega)
    have side : -(5*(t:ℤ)) < (x:ℤ)+z-2*y ∧ (x:ℤ)+z-2*y < 5*t := by
      have := bound i
      have := bound j
      have := bound k
      have := rs x
      have := rs y
      have := rs z
      constructor <;> omega
    have tp : (0:ℤ)<t := by exact_mod_cast ht
    have hh : -4≤h ∧ h≤4 := by
      constructor
      · by_contra! e
        have b := mul_le_mul_of_nonneg_left (show h≤ -5 by omega) tp.le
        nlinarith only [b,dh,side.1]
      · by_contra! e
        have b := mul_le_mul_of_nonneg_left (show 5≤h by omega) tp.le
        nlinarith only [b,dh,side.2]
    obtain ⟨rfl,rfl⟩ := strong_roots ht weak hx hy hz h hh.1 hh.2 (by simpa [mul_comm] using dh)
    have dg : t*(i.val+k.val)=t*(j.val+j.val) := by rw [Nat.mul_add,Nat.mul_add]; omega
    exact ⟨rfl,rfl,two_digits _ _ _ _ c1 c2 (Nat.eq_of_mul_eq_mul_left ht dg)⟩
  let dom := pairs t A ×ˢ (univ : Finset (Fin 5))
  let tag (u : ℕ × Fin 5) := phase (g u.1) u.2
  let site (u : ℕ × Fin 5) := pos u.1 u.2
  let F (c : Fin 4) := dom.filter (fun u => tag u=c)
  have cap (c : Fin 4) : (F c).card ≤ rothNumberNat ((n+1)/2+2*t) := by
    have comp {x : ℕ} {i : Fin 5} (h : (x,i) ∈ F c) :
        x ∈ pairs t A ∧ phase (g x) i=c := ⟨(mem_product.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
    have inj : Set.InjOn site (↑(F c) : Set (ℕ × Fin 5)) := by
      rintro ⟨x,i⟩ hx ⟨y,j⟩ hy e
      change pos x i=pos y j at e
      obtain ⟨eq,_,di⟩ := proj (comp hx).1 (comp hy).1 (comp hy).1
        ((comp hx).2.trans (comp hy).2.symm) rfl (by rw [e])
      exact Prod.ext eq di
    have free : ThreeAPFree (↑((F c).image site) : Set ℕ) := by
      apply threeAPFree_iff_eq_right.mpr
      intro a ha b hb d hd e
      obtain ⟨⟨x,i⟩,hx,rfl⟩ := mem_image.mp ha
      obtain ⟨⟨y,j⟩,hy,rfl⟩ := mem_image.mp hb
      obtain ⟨⟨z,k⟩,hz,rfl⟩ := mem_image.mp hd
      obtain ⟨rfl,rfl,rfl⟩ := proj (comp hx).1 (comp hy).1 (comp hz).1
        ((comp hx).2.trans (comp hy).2.symm) ((comp hy).2.trans (comp hz).2.symm) e
      rfl
    rw [← card_image_of_injOn inj]
    apply free.le_rothNumberNat _ _ rfl
    intro a ha
    obtain ⟨⟨x,i⟩,hx,rfl⟩ := mem_image.mp ha
    have xt := mem_range.mp (fit (mem_filter.mp (comp hx).1).2)
    have jj : jump (g x) i ≤ 1 := by dsimp [jump]; split <;> decide
    have tj := Nat.mul_le_mul_left t jj
    have rr := small x
    have dd := dec x
    change pos x i < (n+1)/2+2*t
    dsimp only [pos]
    omega
  have total : ∑ c : Fin 4, (F c).card = dom.card := by
    dsimp only [F]
    simp_rw [card_filter]
    rw [sum_comm]
    simp
  have lim := sum_le_sum (s:= (univ : Finset (Fin 4))) (fun c _ => cap c)
  rw [total] at lim
  simpa [dom, Nat.mul_comm] using lim

#print axioms half_per_pair
end Erdos142HalfScale
