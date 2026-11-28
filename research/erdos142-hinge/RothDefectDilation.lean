import RothExactDefects

open Finset

namespace Erdos142ExactDefects

/-- Every rational dilation m/n up to two transfers all the surviving points.
    The extra coordinate partitions the candidates into n*t possible phases. -/
theorem rational_dilation (B : Finset ℕ) (n m t : ℕ) (hn : 0 < n) (ht : 0 < t)
    (lower : n ≤ m) (upper : m ≤ 2*n) (fit : B ⊆ range n)
    (strong : ∀ x ∈ B, ∀ y ∈ B, ∀ z ∈ B,
      (let d := (x:ℤ)+z-2*y; d=0 ∨ d=t ∨ d= -(t:ℤ)) → x=y ∧ y=z) :
    m*B.card ≤ n*rothNumberNat (m+2*t) := by
  let dom := B ×ˢ range (m*t)
  let total (p : ℕ × ℕ) := (m-n)*p.1+p.2
  let block (p : ℕ × ℕ) := total p / (n*t)
  let phase (p : ℕ × ℕ) := total p % (n*t)
  let pos (p : ℕ × ℕ) := p.1+t*block p
  let enc (p : ℕ × ℕ) := (phase p,pos p)
  let S (h : ℕ) := (dom.filter (fun p => phase p = h)).image pos
  have nt := Nat.mul_pos hn ht
  have mtpos : 0 < m := by omega
  have iden (p : ℕ × ℕ) : n*pos p+phase p = m*p.1+p.2 := by
    have id := Nat.mod_add_div (total p) (n*t)
    have split : (m-n)*p.1+n*p.1=m*p.1 := by
      rw [← Nat.add_mul, Nat.sub_add_cancel lower]
    dsimp only [pos,block,phase]
    rw [Nat.mul_add,← Nat.mul_assoc]
    dsimp only [total] at id ⊢
    omega
  have components {p} (hp : p ∈ dom) : p.1 ∈ B ∧ p.2 < m*t := by
    exact ⟨(mem_product.mp hp).1,mem_range.mp (mem_product.mp hp).2⟩
  have proj {p v w : ℕ × ℕ} (hp : p ∈ dom) (hv : v ∈ dom) (hw : w ∈ dom)
      (a : phase p = phase v) (b : phase v = phase w) (eq : pos p+pos w=pos v+pos v) :
      p.1=v.1 ∧ v.1=w.1 := by
    have cong : (t:ℤ) ∣ (p.1:ℤ)+w.1-2*v.1 := by
      have e : (p.1:ℤ)+t*(block p)+(w.1+t*(block w)) =
          v.1+t*(block v)+(v.1+t*(block v)) := by exact_mod_cast eq
      use 2*(block v:ℤ)-block p-block w
      linarith
    let Y (g : ℕ × ℕ) : ℝ := ↑(n*pos g+phase g)
    have tubes {g : ℕ × ℕ} (hg : g ∈ dom) :
        (m:ℝ)*(g.1:ℕ)+0 ≤ Y g ∧ Y g < (m:ℝ)*(g.1:ℕ)+0+(m:ℝ)*t := by
      dsimp only [Y]
      rw [iden]
      have e : m*g.1+g.2 < m*g.1+m*t := Nat.add_lt_add_left (components hg).2 _
      constructor
      · push_cast; linarith
      · simpa only [add_zero,Nat.cast_add,Nat.cast_mul] using (show (↑(m*g.1+g.2):ℝ)<↑(m*g.1+m*t) by exact_mod_cast e)
    have ye : Y p+Y w=2*Y v := by
      have e := congrArg (fun i => n*i) eq
      simp only [Nat.mul_add] at e
      have h : n*pos p+phase p+(n*pos w+phase w)=2*(n*pos v+phase v) := by omega
      dsimp only [Y]
      exact_mod_cast h
    apply strong _ (components hp).1 _ (components hv).1 _ (components hw).1
    exact tube_projection p.1 v.1 w.1 t (by exact_mod_cast ht) m 0
      (Y p) (Y v) (Y w) (by exact_mod_cast mtpos) (by simpa using tubes hp)
      (by simpa using tubes hv) (by simpa using tubes hw) ye cong
  have inj : Set.InjOn enc (↑dom : Set (ℕ × ℕ)) := by
    intro p hp v hv e
    have sameH : phase p = phase v := congrArg Prod.fst e
    have sameY : pos p = pos v := congrArg Prod.snd e
    have sameX := (proj hp hv hv sameH rfl (by rw [sameY])).1
    have ep := iden p
    rw [sameX,sameH,sameY] at ep
    exact Prod.ext sameX (by have := iden v; omega)
  have cap (h : ℕ) : (S h).card ≤ rothNumberNat (m+2*t) := by
    have free : ThreeAPFree (↑(S h) : Set ℕ) := by
      apply threeAPFree_iff_eq_right.mpr
      intro X hX Y hY Z hZ eq
      obtain ⟨p,hp,rfl⟩ := mem_image.mp hX
      obtain ⟨v,hv,rfl⟩ := mem_image.mp hY
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hZ
      obtain ⟨hp,ph⟩ := mem_filter.mp hp
      obtain ⟨hv,vh⟩ := mem_filter.mp hv
      obtain ⟨hw,wh⟩ := mem_filter.mp hw
      obtain ⟨pv,vw⟩ := proj hp hv hw (ph.trans vh.symm) (vh.trans wh.symm) eq
      have ep := iden p
      have ew := iden w
      rw [pv,ph] at ep
      rw [← vw,wh] at ew
      have mtle : m*t ≤ 2*(n*t) := by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right t upper
      have smallP := (components hp).2
      have smallW := (components hw).2
      have spread : ¬(pos p+2*t ≤ pos w) ∧ ¬(pos w+2*t ≤ pos p) := by
        constructor <;> intro big
        · have bound := Nat.mul_le_mul_left n big
          simp only [Nat.mul_add, Nat.mul_left_comm n 2] at bound
          omega
        · have bound := Nat.mul_le_mul_left n big
          simp only [Nat.mul_add, Nat.mul_left_comm n 2] at bound
          omega
      have vv : block p+block w=block v+block v := by
        apply Nat.eq_of_mul_eq_mul_left ht
        dsimp only [pos] at eq
        rw [pv,←vw] at eq
        simp only [Nat.mul_add]
        omega
      have equal : block p = block w := by
        by_contra neq
        have apart : block p+2 ≤ block w ∨ block w+2 ≤ block p := by omega
        dsimp only [pos] at spread
        rw [pv,←vw] at spread
        rcases apart with ap|ap <;> have step := Nat.mul_le_mul_left t ap <;>
          simp only [Nat.mul_add, Nat.mul_comm t 2] at step <;> omega
      dsimp only [pos]
      rw [pv,←vw,equal]
    apply free.le_rothNumberNat _ _ rfl
    intro y hy
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hy
    obtain ⟨bx,small⟩ := components (mem_filter.mp hp).1
    have eq := iden p
    have xlt := Nat.mul_lt_mul_of_pos_left (mem_range.mp (fit bx)) mtpos
    have bound := Nat.mul_le_mul_right t upper
    apply lt_of_mul_lt_mul_left (a := n) _ (by omega)
    rw [Nat.mul_add n m (2*t), Nat.mul_comm n m,Nat.mul_left_comm n 2]
    rw [Nat.mul_assoc] at bound
    omega
  let family := (range (n*t)).biUnion (fun h => (S h).image (fun y => (h,y)))
  have inside : dom.image enc ⊆ family := by
    intro z hz
    obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
    apply mem_biUnion.mpr
    refine ⟨phase p,mem_range.mpr (Nat.mod_lt _ nt),?_⟩
    exact mem_image.mpr ⟨pos p,mem_image.mpr ⟨p,mem_filter.mpr ⟨hp,rfl⟩,rfl⟩,rfl⟩
  have bound : (dom.image enc).card ≤ (n*t)*rothNumberNat (m+2*t) := calc
    _ ≤ family.card := card_le_card inside
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ _h ∈ range (n*t), rothNumberNat (m+2*t) := sum_le_sum (fun h _ => card_image_le.trans (cap h))
    _ = _ := by simp
  rw [card_image_of_injOn inj] at bound
  change (B ×ˢ range (m*t)).card ≤ _ at bound
  rw [card_product,card_range] at bound
  have e : (m*B.card)*t ≤ (n*rothNumberNat (m+2*t))*t := by nlinarith only [bound]
  exact Nat.le_of_mul_le_mul_right e ht

/-- Finite density-drop criterion for a cover of the three-distinct-point defect. -/
theorem rational_cover_transfer (A C : Finset ℕ) (n m t : ℕ) (hn : 0 < n) (ht : 0 < t)
    (lower : n ≤ m) (upper : m ≤ 2*n) (fit : A ⊆ range n)
    (free : ThreeAPFree (↑A : Set ℕ)) (hc : Covers A C t) :
    m*A.card ≤ n*rothNumberNat (m+2*t)+m*(C.card+(badStarts A t).card) := by
  let U := C ∪ badStarts A t
  let B := A \ U
  have cap := rational_dilation B n m t hn ht lower upper
    (fun x hx => fit (mem_sdiff.mp hx).1) (cleaned_strong A C t ht free hc)
  have cA : A.card ≤ B.card + (C.card+(badStarts A t).card) := by
    calc
      _ ≤ (B ∪ U).card := card_le_card (by intro x hx; by_cases h : x ∈ U <;> simp [B,h,hx])
      _ ≤ B.card + U.card := card_union_le _ _
      _ ≤ _ := Nat.add_le_add_left (card_union_le _ _) _
  have prod := Nat.mul_le_mul_left m cA
  rw [Nat.mul_add] at prod
  omega

#print axioms rational_dilation
#print axioms rational_cover_transfer

end Erdos142ExactDefects
