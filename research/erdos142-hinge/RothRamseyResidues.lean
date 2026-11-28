import RothRamseyGlue
import RothPrimeRows

open Finset Erdos142RamseyGlue Erdos142LongDigits
namespace Erdos142RamseyResidues

def extend (p t : ℕ) (S H : Finset ℕ) :=
  S.filter (fun x => (x+t)%p=0) ∪ H.filter (fun x => (x+t)%p=1)

/-- The two adjacent residues permit arbitrary free data on the first residue. -/
theorem extend_free {p k : ℕ} (hp : 3≤p) (hk : 3≤k) (t : ℕ) (S H : Finset ℕ)
    (sfree : Free k S) (hfree : Free 3 H) : Free k (extend p t S H) := by
  let tag (x : ℕ) := (x+t)%p
  let seed (i : ℕ) := if i=0 then S else H
  have labels {x : ℕ} (hx : x ∈ extend p t S H) : tag x=0 ∨ tag x=1 :=
    (mem_union.mp hx).elim (fun h => Or.inl (mem_filter.mp h).2)
      (fun h => Or.inr (mem_filter.mp h).2)
  apply free_glue hk _ tag seed
  · intro x hx
    rcases mem_union.mp hx with h|h
    · have ht : tag x=0 := (mem_filter.mp h).2
      simpa [seed,ht] using (mem_filter.mp h).1
    · have ht : tag x=1 := (mem_filter.mp h).2
      simpa [seed,ht] using (mem_filter.mp h).1
  · intro i
    by_cases hi : i=0
    · simpa [seed,hi] using sfree
    · simp only [seed,if_neg hi]
      intro a q pos terms
      exact hfree a q pos (fun j hj => terms j (by omega))
  · intro x hx y hy z hz eq
    have lx := labels hx
    have ly := labels hy
    have lz := labels hz
    have add (u v : ℕ) (small : tag u+tag v<p) :
        ((u+t)+(v+t))%p=tag u+tag v := by
      rw [Nat.add_mod]
      exact Nat.mod_eq_of_lt small
    have e : (x+t)+(z+t)=(y+t)+(y+t) := by omega
    have mid := congrArg (fun n => n%p) e
    change ((x+t)+(z+t))%p=((y+t)+(y+t))%p at mid
    rw [add x z (by omega),add y y (by omega)] at mid
    omega

/-- At the threshold n ≤ p(L−1), every step of an L-window is a unit modulo p. -/
theorem extend_hits {p n L ell : ℕ} (prime : p.Prime) (hp : 3≤p)
    (he : 0<ell) (width : p*ell≤L) (cap : n≤p*(L-1))
    (t : ℕ) (S H : Finset ℕ) (hit : Hits n ell H) : Hits n L (extend p t S H) := by
  apply hits_glue (fun x => (x+t)%p=1) _ hit
  · intro x hx prop
    exact mem_union_right _ (mem_filter.mpr ⟨hx,prop⟩)
  · intro a q hq fit
    have hl : 0<L := lt_of_lt_of_le (Nat.mul_pos (by omega) he) width
    have last := fit (L-1) (by omega)
    have hqp : q<p := by
      by_contra! large
      have := Nat.mul_le_mul_left (L-1) large
      rw [Nat.mul_comm (L-1) p] at this
      omega
    have unit : q.Coprime p := (prime.coprime_iff_not_dvd.mpr
      (fun dvd => (Nat.not_le_of_gt hqp) (Nat.le_of_dvd hq dvd))).symm
    obtain ⟨b,beq⟩ := (Erdos142PrimeRows.residue_bijective (by omega : 0<p) (a+t) q unit).surjective
      (⟨1,by omega⟩ : Fin p)
    have phase : ((a+t)+b.val*q)%p=1 := congrArg Fin.val beq
    refine ⟨b.val,p,by omega,?_⟩
    intro i hi
    have below : b.val+i*p < p*ell := calc
      b.val+i*p < p+i*p := Nat.add_lt_add_right b.isLt _
      _ = p*(i+1) := by ring
      _ ≤ p*ell := Nat.mul_le_mul_left _ hi
    constructor
    · omega
    · have rearr : a+(b.val+i*p)*q+t=((a+t)+b.val*q)+(i*q)*p := by ring
      rw [rearr,Nat.add_mul_mod_self_right,phase]

private def sample : Finset ℕ :=
  {0,1,10,11,14,15,25,32,38,42,43,47,55,57,58,60}

private theorem sample_free : Free 3 sample := by
  have cert : ∀ a : Fin 61, ∀ q : Fin 31, 0<q.val → a.val ∈ sample →
      a.val+q.val ∈ sample → a.val+2*q.val ∉ sample := by decide
  intro a q hq terms
  have endpt : a+2*q ∈ sample := terms 2 (by decide)
  have bounded : ∀ x ∈ sample, x<61 := by decide
  have := bounded _ endpt
  exact cert ⟨a,by omega⟩ ⟨q,by omega⟩ hq (by simpa using terms 0 (by decide))
    (by simpa using terms 1 (by decide)) endpt

private theorem sample_hits : Hits 61 10 sample := by
  have cert : ∀ a : Fin 61, ∀ q : Fin 7, 0<q.val → a.val+9*q.val<61 →
      ∃ i : Fin 10, a.val+i.val*q.val ∈ sample := by decide
  intro a q hq fits
  have last := fits 9 (by decide)
  obtain ⟨i,hi⟩ := cert ⟨a,by omega⟩ ⟨q,by omega⟩ hq last
  exact ⟨i.val,i.isLt,hi⟩

/-- A complete instance on 61 sites. Every point of the prescribed free set
    is retained by one of the three phases. Every extension hits all 30-term APs. -/
theorem all_inputs_61 {k : ℕ} (hk : 3≤k) (S : Finset ℕ) (subset : S ⊆ range 61)
    (sfree : Free k S) :
    ∃ family : Fin 3 → Finset ℕ,
      (∀ t, family t ⊆ range 61 ∧ Free k (family t) ∧ Hits 61 30 (family t)) ∧
      (∀ x ∈ S, ∃ t, x ∈ family t) := by
  refine ⟨fun t => extend 3 t.val S sample,?_,?_⟩
  · intro t
    refine ⟨?_,extend_free (by decide) hk _ _ _ sfree sample_free,
      extend_hits (by decide) (by decide) (by decide : 0<10) (by decide) (by decide) _ _ _ sample_hits⟩
    intro x hx
    rcases mem_union.mp hx with hs|hh
    · exact subset (mem_filter.mp hs).1
    · have bounded : sample ⊆ range 61 := by decide
      exact bounded (mem_filter.mp hh).1
  · intro x hx
    let t := 2 - (x+2)%3
    have h : (x+t)%3=0 := by dsimp [t]; omega
    exact ⟨⟨t,by dsimp [t]; omega⟩,mem_union_left _ (mem_filter.mpr ⟨hx,h⟩)⟩

#print axioms extend_free
#print axioms extend_hits
#print axioms all_inputs_61
end Erdos142RamseyResidues
