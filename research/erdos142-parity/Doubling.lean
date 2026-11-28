import UpstreamParity

namespace ProgressionParity

private abbrev sizes (k N : ℕ) : Set ℕ :=
  {Finset.card S | (S) (_ : S ⊆ Finset.Icc 1 N) (_ : (S : Set ℕ).IsAPOfLengthFree k)}

private theorem bounded (k N : ℕ) : BddAbove (sizes k N) := by
  refine ⟨(Finset.Icc 1 N).card, ?_⟩
  rintro m ⟨S, hs, _, rfl⟩
  exact Finset.card_le_card hs

theorem attained {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ Free (· ∈ S) k ∧
      S.card = Set.IsAPOfLengthFree.maxCard k N := by
  have emptyFree : Free (fun x : ℕ => x ∈ (∅ : Finset ℕ)) k := by
    intro a d _ h
    exact Finset.notMem_empty _ ((run_iff_forall _ a d k).mp h 0 (by omega))
  have hn : (sizes k N).Nonempty :=
    ⟨0,∅,Finset.empty_subset _, (upstream_iff_free _ hk).mpr emptyFree, rfl⟩
  obtain ⟨S, hsub, hf, he⟩ := Nat.sSup_mem hn (bounded k N)
  exact ⟨S,hsub,(upstream_iff_free _ hk).mp hf,he⟩

private def sparse (x : ℕ) := 4*x-3

private theorem construction_free {k : ℕ} (hk : 4 ≤ k) (A B : Finset ℕ)
    (positive : ∀ x ∈ B, 1 ≤ x) (ha : Free (· ∈ A) k) (hb : Free (· ∈ B) k) :
    Free (· ∈ (A.image (2*·) ∪ B.image sparse)) k := by
  let C := A.image (2*·) ∪ B.image sparse
  have parts {z : ℕ} (hz : z ∈ C) :
      (∃ x ∈ A, 2*x=z) ∨ (∃ y ∈ B, 4*y-3=z) := by
    rcases Finset.mem_union.mp hz with he|ho
    · exact Or.inl (Finset.mem_image.mp he)
    · exact Or.inr (Finset.mem_image.mp ho)
  have nod3 {z : ℕ} (hz : z ∈ C) : z%4≠3 := by
    rcases parts hz with ⟨x,hx,rfl⟩|⟨y,hy,rfl⟩
    · omega
    · have := positive y hy; omega
  have evenMem {z : ℕ} (hz : z ∈ C) (h : z%2=0) : z/2 ∈ A := by
    rcases parts hz with ⟨x,hx,rfl⟩|⟨y,hy,rfl⟩
    · simpa using hx
    · have := positive y hy; omega
  have oddMem {z : ℕ} (hz : z ∈ C) (h : z%2=1) : z%4=1 ∧ z/4+1 ∈ B := by
    rcases parts hz with ⟨x,hx,rfl⟩|⟨y,hy,rfl⟩
    · omega
    · have := positive y hy
      refine ⟨by omega, ?_⟩
      rwa [show (4*y-3)/4+1=y by omega]
  intro a d hd h
  have allp : ∀ i < k, a+i*d ∈ C := (run_iff_forall _ a d k).mp h
  have p₀ : a ∈ C := by simpa using allp 0 (by omega)
  have p₁ : a+d ∈ C := by simpa using allp 1 (by omega)
  have dEven : d%2=0 := by
    have h₀ := nod3 p₀
    have h₁ := nod3 p₁
    have h₂ := nod3 (allp 2 (by omega))
    have h₃ := nod3 (allp 3 (by omega))
    rw [Nat.add_mod] at h₁ h₂ h₃
    rw [Nat.mul_mod] at h₂ h₃
    have ah : a%4=0 ∨ a%4=1 ∨ a%4=2 ∨ a%4=3 := by omega
    have dh : d%4=0 ∨ d%4=1 ∨ d%4=2 ∨ d%4=3 := by omega
    rcases ah with h|h|h|h <;> rcases dh with t|t|t|t <;> omega
  by_cases aEven : a%2=0
  · apply ha (a/2) (d/2) (by omega)
    apply (run_iff_forall _ _ _ _).mpr
    intro i hi
    have eq : a+i*d=2*(a/2+i*(d/2)) := by
      calc
        a+i*d = 2*(a/2)+i*(2*(d/2)) := congrArg₂ Nat.add (by omega) (congrArg (i*·) (by omega))
        _ = _ := by simp only [Nat.mul_add, Nat.mul_left_comm]
    have hp := evenMem (allp i hi) (by omega)
    rwa [eq, Nat.mul_div_cancel_left _ (by decide : 0 < 2)] at hp
  · have s₀ := (oddMem p₀ (by omega)).1
    have s₁ := (oddMem p₁ (by omega)).1
    have dFour : d%4=0 := by omega
    apply hb (a/4+1) (d/4) (by omega)
    apply (run_iff_forall _ _ _ _).mpr
    intro i hi
    have eq : a+i*d=4*(a/4+i*(d/4))+1 := by
      calc
        a+i*d = (4*(a/4)+1)+i*(4*(d/4)) :=
          congrArg₂ Nat.add (by omega) (congrArg (i*·) (by omega))
        _ = _ := by simp only [Nat.mul_add, Nat.mul_left_comm, Nat.add_assoc, Nat.add_comm]
    have hp := (oddMem (allp i hi) (by omega)).2
    have fix : (a+i*d)/4+1 = (a/4+1)+i*(d/4) := by omega
    rwa [fix] at hp

open Set.IsAPOfLengthFree in
theorem doubling_recurrence {k : ℕ} (hk : 4 ≤ k) (N : ℕ) :
    maxCard k N + maxCard k ((N+1)/2) ≤ maxCard k (2*N) := by
  obtain ⟨A,hA,fA,cA⟩ := attained (by omega : 1<k) N
  obtain ⟨B,hB,fB,cB⟩ := attained (by omega : 1<k) ((N+1)/2)
  have bp : ∀ x ∈ B, 1 ≤ x := fun x h => (Finset.mem_Icc.mp (hB h)).1
  let C := A.image (2*·) ∪ B.image sparse
  have dis : Disjoint (A.image (2*·)) (B.image sparse) := by
    apply Finset.disjoint_left.mpr
    rintro z hz he
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp he
    have := bp y hy
    unfold sparse at eq
    omega
  have hc : C.card = A.card+B.card := by
    dsimp only [C]
    rw [Finset.card_union_of_disjoint dis,Finset.card_image_of_injective,Finset.card_image_of_injective]
    · intro x y h; unfold sparse at h; omega
    · intro x y h; change 2*x=2*y at h; omega
  have cs : C ⊆ Finset.Icc 1 (2*N) := by
    intro z hz
    rcases Finset.mem_union.mp hz with h|h
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp (hA hx)
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp h
      obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp (hB hx)
      unfold sparse
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  change _ ≤ sSup (sizes k (2*N))
  apply le_csSup (bounded k (2*N))
  exact ⟨C,cs,(upstream_iff_free _ (by omega)).mpr (construction_free hk A B bp fA fB),by rw [hc,cA,cB]⟩

open Set.IsAPOfLengthFree in
theorem bound_witness {k q : ℕ} (hk : 1<k) (A : Finset ℕ)
    (hs : A ⊆ Finset.Icc 1 q) (hf : Free (· ∈ A) k) : A.card ≤ maxCard k q :=
  le_csSup (bounded k q) ⟨A,hs,(upstream_iff_free _ hk).mpr hf,rfl⟩

open Set.IsAPOfLengthFree in
theorem halving_upper {k : ℕ} (hk : 1<k) (N : ℕ) :
    maxCard k N ≤ 2*maxCard k ((N+1)/2) := by
  let q := (N+1)/2
  obtain ⟨A,hA,fA,cA⟩ := attained hk N
  let B := A.filter (· ≤ q)
  let H := A.filter (fun x => ¬ x ≤ q)
  let D := H.image (fun x => x-q)
  have lower : B.card ≤ maxCard k q := by
    apply bound_witness hk
    · intro x hx
      obtain ⟨a,b⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (hA a)).1,b⟩
    · intro a d hd h
      apply fA a d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      exact (Finset.mem_filter.mp ((run_iff_forall _ _ _ _).mp h i hi)).1
  have dc : D.card=H.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy eq
    have ax := (Finset.mem_filter.mp hx).2
    have ay := (Finset.mem_filter.mp hy).2
    change x-q=y-q at eq
    omega
  have upper : D.card ≤ maxCard k q := by
    apply bound_witness hk
    · intro z hz
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx,hy⟩ := Finset.mem_filter.mp ha
      have leN := (Finset.mem_Icc.mp (hA hx)).2
      dsimp [q] at *
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · intro a d hd h
      apply fA (a+q) d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ((run_iff_forall _ _ _ _).mp h i hi)
      obtain ⟨hA',high⟩ := Finset.mem_filter.mp hx
      change x-q=a+i*d at eq
      rwa [show a+q+i*d=x by omega]
  have sum : B.card+H.card=A.card := @Finset.card_filter_add_card_filter_not ℕ A (· ≤ q) _ _
  change maxCard k N ≤ 2*maxCard k q
  omega

open Set.IsAPOfLengthFree in
theorem three_halves_doubling {k : ℕ} (hk : 4≤k) (N : ℕ) :
    3*maxCard k N ≤ 2*maxCard k (2*N) := by
  have h₁ := doubling_recurrence hk N
  have h₂ := halving_upper (by omega : 1<k) N
  omega

#print axioms doubling_recurrence
#print axioms three_halves_doubling
end ProgressionParity
