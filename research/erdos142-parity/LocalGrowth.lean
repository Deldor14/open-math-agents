import PrimePower

namespace ProgressionParity

private lemma no_midpoint {B : Finset ℕ} (free : Free (· ∈ B) 3)
    {x y z : ℕ} (hx : x∈B) (hy : y∈B) (hz : z∈B) (eq : x+z=2*y) : x=y := by
  by_contra neq
  by_cases lt : x<y
  · apply free x (y-x) (by omega)
    simpa [Run,show x+(y-x)=y by omega,show y+(y-x)=z by omega] using And.intro hx (And.intro hy hz)
  · apply free z (y-z) (by omega)
    simpa [Run,show z+(y-z)=y by omega,show y+(y-z)=x by omega] using And.intro hz (And.intro hy hx)

open Set.IsAPOfLengthFree in
theorem digit_product {k m b : ℕ} (hk : 3≤k) (hm : 0<m) (space : 2*(m-1)<b) (N : ℕ) :
    maxCard k N * maxCard 3 m ≤ maxCard k (b*N) := by
  have bp : 0<b := by omega
  obtain ⟨A,ha,fa,ca⟩ := attained (by omega : 1<k) N
  obtain ⟨B,hb,fb,cb⟩ := attained (by decide : 1<3) m
  let enc := fun u : ℕ × ℕ => block b (u.1,u.2-1)
  let C := (A ×ˢ B).image enc
  have decode {u : ℕ × ℕ} (hu : u∈A ×ˢ B) :
      (enc u-1)/b+1=u.1 ∧ (enc u-1)%b+1=u.2 := by
    obtain ⟨ax,by'⟩ := Finset.mem_product.mp hu
    have xh := (Finset.mem_Icc.mp (ha ax)).1
    obtain ⟨yl,yh⟩ := Finset.mem_Icc.mp (hb by')
    obtain ⟨one,two⟩ := block_decode bp xh (show u.2-1<b by omega)
    exact ⟨one,by change (block b (u.1,u.2-1)-1)%b+1=u.2;omega⟩
  have info {z : ℕ} (hz : z∈C) : z∈Finset.Icc 1 (b*N) ∧ (z-1)/b+1 ∈ A ∧ (z-1)%b+1 ∈ B := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨ax,by'⟩ := Finset.mem_product.mp hu
    obtain ⟨dx,dy⟩ := decode hu
    obtain ⟨xl,xh⟩ := Finset.mem_Icc.mp (ha ax)
    obtain ⟨yl,yh⟩ := Finset.mem_Icc.mp (hb by')
    have upper : b*(u.1-1)+b ≤ b*N := by
      rw [← Nat.mul_succ]
      exact Nat.mul_le_mul_left _ (by omega)
    exact ⟨Finset.mem_Icc.mpr ⟨by simp [enc,block],by dsimp [enc,block];omega⟩,dx ▸ ax,dy ▸ by'⟩
  have cc : C.card=A.card*B.card := by
    dsimp only [C]
    rw [Finset.card_image_of_injOn,Finset.card_product]
    intro u hu v hv eq
    obtain ⟨ux,uy⟩ := decode hu
    obtain ⟨vx,vy⟩ := decode hv
    exact Prod.ext (ux.symm.trans ((congrArg (fun z => (z-1)/b+1) eq).trans vx))
      (uy.symm.trans ((congrArg (fun z => (z-1)%b+1) eq).trans vy))
  have free : Free (· ∈ C) k := by
    intro a d hd run
    have H := (run_iff_forall _ _ _ _).mp run
    have h0 : a∈C := by simpa using H 0 (by omega)
    have h1 : a+d∈C := by simpa using H 1 (by omega)
    have h2 : a+2*d∈C := H 2 (by omega)
    have first := (Finset.mem_Icc.mp (info h0).1).1
    let u := (a-1)%b
    let v := (a+d-1)%b
    let w := (a+2*d-1)%b
    have hu : u+1∈B := (info h0).2.2
    have hv : v+1∈B := (info h1).2.2
    have hw : w+1∈B := (info h2).2.2
    have uHi := (Finset.mem_Icc.mp (hb hu)).2
    have vHi := (Finset.mem_Icc.mp (hb hv)).2
    have wHi := (Finset.mem_Icc.mp (hb hw)).2
    have con : u+w ≡ v+v [MOD b] := by
      have A : u ≡ a-1 [MOD b] := Nat.mod_modEq _ _
      have B' : v ≡ a+d-1 [MOD b] := Nat.mod_modEq _ _
      have C' : w ≡ a+2*d-1 [MOD b] := Nat.mod_modEq _ _
      exact (A.add C').trans ((show a-1+(a+2*d-1)=(a+d-1)+(a+d-1) by omega) ▸ (B'.add B').symm)
    have eq := con.eq_of_lt_of_lt (by omega) (by omega)
    have fixed := no_midpoint fb hu hv hw (by omega)
    have step : b ∣ d := by
      have h : (a-1)+d ≡ (a-1)+0 [MOD b] := by
        change ((a-1)+d)%b=((a-1)+0)%b
        rw [show a-1+d=a+d-1 by omega,Nat.add_zero]
        change v=u
        omega
      exact Nat.modEq_zero_iff_dvd.mp (h.add_left_cancel' (a-1))
    obtain ⟨e,rfl⟩ := step
    apply fa ((a-1)/b+1) e (by by_contra! he; simp [show e=0 by omega] at hd)
    apply (run_iff_forall _ _ _ _).mpr
    intro i hi
    have mem := (info (H i hi)).2.1
    have id : a+i*(b*e)-1 = a-1+b*(i*e) := by rw [Nat.mul_left_comm i b e];omega
    rw [id,Nat.add_mul_div_left _ _ bp] at mem
    rwa [show (a-1)/b+1+i*e=(a-1)/b+i*e+1 by omega]
  have bnd := bound_witness (by omega : 1<k) C (fun _ hz => (info hz).1) free
  rwa [cc,ca,cb] at bnd

open Set.IsAPOfLengthFree in
theorem interval_mono {k M N : ℕ} (hk : 1<k) (le : M≤N) : maxCard k M ≤ maxCard k N := by
  obtain ⟨A,ha,fa,ca⟩ := attained hk M
  rw [← ca]
  exact bound_witness hk A (ha.trans (Finset.Icc_subset_Icc_right le)) fa

open Set.IsAPOfLengthFree in
theorem interval_subadditive {k : ℕ} (hk : 1<k) (M N : ℕ) :
    maxCard k (M+N) ≤ maxCard k M+maxCard k N := by
  obtain ⟨A,ha,fa,ca⟩ := attained hk (M+N)
  let L := A.filter (·≤M)
  let H := A.filter (fun x => ¬x≤M)
  let T := H.image (·-M)
  have lc : L.card ≤ maxCard k M := by
    apply bound_witness hk
    · intro x hx
      obtain ⟨ax,le⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp (ha ax)).1,le⟩
    · intro a d hd run
      apply fa a d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      exact (Finset.mem_filter.mp ((run_iff_forall _ _ _ _).mp run i hi)).1
  have tc : T.card=H.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy eq
    have xl := (Finset.mem_filter.mp hx).2
    have yl := (Finset.mem_filter.mp hy).2
    change x-M=y-M at eq
    omega
  have hc : T.card ≤ maxCard k N := by
    apply bound_witness hk
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨ax,high⟩ := Finset.mem_filter.mp hx
      have upper := (Finset.mem_Icc.mp (ha ax)).2
      exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
    · intro a d hd run
      apply fa (a+M) d hd
      apply (run_iff_forall _ _ _ _).mpr
      intro i hi
      obtain ⟨x,hx,eq⟩ := Finset.mem_image.mp ((run_iff_forall _ _ _ _).mp run i hi)
      obtain ⟨ax,high⟩ := Finset.mem_filter.mp hx
      change x-M=a+i*d at eq
      rwa [show a+M+i*d=x by omega]
  have sum : L.card+H.card=A.card := @Finset.card_filter_add_card_filter_not ℕ A (·≤M) _ _
  omega

open Set.IsAPOfLengthFree in
theorem relative_increment {k m N H : ℕ} (hk : 3≤k) (hm : 0<m)
    (fits : (2*m-1)*H ≤ N) :
    maxCard 3 m * (maxCard k (N+H)-maxCard k N) ≤ maxCard k N := by
  have d := digit_product hk hm (show 2*(m-1)<2*m-1 by omega) H
  have le := interval_mono (by omega : 1<k) fits
  have sub := interval_subadditive (by omega : 1<k) N H
  exact (Nat.mul_le_mul_left _ (show maxCard k (N+H)-maxCard k N ≤ maxCard k H by omega)).trans
    ((Nat.mul_comm (maxCard 3 m) (maxCard k H)) ▸ d.trans le)

#print axioms relative_increment
end ProgressionParity
