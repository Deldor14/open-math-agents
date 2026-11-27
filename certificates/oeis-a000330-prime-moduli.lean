import Mathlib

namespace Deldor14.Pyramidal
open Finset Polynomial
open scoped Pointwise

def pyr (r n : ℤ) := n*(n+1)*((r-2)*n-(r-5))/6
theorem scaled (r n : ℤ) : 6*pyr r n=n*(n+1)*((r-2)*n-(r-5)) := by
  have total (a b : ℤ) (ha : 0≤a) (ha' : a<6) (hb : 0≤b) (hb' : b<6) :
      (a*(a+1)*((b-2)*a-(b-5)))%6=0 := by interval_cases a <;> interval_cases b <;> decide
  have repr (x : ℤ) : x%6 ≡ x [ZMOD 6] := Int.mod_modEq x 6
  have eq := ((repr n).mul ((repr n).add (Int.ModEq.refl 1))).mul
    ((((repr r).sub (Int.ModEq.refl 2)).mul (repr n)).sub ((repr r).sub (Int.ModEq.refl 5)))
  have h := total (n%6) (r%6) (by omega) (by omega) (by omega) (by omega)
  unfold Int.ModEq at eq
  have dv : 6 ∣ n*(n+1)*((r-2)*n-(r-5)) := Int.dvd_of_emod_eq_zero (Eq.trans (Eq.symm eq) h)
  unfold pyr
  rw [mul_comm,Int.ediv_mul_cancel dv]

theorem square (r n : ℤ) : pyr r n+pyr r (-n)=n^2 := by
  have a := scaled r n
  have b := scaled r (-n)
  linarith only [a,b]

private theorem fiberBound {p : ℕ} [Fact p.Prime] (F : (ZMod p)[X]) (hpos : 0<F.degree) :
    p ≤ F.natDegree*(univ.image F.eval).card := by
  classical
  have h := card_le_mul_card_image (f:=F.eval) univ F.natDegree (by
    intro v _
    have hn : F-C v≠0 := fun he => (not_le_of_gt hpos) ((sub_eq_zero.mp he) ▸ degree_C_le)
    have sub : (univ.filter (fun t => F.eval t=v)) ⊆ (F-C v).roots.toFinset := by
      intro t ht
      have e := (mem_filter.mp ht).2
      simpa only [Multiset.mem_toFinset,mem_roots hn,IsRoot,eval_sub,eval_C,sub_eq_zero] using e
    exact (card_le_card sub).trans ((Multiset.toFinset_card_le _).trans (card_roots_sub_C' hpos)))
  simpa [ZMod.card] using h

private theorem triple_image {p : ℕ} [Fact p.Prime] (hp : 5≤p) (F : (ZMod p)[X])
    (hpos : 0<F.degree) (hd : F.natDegree≤3)
    (alt : F.natDegree≤2 ∨ ∃ c, ∀ x, F.eval (2*c-x)=2*F.eval c-F.eval x) (z : ZMod p) :
    ∃ a b c : ZMod p, z=F.eval a+F.eval b+F.eval c := by
  classical
  let s : Finset (ZMod p) := univ.image F.eval
  let T := s+s+s
  have non : s.Nonempty := ⟨F.eval 0,mem_image_of_mem _ (mem_univ _)⟩
  have bnd : p≤F.natDegree*s.card := fiberBound F hpos
  have b3 := bnd.trans (Nat.mul_le_mul_right s.card hd)
  have d := ZMod.cauchy_davenport (Fact.out : Nat.Prime p) non non
  have t := ZMod.cauchy_davenport (Fact.out : Nat.Prime p) (non.add non) non
  have sp := non.card_pos
  have repr (y : ZMod p) : y∈T ↔ ∃ a b c : ZMod p, y=F.eval a+F.eval b+F.eval c := by
    constructor
    · intro hy
      obtain ⟨w,hw,c,hc,rfl⟩ := mem_add.mp hy
      obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hw
      obtain ⟨i,_,rfl⟩ := mem_image.mp ha
      obtain ⟨j,_,rfl⟩ := mem_image.mp hb
      obtain ⟨k,_,rfl⟩ := mem_image.mp hc
      exact ⟨i,j,k,rfl⟩
    · rintro ⟨a,b,c,rfl⟩
      exact add_mem_add (add_mem_add (mem_image_of_mem _ (mem_univ a)) (mem_image_of_mem _ (mem_univ b)))
        (mem_image_of_mem _ (mem_univ c))
  apply (repr _).mp
  have prime := (Fact.out : Nat.Prime p)
  have pm : p%3≠0 := by
    intro e
    have n := (Nat.prime_dvd_prime_iff_eq Nat.prime_three prime).mp (Nat.dvd_of_mod_eq_zero e)
    omega
  have count : Tᶜ.card=p-T.card := by rw [Finset.card_compl,ZMod.card]
  have tc : T.card=(s+s+s).card := rfl
  rcases alt with h|⟨c,reflect⟩
  · have b2 := bnd.trans (Nat.mul_le_mul_right s.card h)
    by_contra hz
    have a := card_pos.mpr (show Tᶜ.Nonempty from ⟨z,mem_compl.mpr hz⟩)
    omega
  · by_contra hz
    have low : Tᶜ.card≤1 := by omega
    have symm (y : ZMod p) (hy : y∈T) : 6*F.eval c-y∈T := by
      obtain ⟨i,j,k,rfl⟩ := (repr _).mp hy
      apply (repr _).mpr
      refine ⟨2*c-i,2*c-j,2*c-k,?_⟩
      rw [reflect,reflect,reflect]
      ring
    have notR : 6*F.eval c-z∉T := by
      intro hr
      have hv := symm _ hr
      apply hz
      convert hv using 1 <;> ring
    have eq := card_le_one_iff.mp low (mem_compl.mpr hz) (mem_compl.mpr notR)
    have nz : (2 : ZMod p)≠0 := by exact_mod_cast (show ¬ p ∣ 2 by intro ht;have := Nat.le_of_dvd (by decide : 0<2) ht;omega) |> (ZMod.natCast_eq_zero_iff 2 p).not.mpr
    apply hz
    apply (repr _).mpr
    refine ⟨c,c,c,mul_left_cancel₀ nz ?_⟩
    linear_combination eq

private noncomputable def form {p : ℕ} (r : ZMod p) : (ZMod p)[X] :=
  C (r-2)*X^3+C 3*X^2+C (5-r)*X
private theorem evalForm {p : ℕ} (r x : ZMod p) :
    (form r).eval x=(r-2)*x^3+3*x^2+(5-r)*x := by simp [form]

theorem local_large {p : ℕ} [Fact p.Prime] (hp : 5≤p) (r z : ℤ) :
    ∃ a b c : ℤ, z ≡ pyr r a+pyr r b+pyr r c [ZMOD (p:ℤ)] := by
  classical
  have nzd (n : ℕ) (ht : 0<n) (lt : n<p) : (n : ZMod p)≠0 :=
    fun eq => (not_le.mpr lt) (Nat.le_of_dvd ht ((ZMod.natCast_eq_zero_iff _ _).mp eq))
  have six : (6 : ZMod p)≠0 := by
    have h2 : (2 : ZMod p)≠0 := nzd 2 (by decide) (by omega)
    have h3 : (3 : ZMod p)≠0 := nzd 3 (by decide) (by omega)
    exact (show (6 : ZMod p)=2*3 by norm_num) ▸ mul_ne_zero h2 h3
  let R : ZMod p := r
  let F := form R
  have pos : 0<F.degree := by
    have co : F.coeff 2=3 := by simp only [F,form,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X];norm_num
    have nz : F.coeff 2≠0 := by rw [co];exact nzd 3 (by decide) (by omega)
    exact natDegree_pos_iff_degree_pos.mp (lt_of_lt_of_le (by decide : 0<2) (le_natDegree_of_ne_zero nz))
  have lem (d : ℕ) (h : d≥1) : (C (5-R)*X).natDegree≤d :=
    (by simpa only [pow_one] using natDegree_C_mul_X_pow_le (5-R) 1 : (C (5-R)*X).natDegree≤1).trans h
  have d3 : F.natDegree≤3 := by
    unfold F form
    apply (natDegree_add_le _ _).trans
    refine max_le ((natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) ?_)) (lem 3 (by decide))
    exact (natDegree_C_mul_X_pow_le (3:ZMod p) 2).trans (by decide)
  have alt : F.natDegree≤2 ∨ ∃ c, ∀ x, F.eval (2*c-x)=2*F.eval c-F.eval x := by
    by_cases e : R-2=0
    · left
      simp only [F,form,e,map_zero,zero_mul,zero_add]
      exact (natDegree_add_le _ _).trans (max_le (natDegree_C_mul_X_pow_le _ _) (lem 2 (by decide)))
    · right
      let c := -(R-2)⁻¹
      have h : (R-2)*c= -1 := by simp [c,e]
      refine ⟨c,fun x => ?_⟩
      simp only [F,evalForm]
      linear_combination (6*(c-x)^2)*h
  obtain ⟨a,b,c,eq⟩ := triple_image hp F pos d3 alt (6*(z:ZMod p))
  have cast (x : ZMod p) : 6*(pyr r (x.val:ℤ) : ZMod p)=F.eval x := by
    have h := congrArg (fun n : ℤ => (n:ZMod p)) (scaled r (x.val:ℤ))
    push_cast at h
    simp only [ZMod.natCast_zmod_val] at h
    change _=(form R).eval x
    rw [evalForm]
    dsimp [R]
    linear_combination h
  refine ⟨a.val,b.val,c.val,(ZMod.intCast_eq_intCast_iff ..).mp ?_⟩
  push_cast
  apply mul_left_cancel₀ six
  rw [mul_add,mul_add,cast,cast,cast]
  exact eq
theorem local_all (r z : ℤ) (p : ℕ) (hp : p.Prime) :
    ∃ a b c : ℤ, z ≡ pyr r a+pyr r b+pyr r c [ZMOD (p:ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases big : 5≤p
  · exact local_large big r z
  have hi := hp.two_le
  have q : p=2 ∨ p=3 := by
    have h : p≠4 := by rintro rfl;exact (by decide : ¬Nat.Prime 4) hp
    omega
  have h₀ : pyr r 0=0 := by simp [pyr]
  have h₁ : pyr r 1=1 := by have h := scaled r 1;linarith
  rcases q with rfl|rfl
  · by_cases e : z%2=0
    · exact ⟨0,0,0,by simp [h₀,Int.ModEq,e]⟩
    · exact ⟨1,0,0,by simp only [h₁,h₀,add_zero,Int.ModEq];omega⟩
  · by_cases zero : z%3=0
    · exact ⟨0,0,0,by simp [h₀,Int.ModEq,zero]⟩
    by_cases one : z%3=1
    · exact ⟨1,0,0,by simp [h₁,h₀,Int.ModEq,one]⟩
    · exact ⟨1,1,0,by simp only [h₁,h₀,add_zero,Int.ModEq];omega⟩

#print axioms local_all
#print axioms square
end Deldor14.Pyramidal
