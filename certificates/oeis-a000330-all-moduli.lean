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



namespace Deldor14.PyramidalSmooth
private def f {K : Type*} [Field K] (A B x : K) := A*x^3+3*x^2+B*x
private def d {K : Type*} [Field K] (A B x : K) := 3*A*x^2+6*x+B

theorem regularize {p : ℕ} [Fact p.Prime] (hp : 5≤p) (A B a b c : ZMod p) :
    ∃ x y z : ZMod p, f A B a+f A B b+f A B c=f A B x+f A B y+f A B z ∧ d A B x≠0 := by
  let F := f A B
  let D := d A B
  change ∃ x y z, F a+F b+F c=F x+F y+F z ∧ D x≠0
  have small (n : ℕ) (hn : 0<n) (lt : n<p) : (n:ZMod p)≠0 :=
    fun h => (not_le.mpr lt) (Nat.le_of_dvd hn ((ZMod.natCast_eq_zero_iff n p).mp h))
  have three : (3:ZMod p)≠0 := small 3 (by decide) (by omega)
  have two : (2:ZMod p)≠0 := small 2 (by decide) (by omega)
  have six : (6:ZMod p)≠0 := (show (6:ZMod p)=2*3 by norm_num) ▸ mul_ne_zero two three
  by_cases ha : D a=0
  swap
  · exact ⟨a,b,c,rfl,ha⟩
  by_cases hb : D b=0
  swap
  · exact ⟨b,a,c,by ring,hb⟩
  by_cases hc : D c=0
  swap
  · exact ⟨c,b,a,by ring,hc⟩
  by_cases zero : A=0
  · subst A
    have ab : a=b := by apply mul_left_cancel₀ six;dsimp [D,d] at ha hb;linear_combination ha-hb
    have ac : a=c := by apply mul_left_cancel₀ six;dsimp [D,d] at ha hc;linear_combination ha-hc
    subst b
    subst c
    obtain ⟨u,v,uv⟩ := ZMod.sq_add_sq p (-1)
    refine ⟨a+1,a+u,a+v,?_,?_⟩
    · dsimp [F,f,D,d] at *
      linear_combination -(1+u+v)*ha - 3*uv
    · intro h
      apply six
      dsimp [D,d] at h ha
      linear_combination h-ha
  · have repair (u : ZMod p) (crit : D u=0) : (∃ v, F v=F u ∧ D v≠0) ∨ A*u+1=0 := by
      let v := -3/A-2*u
      have rel : A*(v+2*u)= -3 := by dsimp [v];field_simp;ring
      by_cases e : A*u+1=0
      · exact Or.inr e
      left
      have eqF : F v=F u := by
        dsimp [F,f,D,d] at *
        linear_combination (v-u)*crit + (v-u)^2*rel
      refine ⟨v,eqF,?_⟩
      intro z
      have q : 9*(A*u+1)^2=0 := by
        dsimp [D,d] at z crit
        linear_combination A*(z-crit) - (3*A*(v-2*u)-3)*rel
      have nine : (9:ZMod p)≠0 := (show (9:ZMod p)=3*3 by norm_num) ▸ mul_ne_zero three three
      exact (mul_ne_zero nine (pow_ne_zero 2 e)) q
    rcases repair a ha with ⟨v,hv,nd⟩|ca
    · exact ⟨v,b,c,by rw [hv],nd⟩
    rcases repair b hb with ⟨v,hv,nd⟩|cb
    · exact ⟨v,a,c,by rw [hv];ring,nd⟩
    rcases repair c hc with ⟨v,hv,nd⟩|cc
    · exact ⟨v,b,a,by rw [hv];ring,nd⟩
    have ab : a=b := by apply mul_left_cancel₀ zero;linear_combination ca-cb
    have ac : a=c := by apply mul_left_cancel₀ zero;linear_combination ca-cc
    subst b
    subst c
    refine ⟨a+1,a-1,a,?_,?_⟩
    · dsimp [F,f];linear_combination -6*ca
    · intro z
      apply mul_ne_zero three zero
      dsimp [D,d] at z ha
      linear_combination z-ha-6*ca

#print axioms regularize
end Deldor14.PyramidalSmooth



namespace Deldor14.CubicLifting
def poly (A B C x : ℤ) := A*x^3+B*x^2+C*x
def slope (A B C x : ℤ) := 3*A*x^2+2*B*x+C

/-- A regular solution modulo a prime lifts, by explicit integer corrections,
to a solution of the same cubic equation modulo every power of this prime. -/
theorem lift {p : ℕ} [Fact p.Prime] (A B C t x : ℤ)
    (base : (p:ℤ) ∣ poly A B C x-t) (reg : ¬(p:ℤ) ∣ slope A B C x) (k : ℕ) :
    ∃ y : ℤ, (p:ℤ)^(k+1) ∣ poly A B C y-t := by
  have strong (k : ℕ) : ∃ y : ℤ, (p:ℤ)^(k+1) ∣ poly A B C y-t ∧ ¬(p:ℤ) ∣ slope A B C y := by
    induction k with
    | zero => exact ⟨x,by simpa using base,reg⟩
    | succ k ih =>
      obtain ⟨y,⟨h,eq⟩,ny⟩ := ih
      let q : ℤ := (p:ℤ)^(k+1)
      have pq : (p:ℤ) ∣ q := dvd_pow_self _ (by omega : k+1≠0)
      let s := slope A B C y
      have sz : (s : ZMod p)≠0 := fun z => ny ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp z)
      let v : ZMod p := -(h:ZMod p)/(s:ZMod p)
      let u : ℤ := v.val
      have cast : (u : ZMod p)=v := by simp [u]
      have dv : (p:ℤ) ∣ h+s*u := by
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
        push_cast
        rw [cast]
        dsimp [v]
        field_simp
        <;> ring
      let E := (3*A*y+B)*u^2+A*q*u^3
      let J := (6*A*y+2*B)*u+3*A*q*u^2
      have e : poly A B C (y+q*u)-t=q*(h+s*u+q*E) := by
        change poly A B C y-t=q*h at eq
        dsimp [poly,s,slope,E] at *
        linear_combination eq
      have d : slope A B C (y+q*u)=slope A B C y+q*J := by
        dsimp [slope,J];ring
      refine ⟨y+q*u,?_,?_⟩
      · change q*(p:ℤ) ∣ _
        rw [e]
        exact mul_dvd_mul_left q (dvd_add dv (dvd_mul_of_dvd_left pq E))
      · rw [d]
        intro bad
        apply ny
        exact (dvd_add_left (dvd_mul_of_dvd_left pq J)).mp bad
  obtain ⟨y,hy,_⟩ := strong k
  exact ⟨y,hy⟩

#print axioms lift
end Deldor14.CubicLifting

namespace Deldor14.Pyramidal
open Deldor14.CubicLifting
private def Q (r x : ℤ) := poly (r-2) 3 (5-r) x
private theorem six_pyr (r x : ℤ) : 6*pyr r x=Q r x := by
  rw [scaled]; dsimp [Q,poly];ring
private def S (m r z : ℤ) := ∃ a b c : ℤ, m ∣ Q r a+Q r b+Q r c-6*z
private theorem big_power {p : ℕ} [Fact p.Prime] (hp : 5≤p) (k : ℕ) (r z : ℤ) :
    S ((p:ℤ)^(k+1)) r z := by
  obtain ⟨a,b,c,h⟩ := local_large hp r z
  let A : ZMod p := (r:ZMod p)-2
  let B : ZMod p := 5-(r:ZMod p)
  let F := PyramidalSmooth.f A B
  have cast (n : ℤ) : (Q r n : ZMod p)=F (n:ZMod p) := by
    dsimp [Q,poly,F,PyramidalSmooth.f,A,B]; push_cast;ring
  have hv : 6*(z:ZMod p)=F a+F b+F c := by
    have v := (ZMod.intCast_eq_intCast_iff ..).mpr (h.mul_left 6)
    rw [mul_add,mul_add,six_pyr,six_pyr,six_pyr] at v
    push_cast at v
    simpa only [cast] using v
  obtain ⟨x,y,w,eq,nd⟩ := PyramidalSmooth.regularize hp A B (a:ZMod p) b c
  have vals (v : ZMod p) : ((v.val:ℤ):ZMod p)=v := by simp
  let t := 6*z-Q r y.val-Q r w.val
  have base : (p:ℤ) ∣ Q r x.val-t := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    dsimp only [t]
    push_cast
    simp only [cast,vals]
    change _=0
    linear_combination -(hv.trans eq)
  have reg : ¬(p:ℤ) ∣ CubicLifting.slope (r-2) 3 (5-r) x.val := by
    intro bad
    have v := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr bad
    apply nd
    dsimp [CubicLifting.slope] at v
    push_cast at v
    simp only [ZMod.natCast_zmod_val] at v
    dsimp [PyramidalSmooth.d,A,B]
    linear_combination v
  obtain ⟨u,hu⟩ := lift (r-2) 3 (5-r) t x.val base reg k
  exact ⟨u,y.val,w.val,by convert hu using 1 <;> dsimp [Q,t] <;> ring⟩
private theorem two_power (k : ℕ) (r z : ℤ) : S (2^(k+1)) r z := by
  have b : (2:ℤ) ∣ poly (r-2) 3 (5-r) 1-6*z := by
    refine ⟨3-3*z,?_⟩;dsimp [poly];ring
  have g : ¬(2:ℤ) ∣ CubicLifting.slope (r-2) 3 (5-r) 1 := by
    dsimp [CubicLifting.slope];ring_nf;omega
  obtain ⟨x,hx⟩ := lift (p:=2) (r-2) 3 (5-r) (6*z) 1 b g k
  exact ⟨x,0,0,by simpa [Q,poly] using hx⟩
private theorem three_power (k : ℕ) (r z : ℤ) : S (3^(k+1)) r z := by
  by_cases h : (3:ℤ) ∣ 5-r
  swap
  · have b : (3:ℤ) ∣ poly (r-2) 3 (5-r) 0-6*z := by refine ⟨-2*z,?_⟩; simp [poly];ring
    have g : ¬(3:ℤ) ∣ CubicLifting.slope (r-2) 3 (5-r) 0 := by simpa [CubicLifting.slope] using h
    obtain ⟨x,hx⟩ := lift (p:=3) (r-2) 3 (5-r) (6*z) 0 b g k
    exact ⟨x,0,0,by simpa [Q,poly] using hx⟩
  obtain ⟨s,hs⟩ := h
  let u := 1-s
  have rr : r=2+3*u := by dsimp [u];omega
  let G := poly u 1 (1-u)
  have fac (x : ℤ) : Q r x=3*G x := by rw [rr];dsimp [Q,poly,G];ring
  have gz : G 0=0 := by simp [G,poly]
  have go : G 1=2 := by simp [G,poly];ring
  have pick (x : ℤ) : ∃ a b : ℤ, (3:ℤ) ∣ G x+G a+G b-2*z := by
    by_cases e : (G x-2*z)%3=0
    · exact ⟨0,0,by rw [gz];omega⟩
    by_cases f : (G x-2*z)%3=1
    · exact ⟨1,0,by rw [go,gz];omega⟩
    · exact ⟨1,1,by rw [go];omega⟩
  have reg : ∃ x : ℤ, ¬(3:ℤ) ∣ CubicLifting.slope u 1 (1-u) x := by
    by_cases e : (3:ℤ) ∣ 1-u
    · refine ⟨1,?_⟩;dsimp [CubicLifting.slope];ring_nf;omega
    · exact ⟨0,by simpa [CubicLifting.slope] using e⟩
  obtain ⟨x,hx⟩ := reg
  obtain ⟨a,b,hab⟩ := pick x
  let t := 2*z-G a-G b
  have base : (3:ℤ) ∣ G x-t := by convert hab using 1 <;> dsimp [t] <;> ring
  obtain ⟨v,hv⟩ := lift (p:=3) u 1 (1-u) t x base hx k
  obtain ⟨w,hw⟩ := hv
  change G v-t=3^(k+1)*w at hw
  refine ⟨v,a,b,3*w,?_⟩
  simp only [fac]; dsimp only [t] at hw
  linear_combination 3*hw
end Deldor14.Pyramidal

namespace Deldor14.Pyramidal
open Deldor14.CubicLifting
private theorem crt (m n : ℕ) (h : m.Coprime n) (x y : ℤ) :
    ∃ w : ℤ, w ≡ x [ZMOD (m:ℤ)] ∧ w ≡ y [ZMOD (n:ℤ)] := by
  obtain ⟨t,ht⟩ := Int.mod_coprime h
  refine ⟨x+(m:ℤ)*t*(y-x),?_,?_⟩
  · rw [mul_assoc];exact Int.modEq_add_fac_self
  · have hv := (ht.mul_right (y-x)).add_left x
    simpa only [one_mul,add_sub_cancel] using hv
private theorem Qcongr (r : ℤ) {m x y : ℤ} (xy : x ≡ y [ZMOD m]) : Q r x ≡ Q r y [ZMOD m] :=
  (((xy.pow 3).mul_left _).add ((xy.pow 2).mul_left _)).add (xy.mul_left _)
private theorem combine (r z : ℤ) {m n : ℕ} (h : m.Coprime n) (hm : S m r z) (hn : S n r z) :
    S (m*n:ℕ) r z := by
  obtain ⟨a,b,c,ab⟩ := hm
  obtain ⟨d,e,f,de⟩ := hn
  obtain ⟨u,um,un⟩ := crt m n h a d
  obtain ⟨v,vm,vn⟩ := crt m n h b e
  obtain ⟨w,wm,wn⟩ := crt m n h c f
  have M := ((Qcongr r um).add (Qcongr r vm)).add (Qcongr r wm)
  have N := ((Qcongr r un).add (Qcongr r vn)).add (Qcongr r wn)
  refine ⟨u,v,w,?_⟩
  push_cast
  apply Int.modEq_iff_dvd.mp
  apply (Int.modEq_and_modEq_iff_modEq_mul (m:=(m:ℤ)) (n:=(n:ℤ)) (by simpa using h)).mp
  exact ⟨(Int.modEq_iff_dvd.mpr ab).trans M.symm,(Int.modEq_iff_dvd.mpr de).trans N.symm⟩
private theorem scaled_moduli (r z : ℤ) (m : ℕ) : m≠0 → S m r z := by
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro _
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    haveI : Fact p.Prime := ⟨hp⟩
    push_cast
    by_cases large : 5≤p
    · exact big_power large k r z
    have hi := hp.two_le
    have no4 : p≠4 := by rintro rfl;exact (by decide : ¬Nat.Prime 4) hp
    have twoThree : p=2 ∨ p=3 := by omega
    rcases twoThree with rfl|rfl
    · exact two_power k r z
    · exact three_power k r z
  | zero => simp
  | one => exact fun _ => ⟨0,0,0,by simp⟩
  | coprime m n hm hn hc im inn =>
    exact fun _ => combine r z hc (im (by omega)) (inn (by omega))
/-- For every integral order and every positive modulus, each residue is a
sum of three generalized pyramidal numbers of that order. -/
theorem every_modulus (r z : ℤ) (m : ℕ) (hm : 0 < m) :
    ∃ a b c : ℤ, z ≡ pyr r a + pyr r b + pyr r c [ZMOD (m:ℤ)] := by
  obtain ⟨a,b,c,t,ht⟩ := scaled_moduli r z (6*m) (by omega)
  push_cast at ht
  rw [← six_pyr,← six_pyr,← six_pyr] at ht
  exact ⟨a,b,c,Int.modEq_iff_dvd.mpr ⟨t,by linarith only [ht]⟩⟩
#print axioms every_modulus
end Deldor14.Pyramidal
