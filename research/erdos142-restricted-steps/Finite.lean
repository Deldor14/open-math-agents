import Mathlib.Tactic
import Mathlib.Combinatorics.Additive.AP.Three.Defs

namespace Erdos142Pullback

/-- Vanishing second differences on a finite interval give a single signed step. -/
theorem arithmetic (f : ℕ → ℤ) (k : ℕ)
    (h : ∀ i, i+2<k → f i+f (i+2)=2*f (i+1)) :
    ∀ i, i<k → f i=f 0+(i:ℤ)*(f 1-f 0) := by
  have step (i : ℕ) (hi : i+1<k) : f (i+1)-f i=f 1-f 0 := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have last := ih (by omega)
      have second := h i (by omega)
      change f (i+2)-f (i+1)=f 1-f 0
      omega
  intro i hi
  induction i with
  | zero => simp
  | succ i ih =>
    have prev := ih (by omega)
    have last := step i hi
    push_cast
    linarith only [prev,last]

/-- A multiple of b in the open interval (-b,b) is zero, also with a
nonconstant symbolic divisor. -/
theorem no_wrap {b v t : ℤ} (hb : 0<b) (bounds : -b<v ∧ v<b)
    (rep : v=b*t) : v=0 := by
  by_cases pos : 0<t
  · have ht : 1≤t := by omega
    have h := mul_le_mul_of_nonneg_left ht hb.le
    omega
  by_cases neg : t<0
  · have ht : t≤-1 := by omega
    have h := mul_le_mul_of_nonneg_left ht hb.le
    omega
  have : t=0 := by omega
  simp [rep,this]

/-- No progression can lie in the selected cells if the seed has only
constant signed k-progressions and every representative of the tested
grid step has magnitude at least P/(k-1). -/
theorem pullback_impossible (k : ℕ) (P n q c w : ℤ)
    (hk : 3≤k) (hP : 0<P) (hn : 2≤n) (hq : q=2*n-1)
    (S : Set ℤ) (labels errors wraps : ℕ → ℤ)
    (rangeS : ∀ x ∈ S, 0≤x ∧ x<n)
    (seed : ∀ a t : ℤ, (∀ i : ℕ, i<k → a+(i:ℤ)*t ∈ S) → t=0)
    (inside : ∀ i, i<k → labels i ∈ S)
    (rangeE : ∀ i, i<k → 0≤errors i ∧ errors i<P)
    (rep : ∀ i, i<k → 2*P*labels i+errors i =
      c+(i:ℤ)*w+2*P*q*wraps i)
    (far : ∀ z : ℤ, P≤((k:ℤ)-1)*|w+2*P*q*z|) : False := by
  have second (i : ℕ) (hi : i+2<k) :
      labels i+labels (i+2)=2*labels (i+1) ∧
      errors i+errors (i+2)=2*errors (i+1) := by
    have r0 := rep i (by omega)
    have r1 := rep (i+1) (by omega)
    have r2 := rep (i+2) hi
    push_cast at r1 r2
    let z := wraps i+wraps (i+2)-2*wraps (i+1)
    let d := labels i+labels (i+2)-2*labels (i+1)
    let e := errors i+errors (i+2)-2*errors (i+1)
    have eq : e=(2*P)*(q*z-d) := by
      dsimp [d,e,z]
      linear_combination r0-2*r1+r2
    have er0 := rangeE i (by omega)
    have er1 := rangeE (i+1) (by omega)
    have er2 := rangeE (i+2) hi
    have zero : e=0 := no_wrap (by omega) (by dsimp [e]; omega) eq
    have prod : q*z-d=0 := (mul_eq_zero.mp (eq.symm.trans zero)).resolve_left (by omega)
    have s0 := rangeS _ (inside i (by omega))
    have s1 := rangeS _ (inside (i+1) (by omega))
    have s2 := rangeS _ (inside (i+2) hi)
    have dl : d=0 := no_wrap (by omega) (by dsimp [d]; omega) (by omega : d=q*z)
    dsimp [d] at dl
    dsimp [e] at zero
    omega
  have ls := arithmetic labels k (fun i hi => (second i hi).1)
  have es := arithmetic errors k (fun i hi => (second i hi).2)
  have fixed := seed (labels 0) (labels 1-labels 0) (fun i hi => by
    rw [← ls i hi]
    exact inside i hi)
  have rep0 := rep 0 (by omega)
  have rep1 := rep 1 (by omega)
  norm_num at rep0 rep1
  have lbl : labels 1=labels 0 := by omega
  rw [lbl] at rep1
  have first : errors 1-errors 0=w+2*P*q*(wraps 1-wraps 0) := by
    linear_combination rep1-rep0
  have bound := far (wraps 1-wraps 0)
  rw [← first] at bound
  have endpoint := es (k-1) (by omega)
  rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one] at endpoint
  have left := rangeE 0 (by omega)
  have right := rangeE (k-1) (by omega)
  by_cases pos : 0≤errors 1-errors 0
  · rw [abs_of_nonneg pos] at bound
    linarith only [left.1,right.2,bound,endpoint]
  · rw [abs_of_neg (lt_of_not_ge pos)] at bound
    linarith only [left.2,right.1,bound,endpoint]

#print axioms pullback_impossible
end Erdos142Pullback


namespace Erdos142Counting
open Finset

/-- Varying the shift achieves the expected density in every finite test set. -/
theorem some_shift {X G : Type*} [AddGroup G] [Fintype G] [DecidableEq G]
    (T : Finset X) (f : X → G) (U : Finset G) :
    ∃ b : G, T.card * U.card ≤ Fintype.card G * (T.filter (fun x => f x+b ∈ U)).card := by
  classical
  have one (x : X) : (∑ b : G, if f x+b∈U then 1 else 0 : ℕ)=U.card := by
    calc
      _ = ∑ y : G, if y∈U then 1 else 0 := Equiv.sum_comp (Equiv.addLeft (f x)) _
      _ = _ := by simp
  have total : (∑ b : G, (T.filter (fun x => f x+b∈U)).card)=T.card*U.card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
    simp [one]
  by_contra! no
  have less := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty : (Finset.univ : Finset G).Nonempty)
    (fun b _ => no b)
  have lhs : (∑ b : G, Fintype.card G * (T.filter (fun x => f x+b∈U)).card)
      = Fintype.card G * (T.card * U.card) := by rw [← Finset.mul_sum,total]
  have rhs : (∑ _b : G, T.card * U.card) = Fintype.card G * (T.card * U.card) := by simp
  rw [lhs,rhs] at less
  exact (lt_irrefl _ less)



/-- There is a nonzero multiplier for which every signed representative of
every tested residue has large magnitude. The proof counts the forbidden
nonzero residues in both directions. -/
theorem multiplier (p h : ℕ) [Fact p.Prime] (D : Finset ℕ)
    (hp : 2≤p) (hm : D.card<h) (hd : ∀ d∈D, (d : ZMod p)≠0) :
    ∃ a : ZMod p, a≠0 ∧ ∀ d∈D, ∀ v : ℤ, (v : ZMod p)=a*d → p≤2*h*v.natAbs := by
  classical
  let t := (p-1)/(2*h)
  let plus : Finset (ZMod p) := (range t).image fun i => ((i+1:ℕ) : ZMod p)
  let bad := plus ∪ plus.image Neg.neg
  let allBad := insert 0 (D.biUnion fun d => bad.image (fun y => y/(d : ZMod p)))
  have count1 : plus.card≤t := Finset.card_range t ▸ Finset.card_image_le
  have count2 : bad.card≤2*t := by
    have negCount : (plus.image Neg.neg).card ≤ plus.card := Finset.card_image_le
    have := Finset.card_union_le plus (plus.image Neg.neg)
    dsimp [bad]
    omega
  have count3 : allBad.card ≤ 1 + D.card*(2*t) := by
    have all := Finset.card_biUnion_le (s:=D) (t:=fun d => bad.image (fun y => y/(d : ZMod p)))
    have each : (∑ d∈D, (bad.image (fun y => y/(d : ZMod p))).card) ≤ D.card*(2*t) := by
      calc
        _ ≤ ∑ _d∈D, 2*t := Finset.sum_le_sum (fun _ _ => Finset.card_image_le.trans count2)
        _ = _ := by simp
    have ins := Finset.card_insert_le 0 (D.biUnion fun d => bad.image (fun y => y/(d : ZMod p)))
    dsimp [allBad]
    omega
  have few : D.card * (2*t) < p-1 := by
    by_cases hzero : t=0
    · simp [hzero]; omega
    have mul := Nat.mul_lt_mul_of_pos_right hm (show 0<2*t by omega)
    have le := Nat.mul_div_le (p-1) (2*h)
    change (2*h)*t ≤ p-1 at le
    nlinarith
  have total : allBad.card < (univ : Finset (ZMod p)).card := by
    rw [Finset.card_univ,ZMod.card]; omega
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card total
  have nz : a≠0 := by
    intro z
    exact ha (by simp [allBad,z])
  refine ⟨a,nz,?_⟩
  intro d hD v hv
  by_contra! small
  have small' : v.natAbs ≤ t := by
    apply (Nat.le_div_iff_mul_le (by omega : 0<2*h)).mpr
    rw [Nat.mul_comm]
    omega
  have nonzero : v≠0 := by
    intro h
    rw [h,Int.cast_zero] at hv
    exact (mul_ne_zero nz (hd d hD)) hv.symm
  have absPos : 0<v.natAbs := Int.natAbs_pos.mpr nonzero
  have inPlus : ((v.natAbs : ℕ) : ZMod p) ∈ plus := by
    apply Finset.mem_image.mpr
    refine ⟨v.natAbs-1,Finset.mem_range.mpr (by omega),?_⟩
    rw [Nat.sub_add_cancel (by omega : 1≤v.natAbs)]
  have inBad : (v : ZMod p)∈bad := by
    cases v with
    | ofNat x =>
      apply Finset.mem_union_left
      simpa using inPlus
    | negSucc x =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      exact ⟨_,inPlus,by simp⟩
  apply ha
  apply Finset.mem_insert_of_mem
  apply Finset.mem_biUnion.mpr
  refine ⟨d,hD,Finset.mem_image.mpr ⟨_,inBad,?_⟩⟩
  exact (div_eq_iff (hd d hD)).mpr hv

#print axioms some_shift
#print axioms multiplier
end Erdos142Counting

namespace Erdos142Finite
open Finset

/-- A finite transfer with a general seed and no bound on the magnitudes
of the prescribed positive steps. The inequality is integral. -/
theorem transfer (N n k : ℕ) (S D : Finset ℕ) (hk : 3≤k) (hn : 2≤n)
    (inside : ∀ s∈S, s<n) (pos : ∀ d∈D, 0<d)
    (few : D.card < (2*n-1)*(k-1))
    (seed : ∀ a t : ℤ, (∀ i : ℕ, i<k → ∃ s∈S, (s:ℤ)=a+(i:ℤ)*t) → t=0) :
    ∃ T ⊆ range N, N*S.card ≤ (2*(2*n-1))*T.card ∧
      ∀ x d : ℕ, d∈D → ¬(∀ i : ℕ, i<k → x+i*d∈T) := by
  classical
  let q := 2*n-1
  obtain ⟨p,large,prime⟩ := Nat.exists_infinite_primes (D.sup id+2)
  let _ : Fact p.Prime := ⟨prime⟩
  have hp := prime.two_le
  have dq (d) (hd : d∈D) : d<p := by
    have h : d ≤ D.sup id := Finset.le_sup (f:=id) hd
    omega
  obtain ⟨a,_,gap⟩ := Erdos142Counting.multiplier p (q*(k-1)) D hp few (by
    intro d hd hz
    exact Nat.not_dvd_of_pos_of_lt (pos d hd) (dq d hd) ((ZMod.natCast_eq_zero_iff d p).mp hz))
  let M := 2*q*p
  have hq : q≥n := by dsimp [q]; omega
  have hM : 0<M := by
    have hq0 : 0<q := by omega
    have hp0 : 0<p := by omega
    dsimp [M]; positivity
  let _ : NeZero M := ⟨hM.ne'⟩
  let code (z : ℕ×ℕ) := 2*p*z.1+z.2
  let grid (z : ℕ×ℕ) : ZMod M := (code z : ℕ)
  let cells := S ×ˢ range p
  let U := cells.image grid
  have codeLt (z) (hz : z∈cells) : code z<M := by
    obtain ⟨hs,he⟩ := Finset.mem_product.mp hz
    have ls := inside z.1 hs
    have le := Finset.mem_range.mp he
    have hmul := Nat.mul_le_mul_left (2*p) (show z.1+1≤q by omega)
    dsimp [code,M]
    nlinarith
  have codeDiv (z) (hz : z∈cells) : code z/(2*p)=z.1 := by
    have he := Finset.mem_range.mp (Finset.mem_product.mp hz).2
    dsimp [code]
    rw [Nat.mul_add_div (by omega : 0<2*p),Nat.div_eq_of_lt (by omega)]
    omega
  have injective : Set.InjOn grid ↑cells := by
    intro z hz y hy eq
    have vals := congrArg ZMod.val eq
    change ((code z : ZMod M).val) = ((code y : ZMod M).val) at vals
    rw [ZMod.val_natCast_of_lt (codeLt _ hz),ZMod.val_natCast_of_lt (codeLt _ hy)] at vals
    have one : z.1=y.1 := by rw [← codeDiv z hz, ← codeDiv y hy,vals]
    have two : z.2=y.2 := by dsimp [code] at vals; rw [one] at vals; omega
    exact Prod.ext one two
  have cardU : U.card=S.card*p := by
    rw [show U=cells.image grid by rfl,Finset.card_image_of_injOn injective,Finset.card_product,Finset.card_range]
  let f (x : ℕ) : ZMod M := ((2*q*a.val*x : ℕ) : ZMod M)
  obtain ⟨b,avg⟩ := Erdos142Counting.some_shift (range N) f U
  let T := (range N).filter fun x => f x+b∈U
  change (range N).card*U.card≤Fintype.card (ZMod M)*T.card at avg
  rw [Finset.card_range,cardU,ZMod.card] at avg
  refine ⟨T,Finset.filter_subset _ _,?_,?_⟩
  · change N*S.card ≤ (2*q)*T.card
    have scaled : (N*S.card)*p ≤ ((2*q)*T.card)*p := by
      dsimp [M] at avg
      nlinarith only [avg]
    exact Nat.le_of_mul_le_mul_right scaled (by omega)
  intro x d hD hap
  have membership (i : ℕ) (hi : i<k) : ∃ z∈cells, grid z=f (x+i*d)+b :=
    Finset.mem_image.mp (Finset.mem_filter.mp (hap i hi)).2
  choose pair pairIn pairEq using membership
  let z (i : ℕ) := if hi : i<k then pair i hi else (0,0)
  have zIn (i) (hi : i<k) : z i∈cells := by simpa [z,hi] using pairIn i hi
  have zEq (i) (hi : i<k) : grid (z i)=f (x+i*d)+b := by simpa [z,hi] using pairEq i hi
  let c : ℤ := 2*(q:ℤ)*a.val*x+b.val
  let w : ℤ := 2*(q:ℤ)*a.val*d
  have wraps (i : ℕ) (hi : i<k) : ∃ v : ℤ,
      2*(p:ℤ)*(z i).1+(z i).2=c+(i:ℤ)*w+2*(p:ℤ)*q*v := by
    have eq := zEq i hi
    have dvd : (M:ℤ) ∣ (2*(p:ℤ)*(z i).1+(z i).2)-(c+(i:ℤ)*w) := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
      dsimp [c,w]; push_cast
      dsimp [grid,code,f] at eq
      push_cast at eq
      rw [ZMod.natCast_zmod_val]
      linear_combination eq
    obtain ⟨v,hv⟩ := dvd
    refine ⟨v,?_⟩
    dsimp [M] at hv
    linear_combination hv
  choose wrap wrapEq using wraps
  apply Erdos142Pullback.pullback_impossible k p n q c w hk (by exact_mod_cast (show 0<p by omega)) (by exact_mod_cast hn)
    (by dsimp [q]; rw [Nat.cast_sub (by omega : 1≤2*n)]; push_cast; ring)
    {r | ∃ s∈S, (s:ℤ)=r} (fun i => (z i).1) (fun i => (z i).2)
    (fun i => if hi : i<k then wrap i hi else 0)
  · rintro r ⟨s,hs,rfl⟩
    exact ⟨by positivity,by exact_mod_cast inside s hs⟩
  · exact seed
  · intro i hi
    exact ⟨_,(Finset.mem_product.mp (zIn i hi)).1,rfl⟩
  · intro i hi
    exact ⟨by positivity,by exact_mod_cast Finset.mem_range.mp (Finset.mem_product.mp (zIn i hi)).2⟩
  · intro i hi
    simpa [hi] using wrapEq i hi
  · intro u
    let v : ℤ := (a.val:ℤ)*d+(p:ℤ)*u
    have residue : (v : ZMod p)=a*d := by simp [v]
    have magnitude := gap d hD v residue
    have mag : (p:ℤ) ≤ 2*((q:ℤ)*((k:ℤ)-1))*|v| := by
      have zmag := (Nat.cast_le (α:=ℤ)).mpr magnitude
      simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub (show 1≤k by omega),
        Nat.cast_one,Int.natCast_natAbs] using zmag
    have eq : w+2*(p:ℤ)*q*u = (2*(q:ℤ))*v := by dsimp [w,v]; ring
    rw [eq,abs_mul,abs_of_nonneg (by positivity : 0≤2*(q:ℤ))]
    linarith only [mag]

/-- The specialization takes the size of its seed directly from mathlib's
extremal Roth number on the ordinary integer interval. -/
theorem transfer_roth (N n : ℕ) (D : Finset ℕ) (hn : 2≤n)
    (pos : ∀ d∈D, 0<d) (few : D.card < (2*n-1)*2) :
    ∃ T ⊆ range N, N*rothNumberNat n ≤ (2*(2*n-1))*T.card ∧
      ∀ x d : ℕ, d∈D → ¬(∀ i : ℕ, i<3 → x+i*d∈T) := by
  obtain ⟨S,hs,count,free⟩ := rothNumberNat_spec n
  rw [← count]
  apply transfer N n 3 S D (by decide) hn (fun s h => Finset.mem_range.mp (hs h)) pos few
  intro a t members
  obtain ⟨x,hx,ex⟩ := members 0 (by decide)
  obtain ⟨y,hy,ey⟩ := members 1 (by decide)
  obtain ⟨z,hz,ez⟩ := members 2 (by decide)
  norm_num at ex ey ez
  have hxz : x+z=y+y := by omega
  have xy := free hx hy hz hxz
  omega

#print axioms transfer
#print axioms transfer_roth
end Erdos142Finite
