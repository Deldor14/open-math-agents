import Distribution
import Mathlib.Data.Nat.Factorization.Basic

namespace ProgressionParity
open Set.IsAPOfLengthFree

theorem disjoint_blocks_upper {k:ℕ} (hk : 1<k) (N:ℕ) :
    maxCard k N ≤ N-N/k := by
  let q := N/k
  let r := N%k
  have kp : 0<k := by omega
  have rem : r<k := Nat.mod_lt _ kp
  have id : N=q*k+r := by simpa only [q,r,Nat.mul_comm,Nat.add_comm] using (Nat.mod_add_div N k).symm
  have x := interval_subadditive hk (q*k) r
  rw [← id,(initial_values hk).1 r rem] at x
  have y := multiple_upper hk q k
  rw [(initial_values hk).2] at y
  have kd : k-1+1=k := by omega
  have prod : q*(k-1)+q=q*k := by rw [← Nat.mul_succ];exact congrArg (q*·) kd
  change maxCard k N ≤ N-q
  omega

theorem before_first_gap {k N:ℕ} (hk : 1<k) (hN : N≤k.minFac*(k-1)) :
    maxCard k N=N-N/k := by
  have kp : 0<k := by omega
  let I := Finset.Ioc 0 N
  let A := I.filter (fun z => ¬ k ∣ z)
  have sub : A ⊆ Finset.Icc 1 N := by
    intro z hz
    obtain ⟨lo,hi⟩ := Finset.mem_Ioc.mp (Finset.mem_filter.mp hz).1
    exact Finset.mem_Icc.mpr ⟨lo,hi⟩
  have free : Free (· ∈ A) k := by
    intro a d hd run
    have H := (run_iff_forall _ _ _ _).mp run
    have start : a∈A := by simpa using H 0 (by omega)
    have hi := (Finset.mem_Icc.mp (sub (H (k-1) (by omega)))).2
    have lo := (Finset.mem_Icc.mp (sub start)).1
    have ds : d<k.minFac := by
      by_contra! h
      have le := Nat.mul_le_mul_left (k-1) h
      rw [Nat.mul_comm k.minFac (k-1)] at hN
      omega
    have co := Nat.coprime_of_lt_minFac hd.ne' ds
    obtain ⟨i,ik,zero⟩ := hits_residue kp co a 0 kp
    exact (Finset.mem_filter.mp (H i ik)).2 (Nat.dvd_of_mod_eq_zero zero)
  have count := @Finset.card_filter_add_card_filter_not ℕ I (fun z => k ∣ z) _ _
  have divs : (I.filter (fun z => k ∣ z)).card=N/k := Nat.Ioc_filter_dvd_card_eq_div N k
  have ic : I.card=N := by simp [I]
  have bnd := bound_witness hk A sub free
  change (I.filter (fun z => ¬k∣z)).card≤maxCard k N at bnd
  have upper := disjoint_blocks_upper hk N
  omega

private lemma complement_quotient {p h i:ℕ} (hp : 0<p) (hh : 0<h) (hi : i<p*h) :
    i/h+(p*h-1-i)/h=p-1 := by
  let a := i
  let b := p*h-1-i
  have sum : a+b+1=p*h := by dsimp [a,b];omega
  have ra := Nat.mod_lt a hh
  have rb := Nat.mod_lt b hh
  have da := Nat.mod_add_div a h
  have db := Nat.mod_add_div b h
  set q := a/h+b/h
  have prod : h*q=h*(a/h)+h*(b/h) := Nat.mul_add _ _ _
  have strict : q<p := by
    by_contra! z
    have cmp := Nat.mul_le_mul_left h z
    rw [Nat.mul_comm h p] at cmp
    omega
  have top : p≤q+1 := by
    by_contra! z
    have cmp := Nat.mul_le_mul_left h (show q+2≤p by omega)
    rw [Nat.mul_comm h p,Nat.mul_add,Nat.mul_two] at cmp
    omega
  change q=p-1
  omega

private lemma missing_split {k N x:ℕ} (hk:1<k) (hx : 0<x) (xN : x≤N) (A:Finset ℕ)
    (ha : A ⊆ Finset.Icc 1 N) (fa : Free (· ∈ A) k) (missing : x∉A) :
    A.card ≤ maxCard k (x-1)+maxCard k (N-x) := by
  have left := (portion_bounds hk A ha fa (show x-1≤N by omega)).1
  have right := (portion_bounds hk A ha fa xN).2
  have id : A.filter (·≤x)=A.filter (·≤x-1) := by
    ext z
    simp only [Finset.mem_filter]
    constructor <;> grind
  rw [id] at right
  omega

private lemma first_obstruction {k p h:ℕ} (hk : 1<k) (hp : 1<p) (hh : 0<h) (eq : k=p*h) :
    maxCard k (p*(k-1)+1) ≤ p*(k-1)+1-p := by
  let N := p*(k-1)+1
  obtain ⟨A,ha,fa,ca⟩ := attained hk N
  change maxCard k N ≤ N-p
  by_contra! greater
  apply fa 1 p (by omega)
  apply (run_iff_forall _ _ _ _).mpr
  intro i hi
  let x := 1+i*p
  change x ∈ A
  by_contra miss
  have bound := Nat.mul_le_mul_right p (show i≤k-1 by omega)
  have xn : x≤N := by dsimp only [x,N];rw [Nat.mul_comm p (k-1)];omega
  have xp : 0<x := by dsimp [x];omega
  have first := missing_split hk xp xn A ha fa miss
  have before := disjoint_blocks_upper hk (x-1)
  have after := disjoint_blocks_upper hk (N-x)
  have dl := Nat.div_le_self (x-1) k
  have dr := Nat.div_le_self (N-x) k
  have cancel (z:ℕ) : (z*p)/k=z/h := by
    rw [eq,Nat.mul_comm p h,Nat.mul_div_mul_right _ _ (by omega : 0<p)]
  have f : x-1=i*p := by dsimp [x];omega
  have b : N-x=(k-1-i)*p := by
    dsimp only [N,x]
    rw [Nat.sub_mul,Nat.mul_comm p (k-1)]
    omega
  have total : (x-1)/k+(N-x)/k=p-1 := by
    rw [f,b,cancel,cancel,eq]
    exact complement_quotient (by omega) hh (eq ▸ hi)
  omega

theorem first_gap_value {k:ℕ} (hk:1<k) :
    let p := k.minFac
    maxCard k (p*(k-1)+1)=p*(k-1)+1-p := by
  let p := k.minFac
  have hp : 1<p := (Nat.minFac_prime (by omega : k≠1)).one_lt
  obtain ⟨h,hdiv⟩ := Nat.minFac_dvd k
  change k=p*h at hdiv
  have hh : 0<h := by
    by_contra! z
    have zero : h=0 := by omega
    rw [zero,Nat.mul_zero] at hdiv
    omega
  have pk : p≤k := Nat.le_of_dvd (by omega) (Nat.minFac_dvd k)
  have top := first_obstruction hk hp hh hdiv
  have low := interval_mono hk (show p*(k-1)≤p*(k-1)+1 by omega)
  rw [before_first_gap hk (show p*(k-1)≤k.minFac*(k-1) from le_rfl)] at low
  have full₁ : (p-1)*k+k=p*k := by
    rw [← Nat.succ_mul];exact congrArg (·*k) (show (p-1).succ=p by omega)
  have full₂ : p*(k-1)+p=p*k := by
    rw [← Nat.mul_succ];exact congrArg (p*·) (show (k-1).succ=k by omega)
  have division : p*(k-1)/k=p-1 := Nat.div_eq_of_lt_le (by omega)
    (by rw [Nat.succ_mul];omega)
  rw [division] at low
  change maxCard k (p*(k-1)+1)=p*(k-1)+1-p
  omega

#print axioms before_first_gap
#print axioms first_gap_value
end ProgressionParity
