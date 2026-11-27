import OMAStatements.S_oeis_a303647
import Mathlib

open OMA.S_oeis_a303647 PowerSeries
namespace Deldor14.CubicRounding

private noncomputable abbrev root : ℝ := (2:ℝ)^((1:ℝ)/3)
private theorem cube : root^3=2 := by
  rw [root,← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private theorem rootBounds : (125992:ℝ)/100000 < root ∧ root < 125993/100000 := by
  constructor
  · by_contra! h
    have z := pow_le_pow_left₀ (by positivity : 0 ≤ root) h 3
    rw [cube] at z; norm_num at z
  · by_contra! h
    have z := pow_le_pow_left₀ (by norm_num : 0 ≤ (125993:ℝ)/100000) h 3
    rw [cube] at z; norm_num at z

private theorem bounds : (3847:ℝ)/1000 < ratio ∧ ratio < 3848/1000 := by
  change _ < 1/(root-1) ∧ 1/(root-1) < _
  have rootPos : 0 < root-1 := by linarith [rootBounds.1]
  rw [lt_div_iff₀ rootPos,div_lt_iff₀ rootPos]
  constructor <;> linarith [rootBounds.1,rootBounds.2]

private noncomputable abbrev s := ratio-3
private noncomputable abbrev u := 1/ratio
private theorem quad : s*ratio=3+u := by
  have pos : root-1≠0 := by linarith [rootBounds.1]
  change (1/(root-1)-3)*(1/(root-1))=3+1/(1/(root-1))
  field_simp [pos]
  nlinarith [cube]

private theorem coefBounds : (45:ℝ)/100 < s^2-u ∧ s^2-u < 47/100 ∧
    (21:ℝ)/100 < s*u ∧ s*u < 23/100 ∧ (15:ℝ)/100 < 1-s ∧ 1-s < 16/100 := by
  have hu : (25:ℝ)/100 < u ∧ u < 26/100 := by
    have hp : 0 < ratio := by linarith [bounds.1]
    change _ < 1/ratio ∧ 1/ratio < _
    rw [lt_div_iff₀ hp,div_lt_iff₀ hp]
    constructor <;> linarith [bounds.1,bounds.2]
  have hs : (847:ℝ)/1000 < s ∧ s < 848/1000 := by dsimp [s]; constructor <;> linarith [bounds.1,bounds.2]
  have s2 := mul_self_lt_mul_self (by norm_num : 0 ≤ (847:ℝ)/1000) hs.1
  have s3 := mul_self_lt_mul_self (by linarith [hs.1] : 0 ≤ s) hs.2
  have su0 := mul_lt_mul_of_pos_left hu.1 (by linarith [hs.1] : 0 < s)
  have su1 := mul_lt_mul_of_pos_left hu.2 (by linarith [hs.1] : 0 < s)
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [hs.1,hs.2,hu.1,hu.2]

private def seq (b c : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => b
  | n+3 => 3*seq b c (n+2)+3*seq b c (n+1)+seq b c n+c
private noncomputable def err (b c : ℤ) (n : ℕ) : ℝ := seq b c (n+1)-ratio*(seq b c n:ℝ)

private theorem second (b c : ℤ) (n : ℕ) :
    err b c (n+2) = -s*err b c (n+1)-u*err b c n+c := by
  have id : u*ratio=1 := by
    have nz : ratio≠0 := by linarith [bounds.1]
    simp [u,nz]
  have rel : ((seq b c (n+3):ℤ):ℝ)=3*(seq b c (n+2):ℝ)+3*(seq b c (n+1):ℝ)+(seq b c n:ℝ)+c := by
    rw [seq]; push_cast; ring
  unfold err
  rw [rel]
  have sr : s=ratio-3 := rfl
  linear_combination -((seq b c (n+1):ℝ))*quad - (seq b c n:ℝ)*id+(seq b c (n+2):ℝ)*sr

private theorem third (b c : ℤ) (n : ℕ) :
    err b c (n+3)=(s^2-u)*err b c (n+1)+(s*u)*err b c n+(1-s)*c := by
  rw [second b c (n+1),second b c n]; ring

private theorem trap (n : ℕ) : 1 < err 5 3 (n+1) ∧ err 5 3 (n+1) < 2 ∧
    -1 < err 3 (-1) (n+1) ∧ err 3 (-1) (n+1) < 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 3
    · interval_cases n <;> norm_num [err,seq] <;>
        (repeat' constructor) <;> linarith [bounds.1,bounds.2]
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
      obtain ⟨a,b,c,d⟩ := ih k (by omega)
      obtain ⟨A,B,C,D⟩ := ih (k+1) (by omega)
      obtain ⟨lo,hi,lo',hi',e,f⟩ := coefBounds
      have pos : 0 < s^2-u := by linarith
      have pos' : 0 < s*u := by linarith
      rw [third 5 3 (k+1),third 3 (-1) (k+1)]
      push_cast
      have i1 := mul_lt_mul_of_pos_left A pos
      have i2 := mul_lt_mul_of_pos_left a pos'
      have i3 := mul_lt_mul_of_pos_left B pos
      have i4 := mul_lt_mul_of_pos_left b pos'
      have i5 := mul_lt_mul_of_pos_left C pos
      have i6 := mul_lt_mul_of_pos_left c pos'
      have i7 := mul_lt_mul_of_pos_left D pos
      have i8 := mul_lt_mul_of_pos_left d pos'
      refine ⟨?_,?_,?_,?_⟩ <;> linarith

private theorem identify (n : ℕ) : a n=seq 5 3 n ∧ a301483 n=seq 3 (-1) n := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    cases n with
    | zero => exact ⟨rfl,rfl⟩
    | succ n =>
      obtain ⟨lo,hi,lo',hi'⟩ := trap n
      unfold err at lo hi lo' hi'
      constructor
      · rw [a,ih.1,Int.ceil_eq_iff]; push_cast; constructor <;> linarith
      · rw [a301483,ih.2,Int.floor_eq_iff]; push_cast; constructor <;> linarith

private theorem four (b c : ℤ) (n : ℕ) : seq b c (n+4)=4*seq b c (n+3)-2*seq b c (n+1)-seq b c n := by
  have aa : seq b c (n+4)=3*seq b c (n+3)+3*seq b c (n+2)+seq b c (n+1)+c := rfl
  have bb : seq b c (n+3)=3*seq b c (n+2)+3*seq b c (n+1)+seq b c n+c := rfl
  omega

private theorem companion (n : ℕ) :
    seq 5 3 (n+3)=seq 3 (-1) (n+5)-a195350 (n+5)+a195339 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 4
    · interval_cases n <;> decide
    · obtain ⟨k,rfl⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
      have t1 := ih k (by omega)
      have t2 := ih (k+1) (by omega)
      have t3 := ih (k+3) (by omega)
      have u1 := four 5 3 (k+3)
      have u2 := four 3 (-1) (k+5)
      have u3 : a195350 (k+9)=4*a195350 (k+8)-2*a195350 (k+6)-a195350 (k+5) := rfl
      have u4 : a195339 (k+4)=4*a195339 (k+3)-2*a195339 (k+1)-a195339 k := rfl
      linarith only [t1,t2,t3,u1,u2,u3,u4]


private theorem recA (n : ℕ) (hn : 4 ≤ n) : a n=4*a (n-1)-2*a (n-3)-a (n-4) := by
  obtain ⟨k,rfl⟩ : ∃ k,n=k+4 := ⟨n-4,by omega⟩
  simp only [fun t => (identify t).1,show k+4-1=k+3 by omega,show k+4-3=k+1 by omega,
    show k+4-4=k by omega]
  exact four 5 3 k

private theorem series : (1-X)*(1-3*X-3*X^2-X^3)*mk a=X*(1+X+X^2) := by
  have left : (1-X)*(1-3*X-3*X^2-X^3)*mk a =
      mk a-(C 4*mk a)*X+(C 2*mk a)*X^3+mk a*X^4 := by simp only [map_ofNat]; ring
  have right : (X*(1+X+X^2):PowerSeries ℤ)=X+X^2+X^3 := by ring
  rw [left,right]
  apply PowerSeries.ext
  intro n
  have shift (f : PowerSeries ℤ) : coeff n (f*X)=if 1 ≤ n then coeff (n-1) f else 0 := by
    simpa only [pow_one] using coeff_mul_X_pow' f 1 n
  simp only [map_add,map_sub,shift,coeff_mul_X_pow',coeff_C_mul,coeff_mk,coeff_X,coeff_X_pow]
  by_cases small : n < 4
  · interval_cases n <;> norm_num [fun t => (identify t).1,seq]
  · simp only [if_pos (by omega : 1 ≤ n),if_pos (by omega : 3 ≤ n),if_pos (by omega : 4 ≤ n),
      if_neg (by omega : n≠1),if_neg (by omega : n≠2),if_neg (by omega : n≠3)]
    linarith [recA n (by omega)]

theorem result : type_of% @OMA.S_oeis_a303647.main := by
  refine ⟨?_,series,fun n h => recA n (by omega)⟩
  intro n hn
  obtain ⟨k,rfl⟩ : ∃ k,n=k+3 := ⟨n-3,by omega⟩
  rw [(identify _).1,(identify _).2]
  simpa only [show k+3-3=k by omega] using companion k

end Deldor14.CubicRounding
theorem OMA.solution : type_of% @OMA.S_oeis_a303647.main := Deldor14.CubicRounding.result
