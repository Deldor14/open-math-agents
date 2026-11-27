import OMAStatements.S_oeis_a334765
import Mathlib

open OMA.S_oeis_a334765

namespace Deldor14.OppositeDigits

def binary (n : ℕ) := (Nat.digits 2 n).sum

theorem binary_rec (n : ℕ) : binary n = n%2 + binary (n/2) := by
  by_cases h : n=0
  · subst n; decide
  · change (Nat.digits 2 n).sum = _
    rw [Nat.digits_eq_cons_digits_div (by decide : 1<2) h, List.sum_cons]
    rfl

theorem ternary_rec (n : ℕ) : balancedSum n = (n:ℤ)-3*(((n+1)/3:ℕ):ℤ)+balancedSum ((n+1)/3) := by
  by_cases h : n=0
  · subst n; norm_num
  · rw [balancedSum.eq_def n, if_neg h]

theorem ternary_parity (n : ℕ) : balancedSum n % 2 = (n:ℤ)%2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases zero : n=0
    · subst n; rw [balancedSum.eq_def]; decide
    · have small : (n+1)/3<n := by omega
      have par := ih _ small
      rw [ternary_rec n]
      omega

theorem pair_not_one_mod_four {n : ℕ} (h : n%4=1)
    (left : digitMatch n=true) (right : digitMatch (n+1)=true) : False := by
  change decide ((binary n:ℤ) = -balancedSum n)=true at left
  change decide ((binary (n+1):ℤ) = -balancedSum (n+1))=true at right
  have l := of_decide_eq_true left
  have r := of_decide_eq_true right
  have step : binary n=binary (n+1) := by
    rw [binary_rec n,binary_rec (n+1)]
    rw [binary_rec (n/2),binary_rec ((n+1)/2)]
    rw [show n/2/2=(n+1)/2/2 by omega]
    omega
  have p := ternary_parity n
  have q := ternary_parity (n+1)
  push_cast at q
  omega

theorem pair_even_mod_three {n : ℕ} (even : n%2=0)
    (left : digitMatch n=true) (right : digitMatch (n+1)=true) : n%3=1 := by
  change decide ((binary n:ℤ) = -balancedSum n)=true at left
  change decide ((binary (n+1):ℤ) = -balancedSum (n+1))=true at right
  have l := of_decide_eq_true left
  have r := of_decide_eq_true right
  have step : binary (n+1)=binary n+1 := by
    rw [binary_rec (n+1),binary_rec n,show (n+1)/2=n/2 by omega]; omega
  by_contra bad
  have same : (n+1+1)/3=(n+1)/3 := by omega
  have inc := ternary_rec (n+1)
  rw [same] at inc
  have base := ternary_rec n
  push_cast at inc
  omega

theorem no_four (n : ℕ) : ¬(∀ i : Fin 4, digitMatch (n+i.val)=true) := by
  intro h
  have z : digitMatch n=true := h 0
  have a : digitMatch (n+1)=true := h 1
  have b : digitMatch (n+2)=true := h 2
  have c : digitMatch (n+3)=true := h 3
  by_cases even : n%2=0
  · have x := pair_even_mod_three even z a
    have y := pair_even_mod_three (n:=n+2) (by omega) b c
    omega
  · rcases (show n%4=1 ∨ (n+2)%4=1 by omega) with hn | hn
    · exact pair_not_one_mod_four hn z a
    · exact pair_not_one_mod_four hn b c

def fast : ℕ → ℕ → ℕ × ℤ
  | 0, _ => (0,0)
  | d+1, n => (n%2+(fast d (n/2)).1, (n:ℤ)-3*(((n+1)/3:ℕ):ℤ)+(fast d ((n+1)/3)).2)

theorem fast_ok (d n : ℕ) (size : n<2^d) :
    (fast d n).1=binary n ∧ (fast d n).2=balancedSum n := by
  induction d generalizing n with
  | zero =>
    have h : n=0 := by simpa using size
    subst n; constructor
    · decide
    · rw [balancedSum.eq_def]; rfl
  | succ d ih =>
    rw [pow_succ] at size
    obtain ⟨l,_⟩ := ih (n/2) (by omega)
    obtain ⟨_,r⟩ := ih ((n+1)/3) (by omega)
    simp only [fast,l,r]
    exact ⟨(binary_rec n).symm,(ternary_rec n).symm⟩

end Deldor14.OppositeDigits



/- Finite certificates. -/
namespace Deldor14.OppositeDigits

def good (n : ℕ) : Bool := decide (((fast 16 n).1:ℤ) = -(fast 16 n).2)

theorem good_eq {n : ℕ} (hn : n<65536) : good n=digitMatch n := by
  obtain ⟨l,r⟩ := fast_ok 16 n hn
  simp only [good,digitMatch,l,r,binary]

def hitsIn (start size : ℕ) := (List.range' start size).filter good

theorem matches_add (start a b : ℕ) :
    hitsIn start (a+b) = hitsIn start a ++ hitsIn (start+a) b := by
  unfold hitsIn
  rw [← List.range'_append_1,List.filter_append]

set_option maxRecDepth 16000 in
private theorem block_0_256 : hitsIn 0 256 = [0,41,68,131,132] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_256_512 : hitsIn 256 256 = [368,384] := by decide +kernel

private theorem block_0_512 : hitsIn 0 512 = [0,41,68,131,132,368,384] := by
  rw [show 512=256+256 by decide,matches_add,block_0_256]
  change _ ++ hitsIn 256 256 = _
  rw [block_256_512] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_512_768 : hitsIn 512 256 = [528] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_768_1024 : hitsIn 768 256 = [] := by decide +kernel

private theorem block_512_1024 : hitsIn 512 512 = [528] := by
  rw [show 512=256+256 by decide,matches_add,block_512_768]
  change _ ++ hitsIn 768 256 = _
  rw [block_768_1024] <;> rfl

private theorem block_0_1024 : hitsIn 0 1024 = [0,41,68,131,132,368,384,528] := by
  rw [show 1024=512+512 by decide,matches_add,block_0_512]
  change _ ++ hitsIn 512 512 = _
  rw [block_512_1024] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_1024_1280 : hitsIn 1024 256 = [1095,1098,1100,1106,1112,1122,1124,1152,1176] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_1280_1536 : hitsIn 1280 256 = [1346] := by decide +kernel

private theorem block_1024_1536 : hitsIn 1024 512 = [1095,1098,1100,1106,1112,1122,1124,1152,1176,1346] := by
  rw [show 512=256+256 by decide,matches_add,block_1024_1280]
  change _ ++ hitsIn 1280 256 = _
  rw [block_1280_1536] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_1536_1792 : hitsIn 1536 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_1792_2048 : hitsIn 1792 256 = [1824] := by decide +kernel

private theorem block_1536_2048 : hitsIn 1536 512 = [1824] := by
  rw [show 512=256+256 by decide,matches_add,block_1536_1792]
  change _ ++ hitsIn 1792 256 = _
  rw [block_1792_2048] <;> rfl

private theorem block_1024_2048 : hitsIn 1024 1024 = [1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824] := by
  rw [show 1024=512+512 by decide,matches_add,block_1024_1536]
  change _ ++ hitsIn 1536 512 = _
  rw [block_1536_2048] <;> rfl

private theorem block_0_2048 : hitsIn 0 2048 = [0,41,68,131,132,368,384,528,1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_0_1024]
  change _ ++ hitsIn 1024 1024 = _
  rw [block_1024_2048] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_2048_2304 : hitsIn 2048 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_2304_2560 : hitsIn 2304 256 = [] := by decide +kernel

private theorem block_2048_2560 : hitsIn 2048 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_2048_2304]
  change _ ++ hitsIn 2304 256 = _
  rw [block_2304_2560] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_2560_2816 : hitsIn 2560 256 = [2561] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_2816_3072 : hitsIn 2816 256 = [] := by decide +kernel

private theorem block_2560_3072 : hitsIn 2560 512 = [2561] := by
  rw [show 512=256+256 by decide,matches_add,block_2560_2816]
  change _ ++ hitsIn 2816 256 = _
  rw [block_2816_3072] <;> rfl

private theorem block_2048_3072 : hitsIn 2048 1024 = [2561] := by
  rw [show 1024=512+512 by decide,matches_add,block_2048_2560]
  change _ ++ hitsIn 2560 512 = _
  rw [block_2560_3072] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_3072_3328 : hitsIn 3072 256 = [3282,3284] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_3328_3584 : hitsIn 3328 256 = [3336,3344,3392,3524] := by decide +kernel

private theorem block_3072_3584 : hitsIn 3072 512 = [3282,3284,3336,3344,3392,3524] := by
  rw [show 512=256+256 by decide,matches_add,block_3072_3328]
  change _ ++ hitsIn 3328 256 = _
  rw [block_3328_3584] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_3584_3840 : hitsIn 3584 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_3840_4096 : hitsIn 3840 256 = [] := by decide +kernel

private theorem block_3584_4096 : hitsIn 3584 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_3584_3840]
  change _ ++ hitsIn 3840 256 = _
  rw [block_3840_4096] <;> rfl

private theorem block_3072_4096 : hitsIn 3072 1024 = [3282,3284,3336,3344,3392,3524] := by
  rw [show 1024=512+512 by decide,matches_add,block_3072_3584]
  change _ ++ hitsIn 3584 512 = _
  rw [block_3584_4096] <;> rfl

private theorem block_2048_4096 : hitsIn 2048 2048 = [2561,3282,3284,3336,3344,3392,3524] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_2048_3072]
  change _ ++ hitsIn 3072 1024 = _
  rw [block_3072_4096] <;> rfl

private theorem block_0_4096 : hitsIn 0 4096 = [0,41,68,131,132,368,384,528,1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824,2561,3282,3284,3336,3344,3392,3524] := by
  rw [show 4096=2048+2048 by decide,matches_add,block_0_2048]
  change _ ++ hitsIn 2048 2048 = _
  rw [block_2048_4096] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_4096_4352 : hitsIn 4096 256 = [4098,4101,4104,4112,4118,4128,4172] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_4352_4608 : hitsIn 4352 256 = [4352,4496] := by decide +kernel

private theorem block_4096_4608 : hitsIn 4096 512 = [4098,4101,4104,4112,4118,4128,4172,4352,4496] := by
  rw [show 512=256+256 by decide,matches_add,block_4096_4352]
  change _ ++ hitsIn 4352 256 = _
  rw [block_4352_4608] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_4608_4864 : hitsIn 4608 256 = [4739,4740] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_4864_5120 : hitsIn 4864 256 = [] := by decide +kernel

private theorem block_4608_5120 : hitsIn 4608 512 = [4739,4740] := by
  rw [show 512=256+256 by decide,matches_add,block_4608_4864]
  change _ ++ hitsIn 4864 256 = _
  rw [block_4864_5120] <;> rfl

private theorem block_4096_5120 : hitsIn 4096 1024 = [4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740] := by
  rw [show 1024=512+512 by decide,matches_add,block_4096_4608]
  change _ ++ hitsIn 4608 512 = _
  rw [block_4608_5120] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_5120_5376 : hitsIn 5120 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_5376_5632 : hitsIn 5376 256 = [5504] := by decide +kernel

private theorem block_5120_5632 : hitsIn 5120 512 = [5504] := by
  rw [show 512=256+256 by decide,matches_add,block_5120_5376]
  change _ ++ hitsIn 5376 256 = _
  rw [block_5376_5632] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_5632_5888 : hitsIn 5632 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_5888_6144 : hitsIn 5888 256 = [] := by decide +kernel

private theorem block_5632_6144 : hitsIn 5632 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_5632_5888]
  change _ ++ hitsIn 5888 256 = _
  rw [block_5888_6144] <;> rfl

private theorem block_5120_6144 : hitsIn 5120 1024 = [5504] := by
  rw [show 1024=512+512 by decide,matches_add,block_5120_5632]
  change _ ++ hitsIn 5632 512 = _
  rw [block_5632_6144] <;> rfl

private theorem block_4096_6144 : hitsIn 4096 2048 = [4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740,5504] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_4096_5120]
  change _ ++ hitsIn 5120 1024 = _
  rw [block_5120_6144] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_6144_6400 : hitsIn 6144 256 = [6224] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_6400_6656 : hitsIn 6400 256 = [] := by decide +kernel

private theorem block_6144_6656 : hitsIn 6144 512 = [6224] := by
  rw [show 512=256+256 by decide,matches_add,block_6144_6400]
  change _ ++ hitsIn 6400 256 = _
  rw [block_6400_6656] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_6656_6912 : hitsIn 6656 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_6912_7168 : hitsIn 6912 256 = [] := by decide +kernel

private theorem block_6656_7168 : hitsIn 6656 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_6656_6912]
  change _ ++ hitsIn 6912 256 = _
  rw [block_6912_7168] <;> rfl

private theorem block_6144_7168 : hitsIn 6144 1024 = [6224] := by
  rw [show 1024=512+512 by decide,matches_add,block_6144_6656]
  change _ ++ hitsIn 6656 512 = _
  rw [block_6656_7168] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_7168_7424 : hitsIn 7168 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_7424_7680 : hitsIn 7424 256 = [] := by decide +kernel

private theorem block_7168_7680 : hitsIn 7168 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_7168_7424]
  change _ ++ hitsIn 7424 256 = _
  rw [block_7424_7680] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_7680_7936 : hitsIn 7680 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_7936_8192 : hitsIn 7936 256 = [] := by decide +kernel

private theorem block_7680_8192 : hitsIn 7680 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_7680_7936]
  change _ ++ hitsIn 7936 256 = _
  rw [block_7936_8192] <;> rfl

private theorem block_7168_8192 : hitsIn 7168 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_7168_7680]
  change _ ++ hitsIn 7680 512 = _
  rw [block_7680_8192] <;> rfl

private theorem block_6144_8192 : hitsIn 6144 2048 = [6224] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_6144_7168]
  change _ ++ hitsIn 7168 1024 = _
  rw [block_7168_8192] <;> rfl

private theorem block_4096_8192 : hitsIn 4096 4096 = [4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740,5504,6224] := by
  rw [show 4096=2048+2048 by decide,matches_add,block_4096_6144]
  change _ ++ hitsIn 6144 2048 = _
  rw [block_6144_8192] <;> rfl

private theorem block_0_8192 : hitsIn 0 8192 = [0,41,68,131,132,368,384,528,1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824,2561,3282,3284,3336,3344,3392,3524,4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740,5504,6224] := by
  rw [show 8192=4096+4096 by decide,matches_add,block_0_4096]
  change _ ++ hitsIn 4096 4096 = _
  rw [block_4096_8192] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_8192_8448 : hitsIn 8192 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_8448_8704 : hitsIn 8448 256 = [] := by decide +kernel

private theorem block_8192_8704 : hitsIn 8192 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_8192_8448]
  change _ ++ hitsIn 8448 256 = _
  rw [block_8448_8704] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_8704_8960 : hitsIn 8704 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_8960_9216 : hitsIn 8960 256 = [] := by decide +kernel

private theorem block_8704_9216 : hitsIn 8704 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_8704_8960]
  change _ ++ hitsIn 8960 256 = _
  rw [block_8960_9216] <;> rfl

private theorem block_8192_9216 : hitsIn 8192 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_8192_8704]
  change _ ++ hitsIn 8704 512 = _
  rw [block_8704_9216] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_9216_9472 : hitsIn 9216 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_9472_9728 : hitsIn 9472 256 = [] := by decide +kernel

private theorem block_9216_9728 : hitsIn 9216 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_9216_9472]
  change _ ++ hitsIn 9472 256 = _
  rw [block_9472_9728] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_9728_9984 : hitsIn 9728 256 = [9856,9857,9869,9896,9923,9924] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_9984_10240 : hitsIn 9984 256 = [10004] := by decide +kernel

private theorem block_9728_10240 : hitsIn 9728 512 = [9856,9857,9869,9896,9923,9924,10004] := by
  rw [show 512=256+256 by decide,matches_add,block_9728_9984]
  change _ ++ hitsIn 9984 256 = _
  rw [block_9984_10240] <;> rfl

private theorem block_9216_10240 : hitsIn 9216 1024 = [9856,9857,9869,9896,9923,9924,10004] := by
  rw [show 1024=512+512 by decide,matches_add,block_9216_9728]
  change _ ++ hitsIn 9728 512 = _
  rw [block_9728_10240] <;> rfl

private theorem block_8192_10240 : hitsIn 8192 2048 = [9856,9857,9869,9896,9923,9924,10004] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_8192_9216]
  change _ ++ hitsIn 9216 1024 = _
  rw [block_9216_10240] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_10240_10496 : hitsIn 10240 256 = [10247,10250,10274,10337] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_10496_10752 : hitsIn 10496 256 = [10571,10572,10580,10625] := by decide +kernel

private theorem block_10240_10752 : hitsIn 10240 512 = [10247,10250,10274,10337,10571,10572,10580,10625] := by
  rw [show 512=256+256 by decide,matches_add,block_10240_10496]
  change _ ++ hitsIn 10496 256 = _
  rw [block_10496_10752] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_10752_11008 : hitsIn 10752 256 = [10760,10816,10817] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_11008_11264 : hitsIn 11008 256 = [] := by decide +kernel

private theorem block_10752_11264 : hitsIn 10752 512 = [10760,10816,10817] := by
  rw [show 512=256+256 by decide,matches_add,block_10752_11008]
  change _ ++ hitsIn 11008 256 = _
  rw [block_11008_11264] <;> rfl

private theorem block_10240_11264 : hitsIn 10240 1024 = [10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817] := by
  rw [show 1024=512+512 by decide,matches_add,block_10240_10752]
  change _ ++ hitsIn 10752 512 = _
  rw [block_10752_11264] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_11264_11520 : hitsIn 11264 256 = [11328] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_11520_11776 : hitsIn 11520 256 = [] := by decide +kernel

private theorem block_11264_11776 : hitsIn 11264 512 = [11328] := by
  rw [show 512=256+256 by decide,matches_add,block_11264_11520]
  change _ ++ hitsIn 11520 256 = _
  rw [block_11520_11776] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_11776_12032 : hitsIn 11776 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_12032_12288 : hitsIn 12032 256 = [] := by decide +kernel

private theorem block_11776_12288 : hitsIn 11776 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_11776_12032]
  change _ ++ hitsIn 12032 256 = _
  rw [block_12032_12288] <;> rfl

private theorem block_11264_12288 : hitsIn 11264 1024 = [11328] := by
  rw [show 1024=512+512 by decide,matches_add,block_11264_11776]
  change _ ++ hitsIn 11776 512 = _
  rw [block_11776_12288] <;> rfl

private theorem block_10240_12288 : hitsIn 10240 2048 = [10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817,11328] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_10240_11264]
  change _ ++ hitsIn 11264 1024 = _
  rw [block_11264_12288] <;> rfl

private theorem block_8192_12288 : hitsIn 8192 4096 = [9856,9857,9869,9896,9923,9924,10004,10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817,11328] := by
  rw [show 4096=2048+2048 by decide,matches_add,block_8192_10240]
  change _ ++ hitsIn 10240 2048 = _
  rw [block_10240_12288] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_12288_12544 : hitsIn 12288 256 = [12288,12299,12300,12308,12354,12356] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_12544_12800 : hitsIn 12544 256 = [] := by decide +kernel

private theorem block_12288_12800 : hitsIn 12288 512 = [12288,12299,12300,12308,12354,12356] := by
  rw [show 512=256+256 by decide,matches_add,block_12288_12544]
  change _ ++ hitsIn 12544 256 = _
  rw [block_12544_12800] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_12800_13056 : hitsIn 12800 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_13056_13312 : hitsIn 13056 256 = [] := by decide +kernel

private theorem block_12800_13312 : hitsIn 12800 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_12800_13056]
  change _ ++ hitsIn 13056 256 = _
  rw [block_13056_13312] <;> rfl

private theorem block_12288_13312 : hitsIn 12288 1024 = [12288,12299,12300,12308,12354,12356] := by
  rw [show 1024=512+512 by decide,matches_add,block_12288_12800]
  change _ ++ hitsIn 12800 512 = _
  rw [block_12800_13312] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_13312_13568 : hitsIn 13312 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_13568_13824 : hitsIn 13568 256 = [13568] := by decide +kernel

private theorem block_13312_13824 : hitsIn 13312 512 = [13568] := by
  rw [show 512=256+256 by decide,matches_add,block_13312_13568]
  change _ ++ hitsIn 13568 256 = _
  rw [block_13568_13824] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_13824_14080 : hitsIn 13824 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_14080_14336 : hitsIn 14080 256 = [] := by decide +kernel

private theorem block_13824_14336 : hitsIn 13824 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_13824_14080]
  change _ ++ hitsIn 14080 256 = _
  rw [block_14080_14336] <;> rfl

private theorem block_13312_14336 : hitsIn 13312 1024 = [13568] := by
  rw [show 1024=512+512 by decide,matches_add,block_13312_13824]
  change _ ++ hitsIn 13824 512 = _
  rw [block_13824_14336] <;> rfl

private theorem block_12288_14336 : hitsIn 12288 2048 = [12288,12299,12300,12308,12354,12356,13568] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_12288_13312]
  change _ ++ hitsIn 13312 1024 = _
  rw [block_13312_14336] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_14336_14592 : hitsIn 14336 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_14592_14848 : hitsIn 14592 256 = [] := by decide +kernel

private theorem block_14336_14848 : hitsIn 14336 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_14336_14592]
  change _ ++ hitsIn 14592 256 = _
  rw [block_14592_14848] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_14848_15104 : hitsIn 14848 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_15104_15360 : hitsIn 15104 256 = [] := by decide +kernel

private theorem block_14848_15360 : hitsIn 14848 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_14848_15104]
  change _ ++ hitsIn 15104 256 = _
  rw [block_15104_15360] <;> rfl

private theorem block_14336_15360 : hitsIn 14336 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_14336_14848]
  change _ ++ hitsIn 14848 512 = _
  rw [block_14848_15360] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_15360_15616 : hitsIn 15360 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_15616_15872 : hitsIn 15616 256 = [] := by decide +kernel

private theorem block_15360_15872 : hitsIn 15360 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_15360_15616]
  change _ ++ hitsIn 15616 256 = _
  rw [block_15616_15872] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_15872_16128 : hitsIn 15872 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_16128_16256 : hitsIn 16128 128 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_16256_16385 : hitsIn 16256 129 = [] := by decide +kernel

private theorem block_16128_16385 : hitsIn 16128 257 = [] := by
  rw [show 257=128+129 by decide,matches_add,block_16128_16256]
  change _ ++ hitsIn 16256 129 = _
  rw [block_16256_16385] <;> rfl

private theorem block_15872_16385 : hitsIn 15872 513 = [] := by
  rw [show 513=256+257 by decide,matches_add,block_15872_16128]
  change _ ++ hitsIn 16128 257 = _
  rw [block_16128_16385] <;> rfl

private theorem block_15360_16385 : hitsIn 15360 1025 = [] := by
  rw [show 1025=512+513 by decide,matches_add,block_15360_15872]
  change _ ++ hitsIn 15872 513 = _
  rw [block_15872_16385] <;> rfl

private theorem block_14336_16385 : hitsIn 14336 2049 = [] := by
  rw [show 2049=1024+1025 by decide,matches_add,block_14336_15360]
  change _ ++ hitsIn 15360 1025 = _
  rw [block_15360_16385] <;> rfl

private theorem block_12288_16385 : hitsIn 12288 4097 = [12288,12299,12300,12308,12354,12356,13568] := by
  rw [show 4097=2048+2049 by decide,matches_add,block_12288_14336]
  change _ ++ hitsIn 14336 2049 = _
  rw [block_14336_16385] <;> rfl

private theorem block_8192_16385 : hitsIn 8192 8193 = [9856,9857,9869,9896,9923,9924,10004,10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817,11328,12288,12299,12300,12308,12354,12356,13568] := by
  rw [show 8193=4096+4097 by decide,matches_add,block_8192_12288]
  change _ ++ hitsIn 12288 4097 = _
  rw [block_12288_16385] <;> rfl

private theorem block_0_16385 : hitsIn 0 16385 = [0,41,68,131,132,368,384,528,1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824,2561,3282,3284,3336,3344,3392,3524,4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740,5504,6224,9856,9857,9869,9896,9923,9924,10004,10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817,11328,12288,12299,12300,12308,12354,12356,13568] := by
  rw [show 16385=8192+8193 by decide,matches_add,block_0_8192]
  change _ ++ hitsIn 8192 8193 = _
  rw [block_8192_16385] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_16385_16641 : hitsIn 16385 256 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_16641_16897 : hitsIn 16641 256 = [16647,16650,16652,16658,16664,16674,16676,16736,16896] := by decide +kernel

private theorem block_16385_16897 : hitsIn 16385 512 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896] := by
  rw [show 512=256+256 by decide,matches_add,block_16385_16641]
  change _ ++ hitsIn 16641 256 = _
  rw [block_16641_16897] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_16897_17153 : hitsIn 16897 256 = [16916] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_17153_17409 : hitsIn 17153 256 = [17160,17168,17216,17408] := by decide +kernel

private theorem block_16897_17409 : hitsIn 16897 512 = [16916,17160,17168,17216,17408] := by
  rw [show 512=256+256 by decide,matches_add,block_16897_17153]
  change _ ++ hitsIn 17153 256 = _
  rw [block_17153_17409] <;> rfl

private theorem block_16385_17409 : hitsIn 16385 1024 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408] := by
  rw [show 1024=512+512 by decide,matches_add,block_16385_16897]
  change _ ++ hitsIn 16897 512 = _
  rw [block_16897_17409] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_17409_17665 : hitsIn 17409 256 = [17456] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_17665_17921 : hitsIn 17665 256 = [] := by decide +kernel

private theorem block_17409_17921 : hitsIn 17409 512 = [17456] := by
  rw [show 512=256+256 by decide,matches_add,block_17409_17665]
  change _ ++ hitsIn 17665 256 = _
  rw [block_17665_17921] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_17921_18177 : hitsIn 17921 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_18177_18433 : hitsIn 18177 256 = [] := by decide +kernel

private theorem block_17921_18433 : hitsIn 17921 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_17921_18177]
  change _ ++ hitsIn 18177 256 = _
  rw [block_18177_18433] <;> rfl

private theorem block_17409_18433 : hitsIn 17409 1024 = [17456] := by
  rw [show 1024=512+512 by decide,matches_add,block_17409_17921]
  change _ ++ hitsIn 17921 512 = _
  rw [block_17921_18433] <;> rfl

private theorem block_16385_18433 : hitsIn 16385 2048 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408,17456] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_16385_17409]
  change _ ++ hitsIn 17409 1024 = _
  rw [block_17409_18433] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_18433_18689 : hitsIn 18433 256 = [18592,18593] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_18689_18945 : hitsIn 18689 256 = [18752] := by decide +kernel

private theorem block_18433_18945 : hitsIn 18433 512 = [18592,18593,18752] := by
  rw [show 512=256+256 by decide,matches_add,block_18433_18689]
  change _ ++ hitsIn 18689 256 = _
  rw [block_18689_18945] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_18945_19201 : hitsIn 18945 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_19201_19457 : hitsIn 19201 256 = [] := by decide +kernel

private theorem block_18945_19457 : hitsIn 18945 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_18945_19201]
  change _ ++ hitsIn 19201 256 = _
  rw [block_19201_19457] <;> rfl

private theorem block_18433_19457 : hitsIn 18433 1024 = [18592,18593,18752] := by
  rw [show 1024=512+512 by decide,matches_add,block_18433_18945]
  change _ ++ hitsIn 18945 512 = _
  rw [block_18945_19457] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_19457_19713 : hitsIn 19457 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_19713_19969 : hitsIn 19713 256 = [] := by decide +kernel

private theorem block_19457_19969 : hitsIn 19457 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_19457_19713]
  change _ ++ hitsIn 19713 256 = _
  rw [block_19713_19969] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_19969_20225 : hitsIn 19969 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_20225_20481 : hitsIn 20225 256 = [] := by decide +kernel

private theorem block_19969_20481 : hitsIn 19969 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_19969_20225]
  change _ ++ hitsIn 20225 256 = _
  rw [block_20225_20481] <;> rfl

private theorem block_19457_20481 : hitsIn 19457 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_19457_19969]
  change _ ++ hitsIn 19969 512 = _
  rw [block_19969_20481] <;> rfl

private theorem block_18433_20481 : hitsIn 18433 2048 = [18592,18593,18752] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_18433_19457]
  change _ ++ hitsIn 19457 1024 = _
  rw [block_19457_20481] <;> rfl

private theorem block_16385_20481 : hitsIn 16385 4096 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408,17456,18592,18593,18752] := by
  rw [show 4096=2048+2048 by decide,matches_add,block_16385_18433]
  change _ ++ hitsIn 18433 2048 = _
  rw [block_18433_20481] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_20481_20737 : hitsIn 20481 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_20737_20993 : hitsIn 20737 256 = [] := by decide +kernel

private theorem block_20481_20993 : hitsIn 20481 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_20481_20737]
  change _ ++ hitsIn 20737 256 = _
  rw [block_20737_20993] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_20993_21249 : hitsIn 20993 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_21249_21505 : hitsIn 21249 256 = [] := by decide +kernel

private theorem block_20993_21505 : hitsIn 20993 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_20993_21249]
  change _ ++ hitsIn 21249 256 = _
  rw [block_21249_21505] <;> rfl

private theorem block_20481_21505 : hitsIn 20481 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_20481_20993]
  change _ ++ hitsIn 20993 512 = _
  rw [block_20993_21505] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_21505_21761 : hitsIn 21505 256 = [21506] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_21761_22017 : hitsIn 21761 256 = [] := by decide +kernel

private theorem block_21505_22017 : hitsIn 21505 512 = [21506] := by
  rw [show 512=256+256 by decide,matches_add,block_21505_21761]
  change _ ++ hitsIn 21761 256 = _
  rw [block_21761_22017] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_22017_22273 : hitsIn 22017 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_22273_22529 : hitsIn 22273 256 = [] := by decide +kernel

private theorem block_22017_22529 : hitsIn 22017 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_22017_22273]
  change _ ++ hitsIn 22273 256 = _
  rw [block_22273_22529] <;> rfl

private theorem block_21505_22529 : hitsIn 21505 1024 = [21506] := by
  rw [show 1024=512+512 by decide,matches_add,block_21505_22017]
  change _ ++ hitsIn 22017 512 = _
  rw [block_22017_22529] <;> rfl

private theorem block_20481_22529 : hitsIn 20481 2048 = [21506] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_20481_21505]
  change _ ++ hitsIn 21505 1024 = _
  rw [block_21505_22529] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_22529_22785 : hitsIn 22529 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_22785_23041 : hitsIn 22785 256 = [] := by decide +kernel

private theorem block_22529_23041 : hitsIn 22529 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_22529_22785]
  change _ ++ hitsIn 22785 256 = _
  rw [block_22785_23041] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_23041_23297 : hitsIn 23041 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_23297_23553 : hitsIn 23297 256 = [] := by decide +kernel

private theorem block_23041_23553 : hitsIn 23041 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_23041_23297]
  change _ ++ hitsIn 23297 256 = _
  rw [block_23297_23553] <;> rfl

private theorem block_22529_23553 : hitsIn 22529 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_22529_23041]
  change _ ++ hitsIn 23041 512 = _
  rw [block_23041_23553] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_23553_23809 : hitsIn 23553 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_23809_24065 : hitsIn 23809 256 = [] := by decide +kernel

private theorem block_23553_24065 : hitsIn 23553 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_23553_23809]
  change _ ++ hitsIn 23809 256 = _
  rw [block_23809_24065] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_24065_24321 : hitsIn 24065 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_24321_24577 : hitsIn 24321 256 = [] := by decide +kernel

private theorem block_24065_24577 : hitsIn 24065 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_24065_24321]
  change _ ++ hitsIn 24321 256 = _
  rw [block_24321_24577] <;> rfl

private theorem block_23553_24577 : hitsIn 23553 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_23553_24065]
  change _ ++ hitsIn 24065 512 = _
  rw [block_24065_24577] <;> rfl

private theorem block_22529_24577 : hitsIn 22529 2048 = [] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_22529_23553]
  change _ ++ hitsIn 23553 1024 = _
  rw [block_23553_24577] <;> rfl

private theorem block_20481_24577 : hitsIn 20481 4096 = [21506] := by
  rw [show 4096=2048+2048 by decide,matches_add,block_20481_22529]
  change _ ++ hitsIn 22529 2048 = _
  rw [block_22529_24577] <;> rfl

private theorem block_16385_24577 : hitsIn 16385 8192 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408,17456,18592,18593,18752,21506] := by
  rw [show 8192=4096+4096 by decide,matches_add,block_16385_20481]
  change _ ++ hitsIn 20481 4096 = _
  rw [block_20481_24577] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_24577_24833 : hitsIn 24577 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_24833_25089 : hitsIn 24833 256 = [] := by decide +kernel

private theorem block_24577_25089 : hitsIn 24577 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_24577_24833]
  change _ ++ hitsIn 24833 256 = _
  rw [block_24833_25089] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_25089_25345 : hitsIn 25089 256 = [25152] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_25345_25601 : hitsIn 25345 256 = [] := by decide +kernel

private theorem block_25089_25601 : hitsIn 25089 512 = [25152] := by
  rw [show 512=256+256 by decide,matches_add,block_25089_25345]
  change _ ++ hitsIn 25345 256 = _
  rw [block_25345_25601] <;> rfl

private theorem block_24577_25601 : hitsIn 24577 1024 = [25152] := by
  rw [show 1024=512+512 by decide,matches_add,block_24577_25089]
  change _ ++ hitsIn 25089 512 = _
  rw [block_25089_25601] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_25601_25857 : hitsIn 25601 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_25857_26113 : hitsIn 25857 256 = [] := by decide +kernel

private theorem block_25601_26113 : hitsIn 25601 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_25601_25857]
  change _ ++ hitsIn 25857 256 = _
  rw [block_25857_26113] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_26113_26369 : hitsIn 26113 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_26369_26625 : hitsIn 26369 256 = [] := by decide +kernel

private theorem block_26113_26625 : hitsIn 26113 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_26113_26369]
  change _ ++ hitsIn 26369 256 = _
  rw [block_26369_26625] <;> rfl

private theorem block_25601_26625 : hitsIn 25601 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_25601_26113]
  change _ ++ hitsIn 26113 512 = _
  rw [block_26113_26625] <;> rfl

private theorem block_24577_26625 : hitsIn 24577 2048 = [25152] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_24577_25601]
  change _ ++ hitsIn 25601 1024 = _
  rw [block_25601_26625] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_26625_26881 : hitsIn 26625 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_26881_27137 : hitsIn 26881 256 = [] := by decide +kernel

private theorem block_26625_27137 : hitsIn 26625 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_26625_26881]
  change _ ++ hitsIn 26881 256 = _
  rw [block_26881_27137] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_27137_27393 : hitsIn 27137 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_27393_27649 : hitsIn 27393 256 = [] := by decide +kernel

private theorem block_27137_27649 : hitsIn 27137 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_27137_27393]
  change _ ++ hitsIn 27393 256 = _
  rw [block_27393_27649] <;> rfl

private theorem block_26625_27649 : hitsIn 26625 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_26625_27137]
  change _ ++ hitsIn 27137 512 = _
  rw [block_27137_27649] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_27649_27905 : hitsIn 27649 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_27905_28161 : hitsIn 27905 256 = [] := by decide +kernel

private theorem block_27649_28161 : hitsIn 27649 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_27649_27905]
  change _ ++ hitsIn 27905 256 = _
  rw [block_27905_28161] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_28161_28417 : hitsIn 28161 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_28417_28673 : hitsIn 28417 256 = [] := by decide +kernel

private theorem block_28161_28673 : hitsIn 28161 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_28161_28417]
  change _ ++ hitsIn 28417 256 = _
  rw [block_28417_28673] <;> rfl

private theorem block_27649_28673 : hitsIn 27649 1024 = [] := by
  rw [show 1024=512+512 by decide,matches_add,block_27649_28161]
  change _ ++ hitsIn 28161 512 = _
  rw [block_28161_28673] <;> rfl

private theorem block_26625_28673 : hitsIn 26625 2048 = [] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_26625_27649]
  change _ ++ hitsIn 27649 1024 = _
  rw [block_27649_28673] <;> rfl

private theorem block_24577_28673 : hitsIn 24577 4096 = [25152] := by
  rw [show 4096=2048+2048 by decide,matches_add,block_24577_26625]
  change _ ++ hitsIn 26625 2048 = _
  rw [block_26625_28673] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_28673_28929 : hitsIn 28673 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_28929_29185 : hitsIn 28929 256 = [] := by decide +kernel

private theorem block_28673_29185 : hitsIn 28673 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_28673_28929]
  change _ ++ hitsIn 28929 256 = _
  rw [block_28929_29185] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_29185_29441 : hitsIn 29185 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_29441_29697 : hitsIn 29441 256 = [29525,29528,29552] := by decide +kernel

private theorem block_29185_29697 : hitsIn 29185 512 = [29525,29528,29552] := by
  rw [show 512=256+256 by decide,matches_add,block_29185_29441]
  change _ ++ hitsIn 29441 256 = _
  rw [block_29441_29697] <;> rfl

private theorem block_28673_29697 : hitsIn 28673 1024 = [29525,29528,29552] := by
  rw [show 1024=512+512 by decide,matches_add,block_28673_29185]
  change _ ++ hitsIn 29185 512 = _
  rw [block_29185_29697] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_29697_29953 : hitsIn 29697 256 = [29697,29714,29769,29777] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_29953_30209 : hitsIn 29953 256 = [] := by decide +kernel

private theorem block_29697_30209 : hitsIn 29697 512 = [29697,29714,29769,29777] := by
  rw [show 512=256+256 by decide,matches_add,block_29697_29953]
  change _ ++ hitsIn 29953 256 = _
  rw [block_29953_30209] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_30209_30465 : hitsIn 30209 256 = [30272,30336] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_30465_30721 : hitsIn 30465 256 = [] := by decide +kernel

private theorem block_30209_30721 : hitsIn 30209 512 = [30272,30336] := by
  rw [show 512=256+256 by decide,matches_add,block_30209_30465]
  change _ ++ hitsIn 30465 256 = _
  rw [block_30465_30721] <;> rfl

private theorem block_29697_30721 : hitsIn 29697 1024 = [29697,29714,29769,29777,30272,30336] := by
  rw [show 1024=512+512 by decide,matches_add,block_29697_30209]
  change _ ++ hitsIn 30209 512 = _
  rw [block_30209_30721] <;> rfl

private theorem block_28673_30721 : hitsIn 28673 2048 = [29525,29528,29552,29697,29714,29769,29777,30272,30336] := by
  rw [show 2048=1024+1024 by decide,matches_add,block_28673_29697]
  change _ ++ hitsIn 29697 1024 = _
  rw [block_29697_30721] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_30721_30977 : hitsIn 30721 256 = [30740] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_30977_31233 : hitsIn 30977 256 = [30984,30992] := by decide +kernel

private theorem block_30721_31233 : hitsIn 30721 512 = [30740,30984,30992] := by
  rw [show 512=256+256 by decide,matches_add,block_30721_30977]
  change _ ++ hitsIn 30977 256 = _
  rw [block_30977_31233] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_31233_31489 : hitsIn 31233 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_31489_31745 : hitsIn 31489 256 = [] := by decide +kernel

private theorem block_31233_31745 : hitsIn 31233 512 = [] := by
  rw [show 512=256+256 by decide,matches_add,block_31233_31489]
  change _ ++ hitsIn 31489 256 = _
  rw [block_31489_31745] <;> rfl

private theorem block_30721_31745 : hitsIn 30721 1024 = [30740,30984,30992] := by
  rw [show 1024=512+512 by decide,matches_add,block_30721_31233]
  change _ ++ hitsIn 31233 512 = _
  rw [block_31233_31745] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_31745_32001 : hitsIn 31745 256 = [31748] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_32001_32257 : hitsIn 32001 256 = [] := by decide +kernel

private theorem block_31745_32257 : hitsIn 31745 512 = [31748] := by
  rw [show 512=256+256 by decide,matches_add,block_31745_32001]
  change _ ++ hitsIn 32001 256 = _
  rw [block_32001_32257] <;> rfl

set_option maxRecDepth 16000 in
private theorem block_32257_32513 : hitsIn 32257 256 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_32513_32641 : hitsIn 32513 128 = [] := by decide +kernel

set_option maxRecDepth 16000 in
private theorem block_32641_32770 : hitsIn 32641 129 = [] := by decide +kernel

private theorem block_32513_32770 : hitsIn 32513 257 = [] := by
  rw [show 257=128+129 by decide,matches_add,block_32513_32641]
  change _ ++ hitsIn 32641 129 = _
  rw [block_32641_32770] <;> rfl

private theorem block_32257_32770 : hitsIn 32257 513 = [] := by
  rw [show 513=256+257 by decide,matches_add,block_32257_32513]
  change _ ++ hitsIn 32513 257 = _
  rw [block_32513_32770] <;> rfl

private theorem block_31745_32770 : hitsIn 31745 1025 = [31748] := by
  rw [show 1025=512+513 by decide,matches_add,block_31745_32257]
  change _ ++ hitsIn 32257 513 = _
  rw [block_32257_32770] <;> rfl

private theorem block_30721_32770 : hitsIn 30721 2049 = [30740,30984,30992,31748] := by
  rw [show 2049=1024+1025 by decide,matches_add,block_30721_31745]
  change _ ++ hitsIn 31745 1025 = _
  rw [block_31745_32770] <;> rfl

private theorem block_28673_32770 : hitsIn 28673 4097 = [29525,29528,29552,29697,29714,29769,29777,30272,30336,30740,30984,30992,31748] := by
  rw [show 4097=2048+2049 by decide,matches_add,block_28673_30721]
  change _ ++ hitsIn 30721 2049 = _
  rw [block_30721_32770] <;> rfl

private theorem block_24577_32770 : hitsIn 24577 8193 = [25152,29525,29528,29552,29697,29714,29769,29777,30272,30336,30740,30984,30992,31748] := by
  rw [show 8193=4096+4097 by decide,matches_add,block_24577_28673]
  change _ ++ hitsIn 28673 4097 = _
  rw [block_28673_32770] <;> rfl

private theorem block_16385_32770 : hitsIn 16385 16385 = [16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408,17456,18592,18593,18752,21506,25152,29525,29528,29552,29697,29714,29769,29777,30272,30336,30740,30984,30992,31748] := by
  rw [show 16385=8192+8193 by decide,matches_add,block_16385_24577]
  change _ ++ hitsIn 24577 8193 = _
  rw [block_24577_32770] <;> rfl

private theorem block_0_32770 : hitsIn 0 32770 = [0,41,68,131,132,368,384,528,1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824,2561,3282,3284,3336,3344,3392,3524,4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740,5504,6224,9856,9857,9869,9896,9923,9924,10004,10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817,11328,12288,12299,12300,12308,12354,12356,13568,16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408,17456,18592,18593,18752,21506,25152,29525,29528,29552,29697,29714,29769,29777,30272,30336,30740,30984,30992,31748] := by
  rw [show 32770=16385+16385 by decide,matches_add,block_0_16385]
  change _ ++ hitsIn 16385 16385 = _
  rw [block_16385_32770] <;> rfl

def hits : List ℕ := [0,41,68,131,132,368,384,528,1095,1098,1100,1106,1112,1122,1124,1152,1176,1346,1824,2561,3282,3284,3336,3344,3392,3524,4098,4101,4104,4112,4118,4128,4172,4352,4496,4739,4740,5504,6224,9856,9857,9869,9896,9923,9924,10004,10247,10250,10274,10337,10571,10572,10580,10625,10760,10816,10817,11328,12288,12299,12300,12308,12354,12356,13568,16407,16410,16413,16417,16422,16434,16436,16440,16449,16458,16460,16466,16485,16488,16496,16513,16592,16647,16650,16652,16658,16664,16674,16676,16736,16896,16916,17160,17168,17216,17408,17456,18592,18593,18752,21506,25152,29525,29528,29552,29697,29714,29769,29777,30272,30336,30740,30984,30992,31748]


theorem enumeration : (List.range 32770).filter digitMatch = hits := by
  calc
    _ = (List.range 32770).filter good := by
      apply List.filter_congr
      intro n hn
      have cap := List.mem_range.mp hn
      simpa only [good_eq (by omega : n<65536)]
    _ = hits := by simpa only [List.range_eq_range',hitsIn,hits] using block_0_32770

theorem matches_iff {n : ℕ} (lt : n<32770) : digitMatch n=true ↔ n∈hits := by
  rw [← enumeration,List.mem_filter]
  simp [List.mem_range.mpr lt]

theorem no_earlier : ∀ n : Fin 32770, ¬ (∀ i : Fin 3, digitMatch (n.val+i.val)=true) := by
  have verified : ∀ x∈hits, x+2<32770 ∧ (x+1∉hits ∨ x+2∉hits) := by decide +kernel
  intro n all
  have at0 : digitMatch n.val=true := all 0
  have at1 : digitMatch (n.val+1)=true := all 1
  have at2 : digitMatch (n.val+2)=true := all 2
  obtain ⟨cap,fail⟩ := verified _ ((matches_iff n.isLt).mp at0)
  rcases fail with h | h
  · exact h ((matches_iff (by omega)).mp at1)
  · exact h ((matches_iff cap).mp at2)

end Deldor14.OppositeDigits
open Deldor14.OppositeDigits

theorem OMA.solution : type_of% @OMA.S_oeis_a334765.main := by
  refine ⟨no_four,?_,no_earlier,?_⟩
  · intro i
    rw [← good_eq (by have := i.isLt; omega)]
    fin_cases i <;> decide +kernel
  · rw [List.countP_eq_length_filter,enumeration]; decide
