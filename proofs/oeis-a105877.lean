import OMAStatements.S_oeis_a105877
import Mathlib

theorem OMA.solution : type_of% @OMA.S_oeis_a105877.main := by
  intro p prime hp t prim
  letI : Fact p.Prime := ⟨prime⟩
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  have odd := prime.eq_two_or_odd.resolve_left (by omega)
  have halfPos : 0 < (p-1)/2 := by omega
  have symbol : legendreSym p (-5) = -1 := by
    apply (legendreSym.eq_neg_one_iff p).mpr
    rintro ⟨u,hu⟩
    norm_num at hu
    have sq : -5*t^2=(u*t)^2 := by rw [hu];ring
    have ne : u*t ≠ 0 := by
      intro h
      have one := prim.pow_eq_one
      rw [sq,h,zero_pow (by decide : (2:ℕ)≠0),zero_pow (by omega : p-1≠0)] at one
      exact zero_ne_one one
    have h := (prim.pow_eq_one_iff_dvd ((p-1)/2)).mp (by
      rw [sq,← pow_mul,show 2*((p-1)/2)=p-1 by omega]
      exact ZMod.pow_card_sub_one_eq_one ne)
    have := Nat.le_of_dvd halfPos h
    omega
  rw [legendreSym.at_neg (by omega : p≠2) 5] at symbol
  have reciprocal := legendreSym.quadratic_reciprocity_one_mod_four (p := 5) (q := p)
    (by decide) (by omega)
  norm_num only [Nat.cast_ofNat] at reciprocal
  rw [reciprocal,legendreSym.mod 5 (p:ℤ),ZMod.χ₄_nat_eq_if_mod_four] at symbol
  norm_num only [Nat.cast_ofNat] at symbol
  have u := Nat.mod_lt p (by decide : 0<20)
  generalize er : p%20=r at *
  have residues : p%20=11 ∨ p%20=13 ∨ p%20=17 ∨ p%20=19 := by
    have h₅ : (p:ℤ)%5=(r:ℤ)%5 := by omega
    have h₄ : p%4=r%4 := by omega
    have h₂ : p%2=r%2 := by omega
    rw [h₅,h₄,h₂] at symbol
    rw [er]
    interval_cases r <;> first | decide | norm_num at symbol
  exact ⟨by simpa [er] using residues,by
    rw [Nat.odd_iff]
    rcases residues with e | e | e | e <;> omega⟩
