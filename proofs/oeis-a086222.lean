import OMAStatements.S_oeis_a086222
import Mathlib

namespace Deldor14.LcmTriples
open OMA.S_oeis_a086222 Finset
private theorem distinct (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hlt : p<q) : a (p*q)=13 := by
  have cp := hp.coprime_iff_not_dvd.mpr (fun h => hlt.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  have op := hp.one_lt
  have oq := hq.one_lt
  let m := p*q
  have pm : p < m := by dsimp [m];nlinarith [hp.pos,hq.two_le]
  have qm : q < m := by dsimp [m];nlinarith [hq.pos,hp.two_le]
  have mn : m≠0 := by unfold m;exact mul_ne_zero hp.ne_zero hq.ne_zero
  have pd : p ∣ m := dvd_mul_right _ _
  have qd : q ∣ m := dvd_mul_left _ _
  have divs : m.divisors={1,p,q,m} := by
    symm
    apply eq_of_subset_of_card_le
    · intro z hz
      simp only [mem_insert,mem_singleton] at hz
      rcases hz with rfl|rfl|rfl|rfl <;> simp_all [Nat.mem_divisors]
    · change (p*q).divisors.card≤_
      rw [cp.card_divisors_mul,hp.divisors,hq.divisors]
      simp [Finset.card_insert_of_notMem,op.ne,oq.ne,hlt.ne,pm.ne,qm.ne,(op.trans pm).ne]
  have pq : p.lcm q=m := cp.lcm_eq_mul
  have qp : q.lcm p=m := by rw [Nat.lcm_comm,pq]
  have pm' := Nat.lcm_eq_right_iff_dvd.mpr pd
  have mp' := Nat.lcm_eq_left_iff_dvd.mpr pd
  have qm' := Nat.lcm_eq_right_iff_dvd.mpr qd
  have mq' := Nat.lcm_eq_left_iff_dvd.mpr qd
  change a m=13
  unfold a
  rw [divs]
  simp [Finset.filter_insert,Finset.filter_singleton,Finset.sum_insert,op.ne,oq.ne,hlt.ne,pm.ne,qm.ne,(op.trans pm).ne,
    hp.ne_one,hq.ne_one,pm.ne',qm.ne',(op.trans pm).ne',pq,qp,pm',mp',qm',mq',op.le,oq.le,hlt.le,pm.le,qm.le,
    (op.trans pm).le,not_le.mpr op,not_le.mpr oq,not_le.mpr hlt,not_le.mpr pm,not_le.mpr qm,not_le.mpr (op.trans pm)]
private theorem square (p : ℕ) (hp : p.Prime) : a (p^2)=6 := by
  let m := p^2
  have op := hp.one_lt
  have pm : p < m := by dsimp [m];nlinarith [hp.two_le]
  have pd : p ∣ m := dvd_pow_self p (by decide : 2≠0)
  have divs : m.divisors={1,p,m} := by
    ext x
    rw [Nat.mem_divisors_prime_pow hp 2]
    simp only [mem_insert,mem_singleton]
    constructor
    · rintro ⟨j,hj,rfl⟩
      interval_cases j <;> simp [m]
    · rintro (rfl|rfl|rfl)
      · exact ⟨0,by decide,by simp⟩
      · exact ⟨1,by decide,by simp⟩
      · exact ⟨2,le_rfl,rfl⟩
  change a m=6
  unfold a
  rw [divs]
  simp [Finset.filter_insert,Finset.filter_singleton,Finset.sum_insert,op.ne,pm.ne,pm.ne',(op.trans pm).ne,(op.trans pm).ne',Nat.lcm_eq_right_iff_dvd.mpr pd,
    Nat.lcm_eq_left_iff_dvd.mpr pd,op.le,pm.le,(op.trans pm).le,not_le.mpr op,not_le.mpr pm,not_le.mpr (op.trans pm)]
theorem result : type_of% @OMA.S_oeis_a086222.main := by
  refine ⟨?_,square⟩
  intro p q hp hq hn
  rcases lt_or_gt_of_ne hn with h|h
  · exact distinct p q hp hq h
  · rw [mul_comm];exact distinct q p hq hp h
end Deldor14.LcmTriples
theorem OMA.solution : type_of% @OMA.S_oeis_a086222.main := Deldor14.LcmTriples.result
