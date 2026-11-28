import Mathlib

/-! The centered product inequality survives the finite-prefix and power-mixture
join. The argument uses only the stated lower bound and supermultiplicativity
of the tail profile. -/

namespace Erdos142HybridProduct

def size (m n : ℕ) := m*n+(m-1)*(n-1)

noncomputable def hybrid (R : ℕ → ℕ) (J : ℝ → ℝ) (P X n : ℕ) : ℕ :=
  if n ≤ X then max (R n) ⌈(n:ℝ)/P⌉₊ else ⌈((X:ℝ)/P)*J ((n:ℝ)/X)⌉₊

private theorem compare {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    5*(m*n) ≤ 4*size m n ∧ size m n ≤ 2*(m*n) := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨b,rfl⟩ := Nat.exists_eq_add_of_le hn
  unfold size
  rw [show 2+a-1=1+a by omega, show 2+b-1=1+b by omega]
  constructor <;> nlinarith

theorem preserve (R : ℕ → ℕ) (J : ℝ → ℝ) (P X : ℕ)
    (hP : 4 ≤ P) (hX : 10*P ≤ X) (rP : 10 ≤ R P) (rmono : Monotone R)
    (rbound : ∀ n, R n ≤ n) (rone : R 1=1)
    (rprod : ∀ m n, 1 ≤ m → 1 ≤ n → R m*R n ≤ R (size m n))
    (rtail : ∀ n, X ≤ n → (R n : ℝ) ≤ (n:ℝ)/(2*P))
    (jone : ∀ u : ℝ, 1 ≤ u → 1 ≤ J u)
    (jmono : MonotoneOn J (Set.Ici 1))
    (jmul : ∀ u v : ℝ, 1 ≤ u → 1 ≤ v → J u*J v ≤ J (u*v))
    (jlocal : ∀ u : ℝ, 1 ≤ u → u ≤ 2*X → 9/10*u ≤ J u)
    (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    hybrid R J P X m * hybrid R J P X n  ≤  hybrid R J P X (size m n) := by
  let H := hybrid R J P X
  let K : ℝ := (X:ℝ)/P
  have p : (0:ℝ)<P := by exact_mod_cast (show 0<P by omega)
  have x : (0:ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hp : (4:ℝ) ≤ P := by exact_mod_cast hP
  have k : 10 ≤ K := (le_div_iff₀ p).mpr (by exact_mod_cast hX)
  have cap {a : ℕ} (ha : a ≤ X) : H a  ≤  a := by
    change (if a ≤ X then _ else _)  ≤  a
    rw [if_pos ha]
    apply max_le (rbound a)
    apply Nat.ceil_le.mpr
    apply div_le_self (by positivity) (by linarith)
  have hi {a : ℕ} (ha : X<a) : (H a:ℝ)  ≤  11/10*(K*J ((a:ℝ)/X)) := by
    have ja := jone ((a:ℝ)/X) ((one_le_div x).mpr (by exact_mod_cast ha.le))
    have pos : 10 ≤ K*J ((a:ℝ)/X) := k.trans (le_mul_of_one_le_right (by linarith) ja)
    change (((if a ≤ X then _ else _) : ℕ) : ℝ)  ≤  _
    rw [if_neg ha.not_ge]
    have e := Nat.ceil_lt_add_one (show 0 ≤ K*J ((a:ℝ)/X) by linarith)
    change (⌈K*J ((a:ℝ)/X)⌉₊:ℝ)  ≤  _
    linarith
  have tail {a : ℕ} (ha : X<a) : K*J ((a:ℝ)/X)  ≤  (H a:ℝ) := by
    change _  ≤  (((if a ≤ X then _ else _) : ℕ) : ℝ)
    rw [if_neg ha.not_ge]
    exact Nat.le_ceil _
  have localLower {a : ℕ} (ha : a ≤ 2*(X*X)) : (9/10)*((a:ℝ)/P)  ≤  (H a:ℝ) := by
    by_cases hb : a ≤ X
    · have c : ⌈(a:ℝ)/P⌉₊  ≤  H a := by simp [H,hybrid,hb]
      have ceil : (a:ℝ)/P ≤ H a := (Nat.le_ceil _).trans (by exact_mod_cast c)
      linarith [show 0 ≤ (a:ℝ)/P by positivity]
    · have aone : 1 ≤ (a:ℝ)/X := (one_le_div x).mpr (by exact_mod_cast (Nat.le_of_not_ge hb))
      have top : (a:ℝ)/X ≤ 2*X := (div_le_iff₀ x).mpr (by
        exact_mod_cast (by simpa [Nat.mul_assoc] using ha : a  ≤  2*X*X))
      have q := mul_le_mul_of_nonneg_left (jlocal _ aone top) (show 0 ≤ K by linarith)
      calc 9/10*((a:ℝ)/P) = K*(9/10*((a:ℝ)/X)) := by dsimp [K]; field_simp
           _  ≤  _ := q.trans (tail (by omega))
  have one : H 1=1 := by
    have h := cap (a:=1) (by omega)
    have lo : 1 ≤ H 1 := by simp [H,hybrid,show 1 ≤ X by omega,rone]
    omega
  change H m*H n  ≤  H (size m n)
  by_cases mone : m=1
  · subst m; simp [one,size]
  by_cases none : n=1
  · subst n; simp [one,size]
  have m2 : 2 ≤ m := by omega
  have n2 : 2 ≤ n := by omega
  have ⟨lower,upper⟩ := compare m2 n2
  have mnr : 5*((m:ℝ)*n) ≤ 4*(size m n:ℝ) := by exact_mod_cast lower
  have mnr' : (size m n:ℝ) ≤ 2*((m:ℝ)*n) := by exact_mod_cast upper
  have cross {a b : ℕ} (a2 : 2 ≤ a) (b2 : 2 ≤ b) (ha : a ≤ X) (hb : X<b) :
      H a*H b  ≤  H (size a b) := by
    have ⟨lo,up⟩ := compare a2 b2
    have br : (0:ℝ)<b := by exact_mod_cast (show 0<b by omega)
    have ab : (5:ℝ)*((a:ℝ)*b) ≤ 4*(size a b:ℝ) := by exact_mod_cast lo
    have aone : 1 ≤ (b:ℝ)/X := (one_le_div x).mpr (by exact_mod_cast hb.le)
    have fraction : 11/10*(a:ℝ) ≤ 9/10*((size a b:ℝ)/b) := by
      rw [mul_div_assoc', le_div_iff₀ br]
      linarith
    have ba : b ≤ size a b := by
      calc b  ≤  a*b := Nat.le_mul_of_pos_left b (by omega)
           _  ≤  _ := Nat.le_add_right _ _
    have low : 1 ≤ (size a b:ℝ)/b := (one_le_div br).mpr (by exact_mod_cast ba)
    have high : (size a b:ℝ)/b ≤ 2*X := (div_le_iff₀ br).mpr (by
      exact_mod_cast up.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right b ha) : 2*(a*b) ≤ 2*X*b))
    have ja := fraction.trans (jlocal _ low high)
    have prod := jmul ((b:ℝ)/X) ((size a b:ℝ)/b) aone low
    have ident : ((b:ℝ)/X)*((size a b:ℝ)/b)=(size a b:ℝ)/X := by field_simp
    rw [ident] at prod
    have nonnegJ : 0 ≤ J ((b:ℝ)/X) := by linarith [jone _ aone]
    have cap' : (H a:ℝ) ≤ a := by exact_mod_cast cap ha
    have c := mul_le_mul cap' (hi hb) (by positivity) (by positivity)
    have d := mul_le_mul_of_nonneg_left ja (mul_nonneg (by linarith : 0 ≤ K) nonnegJ)
    have f := (mul_le_mul_of_nonneg_left prod (by linarith : 0 ≤ K)).trans (tail (hb.trans_le ba))
    exact_mod_cast (show (H a:ℝ)*(H b:ℝ) ≤ (H (size a b):ℝ) by linarith)
  by_cases ml : m ≤ X <;> by_cases nl : n ≤ X
  · have s := upper.trans (Nat.mul_le_mul_left 2 (Nat.mul_le_mul ml nl))
    by_cases both : H m=R m ∧ H n=R n
    · rw [both.1,both.2]
      apply (rprod m n hm hn).trans
      by_cases ss : size m n ≤ X
      · simp [H,hybrid,ss]
      · have a := rtail _ (Nat.le_of_not_ge ss)
        have b := localLower s
        exact_mod_cast (show (R (size m n):ℝ)  ≤  (H (size m n):ℝ) by
          rw [show (size m n:ℝ)/(2*P)=1/2*((size m n:ℝ)/P) by ring] at a
          linarith [show 0 ≤ (size m n:ℝ)/P by positivity])
    · have line {a : ℕ} (ha : a ≤ X) (apos : 1 ≤ a) (hh : H a≠R a) :
          (H a:ℝ)  ≤  11/10*((a:ℝ)/P) := by
        have strict : R a < ⌈(a:ℝ)/P⌉₊ := by
          by_contra! no
          exact hh (by simp [H,hybrid,ha,no])
        have pr : P ≤ a := by
          by_contra! no
          have c : ⌈(a:ℝ)/P⌉₊  ≤ 1 := Nat.ceil_le.mpr (by norm_num; apply (div_le_one p).mpr; exact_mod_cast no.le)
          have r := (rmono apos); rw [rone] at r; omega
        have low : 10<(a:ℝ)/P := by
          by_contra! neg
          have c : ⌈(a:ℝ)/P⌉₊  ≤ 10 := Nat.ceil_le.mpr neg
          have := rmono pr; omega
        have eq : H a=⌈(a:ℝ)/P⌉₊ := by simp [H,hybrid,ha,strict.le]
        rw [eq]
        linarith [Nat.ceil_lt_add_one (show 0 ≤ (a:ℝ)/P by positivity)]
      have prod : (H m:ℝ)*(H n:ℝ)  ≤  11/10*((m:ℝ)*n/P) := by
        by_cases mm : H m = R m
        · have c := mul_le_mul (show (H m:ℝ) ≤ m by exact_mod_cast cap ml)
              (line nl hn (fun h => both ⟨mm,h⟩)) (by positivity) (by positivity)
          exact c.trans_eq (by ring)
        · have c := mul_le_mul (line ml hm mm) (show (H n:ℝ) ≤ n by exact_mod_cast cap nl)
              (by positivity) (by positivity)
          exact c.trans_eq (by ring)
      have d := div_le_div_of_nonneg_right mnr p.le
      exact_mod_cast (show (H m:ℝ)*(H n:ℝ) ≤ (H (size m n):ℝ) by
        have lb := localLower s
        simp only [div_eq_mul_inv] at prod d lb
        linarith only [prod,d,lb,show 0≤(m:ℝ)*n*(P:ℝ)⁻¹ by positivity])
  · exact cross m2 n2 ml (by omega)
  · simpa [size, Nat.mul_comm] using cross n2 m2 nl (by omega)
  · have um : 1 ≤ (m:ℝ)/X := (one_le_div x).mpr (by exact_mod_cast (Nat.le_of_not_ge ml))
    have un : 1 ≤ (n:ℝ)/X := (one_le_div x).mpr (by exact_mod_cast (Nat.le_of_not_ge nl))
    have a := jmul _ _ um un
    have xx : (1:ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    have unit := one_le_mul_of_one_le_of_one_le um un
    have b := jmul _ _ xx unit
    have scale : (X:ℝ)*(((m:ℝ)/X)*((n:ℝ)/X))=(m:ℝ)*n/X := by field_simp
    rw [scale] at b
    have mn : m*n  ≤  size m n := Nat.le_add_right _ _
    have realmn : (m:ℝ)*n/X  ≤  (size m n:ℝ)/X := by gcongr; exact_mod_cast mn
    have after : X< size m n := (lt_of_not_ge ml).trans_le
      ((Nat.le_mul_of_pos_right m (by omega)).trans mn)
    have hist := jmono (show (m:ℝ)*n/X ∈ Set.Ici 1 by
      rw [← scale]; exact one_le_mul_of_one_le_of_one_le xx unit) (by exact (one_le_div x).mpr (by exact_mod_cast after.le)) realmn
    have jj := jlocal X xx (by linarith)
    have kx : (9/10)*X  ≥  (11/10:ℝ)^2*K := by
      dsimp [K]; rw [mul_div_assoc']; apply (div_le_iff₀ p).mpr; nlinarith [mul_le_mul_of_nonneg_right hp x.le]
    have jm0 : 0 ≤ J ((m:ℝ)/X) := by linarith [jone _ um]
    have jn0 : 0 ≤ J ((n:ℝ)/X) := by linarith [jone _ un]
    have c := mul_le_mul (hi (by omega : X < m)) (hi (by omega : X < n)) (by positivity) (by positivity)
    have e := mul_le_mul (kx.trans jj) a (mul_nonneg jm0 jn0) (by linarith [jone _ xx])
    have f := (mul_le_mul_of_nonneg_left (e.trans (b.trans hist)) (show 0 ≤ K by linarith)).trans (tail after)
    exact_mod_cast (show (H m:ℝ)*(H n:ℝ) ≤ (H (size m n):ℝ) by linarith)

#print axioms preserve
end Erdos142HybridProduct
