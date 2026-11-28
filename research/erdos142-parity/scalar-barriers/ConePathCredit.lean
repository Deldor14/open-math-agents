import BernsteinInteger

/-! Finite binary splitting with a nonnegative boundary. The two letters
increase the exponent of y and of 1-y respectively. -/

namespace Erdos142ConePaths
open Finset

def prepend (b : Bool) : List Bool ↪ List Bool :=
  ⟨List.cons b, fun _ _ h => (List.cons.inj h).2⟩

@[simp] theorem prepend_apply (b : Bool) (w : List Bool) : prepend b w=b::w := rfl

noncomputable def paths (expand : ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → Finset (List Bool)
  | 0, _, _ => {[]}
  | n+1, i, h => by
    classical
    exact if expand i h then
      ((paths expand n (i+1) h).map (prepend true)) ∪
      ((paths expand n i (h+1)).map (prepend false)) else ∅

private theorem separate (s t : Finset (List Bool)) :
    Disjoint (s.map (prepend true)) (t.map (prepend false)) := by
  rw [Finset.disjoint_left]
  rintro w hw hw'
  obtain ⟨a,_,rfl⟩ := Finset.mem_map.mp hw
  obtain ⟨b,_,e⟩ := Finset.mem_map.mp hw'
  have : false=true := (List.cons.inj e).1
  contradiction

/-- The sum of the terminal weights at the prescribed depth is at most
the initial weight. Nodes stopped earlier absorb the remaining credit.
The nonnegativity assumption is restricted to the finite reachable range. -/
theorem credit (F : ℕ → ℕ → ℝ) (expand valid : ℕ → ℕ → Prop) (N : ℕ)
    (split : ∀ i h, valid i h → expand i h → F (i+1) h+F i (h+1)=F i h)
    (children : ∀ i h, valid i h → expand i h → valid (i+1) h ∧ valid i (h+1))
    (positive : ∀ i h, i+h ≤ N → valid i h → 0 ≤ F i h)
    {n i h : ℕ} (limit : n+i+h ≤ N) (node : valid i h) :
    ∑ w ∈ paths expand n i h, F (i+w.count true) (h+w.count false) ≤ F i h := by
  classical
  induction n generalizing i h with
  | zero => simp [paths]
  | succ n ih =>
    by_cases dec : expand i h
    · rw [paths,if_pos dec,sum_union (separate _ _),sum_map,sum_map]
      have c := children i h node dec
      have l := ih (i:=i+1) (h:=h) (by omega) c.1
      have r := ih (i:=i) (h:=h+1) (by omega) c.2
      have out := (add_le_add l r).trans_eq (split i h node dec)
      simpa [List.count_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using out
    · simp only [paths,if_neg dec, sum_empty]
      exact positive i h (by omega) node

/-- Every word for which all proper prefixes split is counted exactly as the
corresponding element of the finite set, independent of node collisions. -/
theorem mem_paths_of_prefix (expand : ℕ → ℕ → Prop) (w : List Bool) (i h : ℕ)
    (opens : ∀ (p : List Bool) (b : Bool) (s : List Bool), w=p++b::s →
        expand (i+p.count true) (h+p.count false)) : w∈paths expand w.length i h := by
  classical
  induction w generalizing i h with
  | nil => simp [paths]
  | cons b w ih =>
    have top : expand i h := by simpa using opens [] b w rfl
    simp only [List.length_cons,paths,if_pos top,mem_union]
    cases b with
    | false =>
      right
      apply mem_map.mpr
      refine ⟨w,ih i (h+1) (fun p b s e => ?_), rfl⟩
      have yes := opens (false::p) b s (by simp [e])
      simpa [List.count_cons, Nat.add_right_comm, Nat.add_assoc, Nat.add_left_comm] using yes
    | true =>
      left
      apply mem_map.mpr
      refine ⟨w,ih (i+1) h (fun p b s e => ?_), rfl⟩
      have yes := opens (true::p) b s (by simp [e])
      simpa [List.count_cons, Nat.add_right_comm, Nat.add_assoc, Nat.add_left_comm] using yes

/-- A prefix below the chord to a buffered endpoint leaves both children
inside the cone. A unit of vertical buffer suffices at each endpoint. -/
theorem chord_split {α K I H i h : ℝ} (a : 0 ≤ α) (N : 0 < I+H)
    (t0 : 0 ≤ i+h) (tN : i+h ≤ I+H)
    (base : 1 ≤ α*K) (endpoint : H+1 ≤ α*(K+I))
    (chord : (I+H)*h ≤ H*(i+h)) : h+1 ≤ α*(K+i) := by
  have h1 := mul_nonneg (sub_nonneg.mpr base) (sub_nonneg.mpr tN)
  have h2 := mul_nonneg (sub_nonneg.mpr endpoint) t0
  have h3 := mul_le_mul_of_nonneg_left chord (show 0≤1+α by linarith)
  apply le_of_mul_le_mul_left (a:=I+H) _ N
  nlinarith only [h1,h2,h3]

/-- Cutting after a maximum partial sum puts every prefix of a zero-total
word below its chord. The cut is an index strictly below the word length. -/
theorem rotate_below {β : Type*} (score : List β → ℤ) (empty : score []=0)
    (add : ∀ p q, score (p++q)=score p+score q) (w : List β)
    (pos : 0<w.length) (total : score w=0) :
    ∃ j<w.length, ∀ t : ℕ, score ((w.rotate j).take t) ≤ 0 := by
  obtain ⟨j,hj,maximum⟩ := (range w.length).exists_max_image
    (fun j => score (w.take j)) ⟨0,mem_range.mpr pos⟩
  have jm := mem_range.mp hj
  have all (t : ℕ) : score (w.take t) ≤ score (w.take j) := by
    by_cases h : t<w.length
    · exact maximum t (mem_range.mpr h)
    · rw [List.take_of_length_le (by omega),total]
      simpa [empty] using maximum 0 (mem_range.mpr pos)
  refine ⟨j,jm,fun t => ?_⟩
  rw [List.rotate_eq_drop_append_take jm.le]
  by_cases ht : t ≤ (w.drop j).length
  · rw [List.take_append_of_le_length ht]
    have joined := add (w.take j) ((w.drop j).take t)
    rw [← List.take_add] at joined
    linarith only [joined,all (j+t)]
  · rw [List.take_append, List.take_of_length_le (by omega),add,List.take_take]
    have closure := add (w.take j) (w.drop j)
    rw [List.take_append_drop,total] at closure
    linarith only [closure,all (min (t-(w.drop j).length) j)]

/-- Counting cuts keeps the same factor for periodic words. -/
theorem rotation_cover {β : Type*} (S T : Finset (List β)) (N : ℕ)
    (cover : ∀ w∈S, ∃ j<N, w.rotate j ∈ T) : S.card ≤ N*T.card := by
  classical
  choose j cap good using fun w : ↥S => cover w.val w.property
  let key (w : ↥S) : Fin N × ↥T := (⟨j w, cap w⟩, ⟨w.val.rotate (j w), good w⟩)
  have inj : Function.Injective key := by
    intro a b same
    have index : j a=j b := congrArg (fun u : Fin N × ↥T => u.1.val) same
    have word : a.val.rotate (j a)=b.val.rotate (j b) := congrArg
      (fun u : Fin N × ↥T => u.2.val) same
    rw [index] at word
    exact Subtype.ext (List.rotate_injective _ word)
  simpa using Fintype.card_le_of_injective key inj

private theorem counts (w : List Bool) : w.count true+w.count false=w.length := by
  induction w with
  | nil => simp
  | cons b w ih => cases b <;> simp <;> omega

/-- At least a fraction 1/(I+H) of the words at a buffered endpoint
comes from the common pruned tree. The set S may be any family with
the indicated endpoint; periodic words require no extra hypothesis. -/
theorem endpoint_fraction (α : ℝ) (K I H : ℕ) (S : Finset (List Bool))
    (nonneg : 0 ≤ α) (pos : 0 < I+H) (root : 1 ≤ α*K)
    (buffer : (H:ℝ)+1 ≤ α*(K+I))
    (fixed : ∀ w∈S, w.length=I+H ∧ w.count false=H) :
    S.card ≤ (I+H)*((paths (fun i h => (h:ℝ)+1 ≤ α*(K+i)) (I+H) 0 0).filter
      (fun w => w.count false=H)).card := by
  apply rotation_cover
  intro w hw
  obtain ⟨len,vert⟩ := fixed w hw
  let score (p : List Bool) : ℤ := ((I:ℤ)+H)*(p.count false)-(H:ℤ)*p.length
  have app (p q : List Bool) : score (p++q)=score p+score q := by
    simp [score,List.count_append]; ring
  have zero : score w=0 := by dsimp [score]; rw [vert,len]; push_cast; ring
  obtain ⟨j,hj,under⟩ := rotate_below score (by simp [score]) app w (len ▸ pos) zero
  refine ⟨j,len ▸ hj,Finset.mem_filter.mpr ⟨?_,((w.rotate_perm j).count_eq false).trans vert⟩⟩
  rw [←len,←List.length_rotate w j]
  apply mem_paths_of_prefix
  intro p b s split
  simp only [Nat.zero_add]
  have below := under p.length
  rw [split,List.take_append_length] at below
  have pmax : p.length ≤ I+H := by
    have eq := congrArg List.length split
    simp only [List.length_rotate,len,List.length_append,List.length_cons] at eq
    omega
  have hz : ((I:ℤ)+H)*(p.count false) ≤ (H:ℤ)*p.length := sub_nonpos.mp below
  have chord : ((I:ℝ)+H)*(p.count false) ≤ (H:ℝ)*((p.count true:ℝ)+p.count false) := by
    rw [←Nat.cast_add (p.count true) (p.count false),counts]
    exact_mod_cast hz
  apply chord_split nonneg (by exact_mod_cast pos) (by positivity) _ root buffer chord
  exact_mod_cast (counts p).le.trans pmax

private def fixedWords : ℕ → ℕ → Finset (List Bool)
  | 0, h => if h=0 then {[]} else ∅
  | n+1, 0 => (fixedWords n 0).map (prepend true)
  | n+1, h+1 => (fixedWords n (h+1)).map (prepend true) ∪
                   (fixedWords n h).map (prepend false)

private theorem fixed_card (n h : ℕ) : (fixedWords n h).card=n.choose h := by
  induction n generalizing h with
  | zero => cases h <;> simp [fixedWords]
  | succ n ih =>
    cases h with
    | zero => simp [fixedWords,ih]
    | succ h =>
      rw [fixedWords,card_union_of_disjoint (separate _ _),card_map,card_map,ih,ih,
        Nat.choose_succ_succ,Nat.add_comm]

private theorem fixed_mem {n h : ℕ} {w : List Bool} (hw : w∈fixedWords n h) :
    w.length=n ∧ w.count false=h := by
  induction n generalizing w h with
  | zero =>
    cases h <;> simp [fixedWords] at hw
    subst w; simp
  | succ n ih =>
    cases h with
    | zero =>
      obtain ⟨p,hp,rfl⟩ := mem_map.mp hw
      simp [ih hp]
    | succ h =>
      rcases mem_union.mp hw with l | r
      · obtain ⟨p,hp,rfl⟩ := mem_map.mp l
        simp [ih hp]
      · obtain ⟨p,hp,rfl⟩ := mem_map.mp r
        simp [ih hp]

/-- Binomial-coefficient form of the buffered endpoint estimate. -/
theorem binomial_fraction (α : ℝ) (K I H : ℕ)
    (nonneg : 0 ≤ α) (pos : 0 < I+H) (root : 1 ≤ α*K)
    (buffer : (H:ℝ)+1 ≤ α*(K+I)) :
    (I+H).choose H ≤ (I+H)*((paths (fun i h => (h:ℝ)+1 ≤ α*(K+i)) (I+H) 0 0).filter
      (fun w => w.count false=H)).card := by
  rw [←fixed_card]
  exact endpoint_fraction α K I H _ nonneg pos root buffer (fun _ h => fixed_mem h)

private theorem leaf_state (expand valid : ℕ → ℕ → Prop)
    (children : ∀ i h, valid i h → expand i h → valid (i+1) h ∧ valid i (h+1))
    {n i h : ℕ} {w : List Bool} (node : valid i h) (atLeaf : w∈paths expand n i h) :
    w.length=n ∧ valid (i+w.count true) (h+w.count false) := by
  classical
  induction n generalizing i h w with
  | zero =>
    simp [paths] at atLeaf
    subst w; simpa using node
  | succ n ih =>
    by_cases e : expand i h
    · rw [paths,if_pos e,mem_union] at atLeaf
      rcases atLeaf with l | r
      · obtain ⟨p,hp,rfl⟩ := mem_map.mp l
        obtain ⟨len,v⟩ := ih (children i h node e).1 hp
        simp [len, Nat.add_left_comm, Nat.add_comm] at v ⊢
        exact v
      · obtain ⟨p,hp,rfl⟩ := mem_map.mp r
        obtain ⟨len,v⟩ := ih (children i h node e).2 hp
        simp [len, Nat.add_left_comm, Nat.add_comm] at v ⊢
        exact v
    · simp [paths,e] at atLeaf

/-- Simultaneous weighted Bernstein estimate, restricted to any chosen
buffered endpoints. Only finitely many node signs are used. -/
theorem weighted_credit (F : ℕ → ℕ → ℝ) (α : ℝ) (K N : ℕ) (S : Finset ℕ)
    (nonneg : 0 ≤ α) (pos : 0 < N) (root : 1 ≤ α*K)
    (split : ∀ i h, F (i+1) h+F i (h+1)=F i h)
    (sign : ∀ i h, i+h ≤ N → (h:ℝ) ≤ α*(K+i) → 0 ≤ F i h)
    (buffered : ∀ h∈S, h ≤ N ∧ (h:ℝ)+1 ≤ α*(K+(N-h:ℕ))) :
    ∑ h∈S, (N.choose h:ℝ)*F (N-h) h ≤ (N:ℝ)*F 0 0 := by
  classical
  let expand (i h : ℕ) := (h:ℝ)+1 ≤ α*(K+i)
  let valid (i h : ℕ) := (h:ℝ) ≤ α*(K+i)
  let W := paths expand N 0 0
  let mass (w : List Bool) := F (w.count true) (w.count false)
  have start : valid 0 0 := by dsimp [valid]; push_cast; linarith
  have children (i h : ℕ) (_ : valid i h) (e : expand i h) :
      valid (i+1) h ∧ valid i (h+1) := by
    dsimp [valid,expand] at e ⊢
    push_cast
    constructor <;> nlinarith only [e,nonneg]
  have state (w) (hw : w∈W) : w.length=N ∧ valid (w.count true) (w.count false) := by
    simpa using leaf_state expand valid children start hw
  have budget : ∑ w∈W, mass w ≤ F 0 0 := by
    simpa [W,mass] using credit F expand valid N (fun i h _ _ => split i h) children
      sign (n:=N) (i:=0) (h:=0) (by omega) start
  have entry (h) (hh : h∈S) : (N.choose h:ℝ)*F (N-h) h ≤
      (N:ℝ)*∑ w∈W.filter (fun w => w.count false=h), mass w := by
    obtain ⟨hle,buf⟩ := buffered h hh
    have num := binomial_fraction α K (N-h) h nonneg (by omega) root buf
    rw [Nat.sub_add_cancel hle] at num
    change N.choose h ≤ N*(W.filter (fun w => w.count false=h)).card at num
    have sgn := sign (N-h) h (by omega) (by linarith)
    have const : ∑ w∈W.filter (fun w => w.count false=h), mass w =
        (((W.filter (fun w => w.count false=h)).card:ℝ)*F (N-h) h) := by
      trans ∑ _w∈W.filter (fun w => w.count false=h), F (N-h) h
      · apply sum_congr rfl
        intro w hw
        obtain ⟨wmem,eq⟩ := mem_filter.mp hw
        have len := (state w wmem).1
        have sum := counts w
        change F _ _=_
        rw [eq,show w.count true=N-h by omega]
      · simp
    rw [const,←mul_assoc]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast num) sgn
  have before := sum_le_sum entry
  rw [←mul_sum, sum_fiberwise_eq_sum_filter] at before
  have part : ∑ w∈W.filter (fun w => w.count false∈S), mass w ≤ ∑ w∈W, mass w := by
    apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    intro w hw _
    obtain ⟨len,good⟩ := state w hw
    exact sign _ _ (by rw [counts,len]) good
  exact before.trans (mul_le_mul_of_nonneg_left (part.trans budget) (by positivity))

/-- Direct specialization to signed forward differences of any real sequence. -/
theorem weighted_differences (u : ℕ → ℝ) (α : ℝ) (K N : ℕ) (S : Finset ℕ)
    (nonneg : 0 ≤ α) (pos : 0<N) (root : 1 ≤ α*K)
    (sign : ∀ i h, i+h ≤ N → (h:ℝ) ≤ α*(K+i) → 0 ≤ Erdos142Bernstein.diff u h (K+i))
    (buffered : ∀ h∈S, h ≤ N ∧ (h:ℝ)+1 ≤ α*(K+(N-h:ℕ))) :
    ∑ h∈S, (N.choose h:ℝ)*Erdos142Bernstein.diff u h (K+(N-h)) ≤ (N:ℝ)*u K := by
  apply weighted_credit (fun i h => Erdos142Bernstein.diff u h (K+i)) α K N S
    nonneg pos root _ sign buffered
  intro i h
  rw [Erdos142Bernstein.diff, Nat.add_assoc K i 1]
  ring

#print axioms weighted_differences
#print axioms weighted_credit
#print axioms binomial_fraction
#print axioms endpoint_fraction
#print axioms rotate_below
#print axioms rotation_cover
#print axioms credit
#print axioms mem_paths_of_prefix
#print axioms chord_split
end Erdos142ConePaths
