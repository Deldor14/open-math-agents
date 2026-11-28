import RothDyadicClusters

open Finset
namespace Erdos142DyadicClusters

def oneShapes : Finset (Finset ℕ) :=
  {{0},{0,1},{0,2},{0,1,3},{0,2,3},{0,2,3,5}}

def weakOne (S : Finset ℕ) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
    (x+z=y+y ∨ x+z=y+y+2 ∨ x+z+2=y+y) → x=y ∨ y=z ∨ x=z

instance (S : Finset ℕ) : Decidable (weakOne S) := by unfold weakOne; infer_instance

/-- Checked one-defect component extension table on the half-step grid. -/
theorem single_extension : ∀ C ∈ oneShapes, ∀ j ∈ range 8,
    (∃ i ∈ C, i+1=j ∨ j+1=i ∨ i+2=j ∨ j+2=i) →
    weakOne (insert j C) → insert j C ∈ oneShapes := by decide

def compressTable : Finset (Finset ℕ × List (Finset ℕ)) :=
  {
  ({0},[{0,2},{2},{2},{2},{2},{2},{2},{2},{2},{2,4}]),
  ({0,1},[{0,1,3},{1,2},{2,3},{2,3},{2,3},{2,3},{2,3},{2,3},{2,3},{2,3}]),
  ({0,2},[{0,2},{2,4},{2,4},{2,4},{2,4},{2,4},{2,4},{2,4},{2,4},{2,4}]),
  ({0,4},[{0,2},{2,4},{2,4},{2,4},{2,4},{2,6},{2,6},{2,6},{2,6},{2,4}]),
  ({0,1,5},[{0,2,3,5},{1,2,5},{2,3,5},{2,3,5},{2,3,5},{2,3,5},{2,3,7},{2,3,7},{2,3,7},{2,3,7}]),
  ({0,4,5},[{0,2,5},{2,4,5},{2,4,5},{2,4,5},{2,4,5,7},{2,5,6},{2,6,7},{2,6,7},{2,6,7},{2,4,7}]),
  ({0,4,5,9},[{0,2,5,9},{2,4,5,9},{2,4,5,9},{2,4,5,9},{2,4,5,7},{2,5,6,9},{2,6,7,9},{2,6,7,9},{2,6,7,9},{2,4,7,9}])}

def doubleTable : Finset (Finset ℕ × List (Finset ℕ)) :=
  {
  ({0},[{0,2},{2,4}]),
  ({0,1},[{0,2,3,5},{2,3,5}]),
  ({0,2},[{0,2,6},{2,4,8}]),
  ({0,1,3},[{0,2,3,5,9},{2,3,5,9}]),
  ({0,2,3},[{0,2,6,7,9},{2,4,7,8}]),
  ({0,2,3,5},[{0,2,6,7,9,13},{2,4,7,8,11,13}])}

/-- The selected outputs lie in the indicated half-open tube on their own
    parity classes, and contain no nonconstant arithmetic progression. -/
def Fits (C D : Finset ℕ) (p q w h : ℕ) : Prop :=
  (∀ y ∈ D, ∃ i ∈ C, y%2=i%2 ∧ p*i+h ≤ q*y ∧ q*y < p*i+h+w) ∧
  (∀ x ∈ D, ∀ y ∈ D, ∀ z ∈ D, x+z=y+y → x=z)

instance (C D : Finset ℕ) (p q w h : ℕ) : Decidable (Fits C D p q w h) := by
  unfold Fits
  infer_instance

/-- Every phase of the compression retains the entire component count. -/
theorem compression_windows :
    compressTable.image Prod.fst = shapes ∧
    ∀ row ∈ compressTable, ∀ h ∈ range 10,
      Fits row.1 (row.2.getD h ∅) 4 5 12 h ∧ row.1.card ≤ (row.2.getD h ∅).card := by
  decide

/-- The two phases at dilation two have mean gain at least three halves. -/
theorem double_windows :
    doubleTable.image Prod.fst = oneShapes ∧
    ∀ row ∈ doubleTable, (∀ h ∈ range 2, Fits row.1 (row.2.getD h ∅) 2 1 4 h) ∧
      3*row.1.card ≤ (row.2.getD 0 ∅).card+(row.2.getD 1 ∅).card := by decide

def unitEdge (s a b : ℤ) : Prop := b=a+s ∨ a=b+s

/-- Four alternating edges either close a square on three consecutive edges,
    or their first, third and fifth vertices themselves form a progression. -/
theorem alternating_path (s t a b c d e : ℤ) (ab : unitEdge s a b)
    (bc : unitEdge t b c) (cd : unitEdge s c d) (de : unitEdge t d e) :
    unitEdge t a d ∨ unitEdge s b e ∨ a+e=2*c := by
  unfold unitEdge at *
  omega

#print axioms single_extension
#print axioms compression_windows
#print axioms double_windows
#print axioms alternating_path
end Erdos142DyadicClusters
