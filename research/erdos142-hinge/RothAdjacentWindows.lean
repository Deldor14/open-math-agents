import RothClusterWindows

open Finset Erdos142DyadicClusters
namespace Erdos142HalfScale

private def halfTable : Finset (Finset ℕ × List (Finset ℕ)) :=
  {
  ({0},[{0},∅,{2},{2}]),
  ({0,1},[{0,1},{1},{2},{2,3}]),
  ({0,2},[{0,2},{2},{2},{2}]),
  ({0,4},[{0,2},∅,{2,4},{2,4}]),
  ({0,1,5},[{0,1,3},{1,3},{2},{2,3,5}]),
  ({0,4,5},[{0,2,3},{3},{2,4},{2,4,5}]),
  ({0,4,5,9},[{0,2,3,5},{3,5},{2,4},{2,4,5,7}])}

theorem half_windows : halfTable.image Prod.fst = shapes ∧
    ∀ r ∈ halfTable, (∀ h ∈ range 4, Fits r.1 (r.2.getD h ∅) 1 2 3 h) ∧
      5*r.1.card ≤ 2*((r.2.getD 0 ∅).card+(r.2.getD 1 ∅).card+
        (r.2.getD 2 ∅).card+(r.2.getD 3 ∅).card) := by decide

private def twiceTable : Finset (Finset ℕ × List (Finset ℕ)) :=
  {
  ({0},[{0,2},{2,4}]),
  ({0,1},[{0,2,3,5},{2,3,5,6}]),
  ({0,2},[{0,2,6,8},{2,4,8,10}]),
  ({0,4},[{0,2,8,10},{2,4,10,12}]),
  ({0,1,5},[{0,2,3,5,11,13},{2,3,5,6,11,13}]),
  ({0,4,5},[{0,2,8,10,11,13},{2,4,10,11,13,14}]),
  ({0,4,5,9},[{0,2,8,10,11,13,19,21},{2,4,10,11,13,14,19,21}])}

theorem twice_windows : twiceTable.image Prod.fst = shapes ∧
    ∀ r ∈ twiceTable, (∀ h ∈ range 2, Fits r.1 (r.2.getD h ∅) 2 1 6 h) ∧
      4*r.1.card ≤ (r.2.getD 0 ∅).card+(r.2.getD 1 ∅).card := by decide

#print axioms half_windows
#print axioms twice_windows
end Erdos142HalfScale
