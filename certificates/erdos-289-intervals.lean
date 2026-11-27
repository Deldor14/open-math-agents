import Mathlib

/-! Casi particolari del problema 289 di Erdős. Ogni intervallo contiene
almeno due interi positivi. Due intervalli distinti sono sempre separati da
almeno un intero omesso. Le somme sono calcolate esattamente in ℚ. -/
namespace Deldor14.Erdos289

def Witness (k : ℕ) (a b : Fin k → ℕ) : Prop :=
  (∀ i, 1 ≤ a i ∧ a i < b i) ∧
  (∀ i j, i ≠ j → b i + 1 < a j ∨ b j + 1 < a i) ∧
  ∑ i, ∑ n ∈ Finset.Icc (a i) (b i), (1 / (n : ℚ)) = 1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_7 : Witness 7 ![6,10,15,20,26,54,143] ![7,12,16,22,27,56,144] := by
  unfold Witness
  decide +kernel

#print axioms example_7

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_8 : Witness 8 ![6,20,25,39,54,65,90,99] ![9,22,28,40,55,66,91,100] := by
  unfold Witness
  decide +kernel

#print axioms example_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_9 : Witness 9 ![5,14,17,20,27,33,44,54,84] ![6,15,18,22,28,34,45,55,85] := by
  unfold Witness
  decide +kernel

#print axioms example_9

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_10 : Witness 10 ![8,17,23,32,55,69,76,84,95,114] ![12,18,24,35,57,70,77,85,96,115] := by
  unfold Witness
  decide +kernel

#print axioms example_10

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_11 : Witness 11 ![6,16,23,27,34,51,68,84,115,135,144] ![8,17,24,30,35,52,70,85,117,136,145] := by
  unfold Witness
  decide +kernel

#print axioms example_11

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_12 : Witness 12 ![7,13,16,21,29,33,39,44,55,84,116,144] ![8,14,18,22,30,34,40,45,56,85,117,145] := by
  unfold Witness
  decide +kernel

#print axioms example_12

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_13 : Witness 13 ![10,16,20,29,35,39,51,55,69,114,143,204,246] ![12,17,24,30,36,41,52,56,70,117,145,205,247] := by
  unfold Witness
  decide +kernel

#print axioms example_13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_14 : Witness 14 ![8,15,23,29,44,54,65,69,77,90,99,104,115,143] ![10,16,27,30,45,55,66,70,78,91,100,105,116,145] := by
  unfold Witness
  decide +kernel

#print axioms example_14

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_15 : Witness 15 ![7,20,32,45,49,68,98,175,195,207,220,224,230,252,275] ![10,24,33,46,50,70,100,176,196,208,221,225,231,253,276] := by
  unfold Witness
  decide +kernel

#print axioms example_15

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_16 : Witness 16 ![7,12,18,32,51,68,95,114,143,147,170,184,195,221,252,272] ![10,13,19,33,52,69,96,115,144,148,171,185,196,222,253,273] := by
  unfold Witness
  decide +kernel

#print axioms example_16

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_17 : Witness 17 ![10,16,20,24,33,40,48,54,75,98,132,140,187,195,204,234,246] ![12,18,21,25,34,42,50,55,76,100,133,141,189,196,205,235,247] := by
  unfold Witness
  decide +kernel

#print axioms example_17

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_18 : Witness 18 ![10,14,20,25,29,39,44,51,54,98,116,144,153,170,189,204,220,245] ![11,16,22,26,30,41,45,52,55,100,117,145,154,171,190,205,221,246] := by
  unfold Witness
  decide +kernel

#print axioms example_18

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_19 : Witness 19 ![9,19,32,39,50,65,68,84,87,98,114,135,144,175,189,204,224,245,260] ![10,26,33,41,51,66,70,85,88,100,115,136,145,176,190,205,225,246,261] := by
  unfold Witness
  decide +kernel

#print axioms example_19

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_20 : Witness 20 ![10,16,20,24,38,51,56,76,84,90,99,143,147,153,185,195,209,221,247,279] ![12,18,21,25,40,52,57,78,85,91,100,144,148,156,187,196,210,222,248,280] := by
  unfold Witness
  decide +kernel

#print axioms example_20

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_21 : Witness 21 ![10,17,24,28,33,39,51,62,65,68,84,91,99,115,135,140,143,154,188,207,234] ![12,18,25,30,34,40,52,63,66,69,85,93,100,116,136,141,145,155,189,208,235] := by
  unfold Witness
  decide +kernel

#print axioms example_21

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_22 : Witness 22 ![15,20,23,27,32,56,80,104,114,119,135,140,144,147,161,184,188,195,207,221,224,234] ![18,21,25,30,35,57,81,105,116,120,136,141,145,148,162,185,190,196,210,222,225,235] := by
  unfold Witness
  decide +kernel

#print axioms example_22

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_23 : Witness 23 ![11,18,24,27,31,35,39,45,51,80,92,104,119,132,140,153,161,188,207,216,220,224,234] ![13,19,25,28,33,36,40,46,52,81,93,105,120,133,141,154,162,189,210,217,221,225,235] := by
  unfold Witness
  decide +kernel

#print axioms example_23

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_24 : Witness 24 ![13,16,24,27,34,38,41,57,76,84,91,98,104,116,135,143,161,204,215,231,245,275,300,322] ![14,19,25,28,35,39,43,58,77,87,92,99,105,117,136,144,162,205,216,232,246,276,301,324] := by
  unfold Witness
  decide +kernel

#print axioms example_24

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_25 : Witness 25 ![8,14,20,34,41,46,53,62,85,114,123,143,164,208,220,224,234,264,272,279,300,328,344,351,424] ![10,15,21,36,42,47,54,63,86,115,124,144,165,210,221,225,235,266,273,280,301,330,345,352,425] := by
  unfold Witness
  decide +kernel

#print axioms example_25

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_26 : Witness 26 ![5,20,32,35,41,45,52,65,92,95,105,170,176,185,204,212,220,246,285,294,354,371,390,407,413,495] ![6,22,33,37,42,46,53,66,93,96,106,171,177,186,205,213,222,247,286,295,355,372,392,408,414,497] := by
  unfold Witness
  decide +kernel

#print axioms example_26

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_27 : Witness 27 ![15,24,27,30,34,38,47,50,56,75,84,90,104,114,147,152,170,184,195,204,216,221,224,234,246,287,328] ![18,25,28,31,36,40,48,51,57,76,85,93,105,115,148,153,171,185,196,205,217,222,225,235,247,288,329] := by
  unfold Witness
  decide +kernel

#print axioms example_27

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_28 : Witness 28 ![9,15,20,25,37,44,55,62,87,114,117,135,144,147,153,175,184,195,207,224,247,259,275,295,341,351,399,413] ![10,16,22,27,38,45,56,63,88,115,118,136,145,148,156,176,185,196,208,225,248,261,276,297,342,352,400,414] := by
  unfold Witness
  decide +kernel

#print axioms example_28

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_29 : Witness 29 ![18,22,25,34,50,54,62,65,69,77,80,84,87,90,95,99,114,119,140,143,153,161,170,175,188,203,224,230,234] ![19,23,29,35,52,56,63,66,70,78,81,85,88,93,96,100,116,120,141,144,155,162,171,176,189,204,225,231,235] := by
  unfold Witness
  decide +kernel

#print axioms example_29

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_30 : Witness 30 ![19,22,25,28,34,50,55,62,65,69,77,80,84,87,90,95,99,114,119,140,143,153,161,170,175,188,203,224,230,234] ![20,23,26,30,36,52,56,63,66,70,78,81,85,88,93,96,100,116,120,141,144,155,162,171,176,189,204,225,231,235] := by
  unfold Witness
  decide +kernel

#print axioms example_30

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_31 : Witness 31 ![12,17,26,30,36,40,60,68,75,81,116,122,128,182,186,204,208,215,221,246,258,300,304,350,369,377,384,405,450,459,475] ![13,19,28,32,37,43,61,70,76,82,117,123,129,183,187,205,210,216,222,248,259,301,305,351,370,378,385,406,451,460,476] := by
  unfold Witness
  decide +kernel

#print axioms example_31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_32 : Witness 32 ![13,22,27,32,41,48,51,56,62,68,77,93,114,140,143,160,186,195,208,216,231,246,265,272,287,328,341,351,368,376,423,440] ![14,24,30,33,42,49,53,58,63,69,78,95,117,141,144,161,187,196,209,217,232,248,266,273,288,329,342,352,369,378,424,442] := by
  unfold Witness
  decide +kernel

#print axioms example_32

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem example_33 : Witness 33 ![9,18,28,46,52,60,77,90,115,122,143,154,164,170,175,182,186,189,203,234,245,252,264,287,304,319,368,376,423,434,440,464,475] ![10,21,29,48,54,64,78,92,116,124,144,155,165,171,176,184,187,190,205,235,246,253,266,288,306,320,369,377,425,435,442,465,476] := by
  unfold Witness
  decide +kernel

#print axioms example_33

theorem all_7_to_33 (k : ℕ) (lo : 7 ≤ k) (hi : k ≤ 33) :
    ∃ a b : Fin k → ℕ, Witness k a b := by
  interval_cases k
  · exact ⟨_,_,example_7⟩
  · exact ⟨_,_,example_8⟩
  · exact ⟨_,_,example_9⟩
  · exact ⟨_,_,example_10⟩
  · exact ⟨_,_,example_11⟩
  · exact ⟨_,_,example_12⟩
  · exact ⟨_,_,example_13⟩
  · exact ⟨_,_,example_14⟩
  · exact ⟨_,_,example_15⟩
  · exact ⟨_,_,example_16⟩
  · exact ⟨_,_,example_17⟩
  · exact ⟨_,_,example_18⟩
  · exact ⟨_,_,example_19⟩
  · exact ⟨_,_,example_20⟩
  · exact ⟨_,_,example_21⟩
  · exact ⟨_,_,example_22⟩
  · exact ⟨_,_,example_23⟩
  · exact ⟨_,_,example_24⟩
  · exact ⟨_,_,example_25⟩
  · exact ⟨_,_,example_26⟩
  · exact ⟨_,_,example_27⟩
  · exact ⟨_,_,example_28⟩
  · exact ⟨_,_,example_29⟩
  · exact ⟨_,_,example_30⟩
  · exact ⟨_,_,example_31⟩
  · exact ⟨_,_,example_32⟩
  · exact ⟨_,_,example_33⟩

#print axioms all_7_to_33

end Deldor14.Erdos289
