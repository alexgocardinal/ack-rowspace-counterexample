import ACK.Basic

namespace ACK.Witness550

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rowMasks : List Nat := [
  2235677450899378, 4469100081065161, 141699841692688, 1319826628482962,
  2579589578957037, 4130315476566737, 1057000981728818, 996040442109755,
  1302392307939977, 906028198430185, 3357941915654863, 3431541563733443,
  4434330260606348, 4502500115745042, 1178676469170560, 371649086116,
  4407569272047065, 3106118882592237, 4112585889679122, 3105569200211951,
  4501433890376076, 4157076465126020, 854340600417067, 4502871764831158,
  1055563107273736, 933855412358434, 2234239576444296, 35734176829633,
  2579632603861455, 35184494449347, 18004589942018, 1320376310863248,
  141150159312402, 2969643597338195, 4148320066508755, 531064385378322,
  3359557823404115, 529998160009356, 3358491598035149, 408290465094054,
  3413536973791425, 3519502638654480, 17961565037600, 1319783603578544,
  4095151569136137, 4373843239071547, 2252865094562883, 2597594168899055,
  3554687133103827, 53146059486947, 346365569104171, 549025950415922
]

theorem rowMasks_length : rowMasks.length = 52 := by
  decide

def edge (i j : Fin 52) : Bool :=
  (rowMasks.getD i.val 0).testBit j.val

def adjacency : Matrix (Fin 52) (Fin 52) ℝ :=
  fun i j => if edge i j then 1 else 0

theorem edge_irrefl :
    ∀ i : Fin 52, edge i i = false := by
  decide

theorem edge_symm :
    ∀ i j : Fin 52, edge i j = edge j i := by
  decide

theorem isSimple : ACK.IsSimpleAdjacency adjacency := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    simp [adjacency, edge_irrefl i]
  · intro i j
    simp only [adjacency, edge_symm i j]
  · intro i j
    cases h : edge i j <;> simp [adjacency, h]

theorem hasEdge :
    ∃ i j : Fin 52, adjacency i j = 1 := by
  refine ⟨0, 1, ?_⟩
  have h : edge (0 : Fin 52) (1 : Fin 52) = true := by
    decide
  simp [adjacency, h]

end ACK.Witness550

#print axioms ACK.Witness550.isSimple
#print axioms ACK.Witness550.hasEdge
