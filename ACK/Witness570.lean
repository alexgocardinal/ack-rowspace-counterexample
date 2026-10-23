import ACK.Basic

namespace ACK.Witness570

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rowMasks : List Nat := [
  2248633216880562, 1014337876667593, 1270493202158608, 1342527724410770,
  17629674496237, 1093914424050385, 484896305270322, 3860742361554747,
  218099258735241, 1992418704098793, 2784376796748495, 3948903560394179,
  4494812090731916, 4503591037438226, 443000106778713, 1763736911610240,
  4350184186708461, 3206588452570051, 2131445167949273, 477575130876473,
  2729275623246619, 2176598694628400, 4428299186998546, 4289272723148066,
  1099515864223360, 1345785052598288, 1131466738308128, 1574466845086841,
  3826167337456987, 4477081654728659, 3418459520374822, 3861459627153535,
  1341525255788684, 565736329715905, 2271870229455113, 2308164987773747,
  2922784546726785, 27490911478816, 1791227823089056, 2314483693545510,
  3372103359277261, 4078220605155750, 3371386093678473, 2260458499223619,
  219818992956115, 1697203068024033, 3403336967763241, 3400796905174511,
  5500678665955, 2295033523321379, 2500572890905229, 1917122822487168
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

end ACK.Witness570

#print axioms ACK.Witness570.isSimple
#print axioms ACK.Witness570.hasEdge
