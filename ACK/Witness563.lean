import ACK.Basic

namespace ACK.Witness563

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rowMasks : List Nat := [
  3796833971441586, 975326376111305, 3382117143155728, 3443816705759122,
  590186053705965, 118938485261009, 3735115157114418, 3878655590195003,
  342540792232585, 906162009605609, 772718156716751, 3588872655091139,
  1969293910609292, 2533206070921490, 61718814327168, 255286422012353,
  263524698309401, 844443195278441, 3638449345135888, 1715269948999084,
  3638430093412114, 1908818304960495, 773783188408332, 1386535501335172,
  904899549203464, 4186757205593406, 3377649266199931, 143521181356811,
  3518445828183298, 3443835957482896, 3637384313444307, 3545733345417638,
  2532160290953683, 465681573009929, 3409385408666294, 3676849706212770,
  70426826907841, 283130218275369, 3453589750031376, 3515308564358544,
  2455080747217347, 3395305047405954, 4108631881889263, 3665247361431097,
  3597110931388187, 3801576046458667, 2551765810919651, 3717465439059072,
  255267170288579, 3382097891431954, 772737408440525, 844210015316173
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

end ACK.Witness563

#print axioms ACK.Witness563.isSimple
#print axioms ACK.Witness563.hasEdge
