import ACK.Classification550

open scoped BigOperators

namespace ACK.Witness550

theorem rowspace_vector_unique
    {x y : Fin 52 → ℝ}
    (hx : ACK.InRealRowSpace adjacency x)
    (hy : ACK.InRealRowSpace adjacency y)
    (h : ∀ k : Fin 14, x (pivotIndex k) = y (pivotIndex k)) :
    x = y := by
  funext j
  rw [every_rowspace_vector_reconstructs hx j,
      every_rowspace_vector_reconstructs hy j]
  apply Finset.sum_congr rfl
  intro k _
  rw [h k]

theorem integerExtension_cast (m : Nat) (j : Fin 52) :
    (integerExtension m j.val : ℝ) =
      ∑ k : Fin 14,
        if m.testBit k.val then (scaledBasis k j : ℝ) else 0 := by
  simp only [integerExtension, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  change
    ((if m.testBit k.val then scaledBasis k j else 0 : ℤ) : ℝ) =
      (if m.testBit k.val then (scaledBasis k j : ℝ) else 0)
  cases h : m.testBit k.val <;> simp [h]

theorem integerExtension_matches_vector
    {x : Fin 52 → ℝ}
    (hx : ACK.InRealRowSpace adjacency x)
    (m : Nat)
    (hp : ∀ k : Fin 14,
      x (pivotIndex k) = if m.testBit k.val then 1 else 0)
    (j : Fin 52) :
    (integerExtension m j.val : ℝ) = 3 * x j := by
  calc
    (integerExtension m j.val : ℝ) =
        ∑ k : Fin 14,
          if m.testBit k.val then (scaledBasis k j : ℝ) else 0 :=
      integerExtension_cast m j
    _ = ∑ k : Fin 14,
          x (pivotIndex k) * (scaledBasis k j : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hp k]
      cases h : m.testBit k.val <;> simp [h]
    _ = 3 * (∑ k : Fin 14,
          x (pivotIndex k) * reconstructionBasis k j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      unfold reconstructionBasis
      ring
    _ = 3 * x j := by
      rw [← every_rowspace_vector_reconstructs hx j]

end ACK.Witness550

#print axioms ACK.Witness550.rowspace_vector_unique
#print axioms ACK.Witness550.integerExtension_matches_vector
