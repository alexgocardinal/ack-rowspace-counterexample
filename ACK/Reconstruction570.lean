import ACK.Certificate570

open scoped BigOperators

namespace ACK.Witness570

theorem cast_integerAdjacency (i j : Fin 52) :
    (integerAdjacency i j : ℝ) = adjacency i j := by
  simp [integerAdjacency, adjacency]

noncomputable def reconstructionBasis (k : Fin 14) (j : Fin 52) : ℝ :=
  (scaledBasis k j : ℝ) / 3

theorem real_scaled_reconstruction (i j : Fin 52) :
    (3 : ℝ) * adjacency i j =
      ∑ k : Fin 14,
        adjacency i (pivotIndex k) * (scaledBasis k j : ℝ) := by
  have h :
      (3 : ℝ) * (integerAdjacency i j : ℝ) =
        ∑ k : Fin 14,
          (integerAdjacency i (pivotIndex k) : ℝ) *
            (scaledBasis k j : ℝ) := by
    exact_mod_cast (integer_reconstruction i j)
  simpa only [cast_integerAdjacency] using h

theorem adjacency_reconstruction (i j : Fin 52) :
    adjacency i j =
      ∑ k : Fin 14,
        adjacency i (pivotIndex k) * reconstructionBasis k j := by
  calc
    adjacency i j = ((3 : ℝ) * adjacency i j) / 3 := by
      ring
    _ = (∑ k : Fin 14,
          adjacency i (pivotIndex k) *
            (scaledBasis k j : ℝ)) / 3 := by
      rw [real_scaled_reconstruction i j]
    _ = ∑ k : Fin 14,
          adjacency i (pivotIndex k) * reconstructionBasis k j := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      simp only [reconstructionBasis]
      ring

theorem every_rowspace_vector_reconstructs
    {x : Fin 52 → ℝ}
    (hx : ACK.InRealRowSpace adjacency x) :
    ∀ j, x j =
      ∑ k : Fin 14,
        x (pivotIndex k) * reconstructionBasis k j := by
  exact ACK.rowspace_reconstruction
    adjacency pivotIndex reconstructionBasis adjacency_reconstruction hx

end ACK.Witness570

#print axioms ACK.Witness570.every_rowspace_vector_reconstructs
