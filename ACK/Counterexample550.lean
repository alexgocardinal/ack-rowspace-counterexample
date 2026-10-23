import ACK.Encoding550

namespace ACK.Witness550

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem rowPrefixBits :
    ∀ (i : Fin 52) (k : Fin 14),
      ((rowMasks.getD i.val 0) % 16384).testBit k.val =
        edge i (pivotIndex k) := by
  decide

theorem zero_in_rowspace :
    ACK.InRealRowSpace adjacency (0 : Fin 52 → ℝ) := by
  refine ⟨fun _ => 0, ?_⟩
  intro j
  simp

theorem adjacency_row_in_rowspace (i : Fin 52) :
    ACK.InRealRowSpace adjacency (adjacency i) := by
  classical
  refine ⟨fun t => if t = i then 1 else 0, ?_⟩
  intro j
  simp [ite_mul]

theorem boolean_rowspace_classification
    (x : Fin 52 → ℝ)
    (hBoolean : ACK.IsBoolean x)
    (hx : ACK.InRealRowSpace adjacency x) :
    x = 0 ∨ ∃ i, x = adjacency i := by
  classical
  let b : Fin 14 → Bool :=
    fun k => decide (x (pivotIndex k) = 1)

  have hp : ∀ k : Fin 14,
      x (pivotIndex k) =
        if (booleanPrefixCode b).testBit k.val then 1 else 0 := by
    intro k
    rw [booleanPrefixCode_correct]
    rcases hBoolean (pivotIndex k) with h0 | h1
    · simp [b, h0]
    · simp [b, h1]

  obtain ⟨lo, hi, hm⟩ := booleanPrefixCode_split b
  have hc := finite_classification lo hi
  dsimp only [ClassificationCheck] at hc

  by_cases hz : classificationCode lo hi = 0
  · have hsum : lo.val + 128 * hi.val = 0 := by
      simpa [hz] using hc
    have hm0 : booleanPrefixCode b = 0 := hm.trans hsum
    left
    apply rowspace_vector_unique hx zero_in_rowspace
    intro k
    simpa [hm0] using hp k

  · by_cases hle : classificationCode lo hi ≤ 52
    · have hsum :
          lo.val + 128 * hi.val =
            (rowMasks.getD (classificationCode lo hi - 1) 0) %
              16384 := by
        simpa [hz, hle] using hc
      have hmrow :
          booleanPrefixCode b =
            (rowMasks.getD (classificationCode lo hi - 1) 0) %
              16384 :=
        hm.trans hsum

      let i : Fin 52 :=
        ⟨classificationCode lo hi - 1, by omega⟩

      right
      refine ⟨i, ?_⟩
      apply rowspace_vector_unique hx (adjacency_row_in_rowspace i)
      intro k
      have hbits :
          (booleanPrefixCode b).testBit k.val =
            edge i (pivotIndex k) := by
        rw [hmrow]
        exact rowPrefixBits i k
      simpa only [hbits, adjacency] using hp k

    · have hbad :
          classificationCode lo hi ≤ 104 ∧
            integerExtension (lo.val + 128 * hi.val)
              (classificationCode lo hi - 53) ≠ 0 ∧
            integerExtension (lo.val + 128 * hi.val)
              (classificationCode lo hi - 53) ≠ 3 := by
        simpa only [if_neg hz, if_neg hle] using hc

      let j : Fin 52 :=
        ⟨classificationCode lo hi - 53, by omega⟩

      have hv :=
        integerExtension_matches_vector hx (booleanPrefixCode b) hp j

      have he :
          (integerExtension (lo.val + 128 * hi.val)
            (classificationCode lo hi - 53) : ℝ) = 3 * x j := by
        simpa only [hm] using hv

      exfalso
      rcases hBoolean j with hj | hj
      · apply hbad.2.1
        have hcast :
            (integerExtension (lo.val + 128 * hi.val)
              (classificationCode lo hi - 53) : ℝ) = 0 := by
          rw [he, hj]
          norm_num
        exact_mod_cast hcast
      · apply hbad.2.2
        have hcast :
            (integerExtension (lo.val + 128 * hi.val)
              (classificationCode lo hi - 53) : ℝ) = 3 := by
          rw [he, hj]
          norm_num
        exact_mod_cast hcast

theorem isCounterexample :
    ACK.IsCounterexample adjacency := by
  exact ⟨isSimple, hasEdge, boolean_rowspace_classification⟩

theorem conjecture_false : ¬ ACK.Conjecture :=
  ACK.counterexample_refutes adjacency isCounterexample

end ACK.Witness550

#print axioms ACK.Witness550.isCounterexample
#print axioms ACK.Witness550.conjecture_false
