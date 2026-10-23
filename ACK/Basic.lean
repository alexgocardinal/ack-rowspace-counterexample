import Mathlib

open scoped BigOperators

namespace ACK

def IsBoolean {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∀ j, x j = 0 ∨ x j = 1

def InRealRowSpace {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) : Prop :=
  ∃ coefficients : Fin n → ℝ,
    ∀ j, x j = ∑ i, coefficients i * A i j

def IsSimpleAdjacency {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, A i i = 0) ∧
  (∀ i j, A i j = A j i) ∧
  (∀ i j, A i j = 0 ∨ A i j = 1)

def Conjecture : Prop :=
  ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ),
    IsSimpleAdjacency A →
    (∃ i j, A i j = 1) →
    ∃ x : Fin n → ℝ,
      IsBoolean x ∧
      x ≠ 0 ∧
      InRealRowSpace A x ∧
      (∀ i, x ≠ A i)

def IsCounterexample {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  IsSimpleAdjacency A ∧
  (∃ i j, A i j = 1) ∧
  (∀ x : Fin n → ℝ,
    IsBoolean x →
    InRealRowSpace A x →
    x = 0 ∨ ∃ i, x = A i)

theorem counterexample_refutes {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (h : IsCounterexample A) :
    ¬ Conjecture := by
  intro hc
  rcases hc n A h.1 h.2.1 with
    ⟨x, hBoolean, hNonzero, hRowSpace, hNew⟩
  rcases h.2.2 x hBoolean hRowSpace with hZero | ⟨i, hEqual⟩
  · exact hNonzero hZero
  · exact hNew i hEqual

end ACK

#print axioms ACK.counterexample_refutes

namespace ACK

theorem rowspace_reconstruction
    {n r : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin r → Fin n)
    (R : Matrix (Fin r) (Fin n) ℝ)
    (hA : ∀ i j,
      A i j = ∑ k : Fin r, A i (p k) * R k j)
    {x : Fin n → ℝ}
    (hx : InRealRowSpace A x) :
    ∀ j, x j = ∑ k : Fin r, x (p k) * R k j := by
  rcases hx with ⟨coefficients, hcoefficients⟩
  intro j
  calc
    x j = ∑ i : Fin n, coefficients i * A i j :=
      hcoefficients j
    _ = ∑ i : Fin n, ∑ k : Fin r,
        (coefficients i * A i (p k)) * R k j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hA i j, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact (mul_assoc _ _ _).symm
    _ = ∑ k : Fin r, ∑ i : Fin n,
        (coefficients i * A i (p k)) * R k j := by
      rw [Finset.sum_comm]
    _ = ∑ k : Fin r, x (p k) * R k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.sum_mul, ← hcoefficients (p k)]

end ACK

#print axioms ACK.rowspace_reconstruction
