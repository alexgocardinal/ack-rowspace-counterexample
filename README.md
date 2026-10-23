# Counterexamples to the Akbari–Cameron–Khosrovshahi adjacency-row-space conjecture

Lean 4 formalizations of three counterexamples to the conjecture that every
finite simple graph containing an edge has a nonzero {0,1}-vector in the
real row space of its adjacency matrix that is not an adjacency row.

For each of the three explicit 52-vertex graphs, Lean proves that every
{0,1}-vector in the real adjacency row space is either zero or an
adjacency row. Each graph therefore refutes the conjecture.

## Authors

- Alex Chan — Harvard University and NBER
- Kurt Sweat — UT Southwestern Medical Center
- Yetong Xu — Harvard Business School

Corresponding author: Alex Chan, achan@hbs.edu.

## Verification

Install Lean through [elan](https://github.com/leanprover/elan).
From the repository directory, run:

```sh
lake exe cache get
lake build
lake env lean Verification.lean
```

The Lean toolchain and Mathlib revision are pinned in `lean-toolchain`,
`lakefile.toml`, and `lake-manifest.json`.

The final counterexample theorems are:

- `ACK.Witness550.isCounterexample`
- `ACK.Witness563.isCounterexample`
- `ACK.Witness570.isCounterexample`

Each namespace also contains `conjecture_false : ¬ ACK.Conjecture`.

The reported axiom dependencies of these six theorems are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
They do not depend on `sorryAx` or `Lean.ofReduceBool`.

## Proof organization

- `ACK/Basic.lean`: the conjecture, counterexample predicate, and general
  row-space reconstruction theorem.
- `ACK/Witness*.lean`: explicit adjacency matrices and simple-graph checks.
- `ACK/Certificate*.lean`: exact integer reconstruction certificates.
- `ACK/Reconstruction*.lean`: reconstruction over the real numbers.
- `ACK/Classification*.lean`: certified classification of all 16,384
  Boolean prefixes.
- `ACK/Bridge*.lean`: connection between integer certificates and real
  row-space vectors.
- `ACK/Encoding*.lean`: completeness of the binary-prefix encoding.
- `ACK/Counterexample*.lean`: assembled counterexample and refutation proofs.
- `Verification.lean`: statement inspection and final axiom reports.

The certificates are embedded in Lean source and checked by Lean.
No external solver or Python installation is required to verify the proofs.
