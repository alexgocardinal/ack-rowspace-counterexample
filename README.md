# Counterexamples to the Akbari–Cameron–Khosrovshahi adjacency-row-space conjecture

Lean 4 formalizations of three counterexamples to the conjecture that every
finite simple graph containing an edge has a nonzero {0,1}-vector in the
real row space of its adjacency matrix that is not an adjacency row.

For each of the three explicit 52-vertex graphs, Lean proves that every
{0,1}-vector in the real adjacency row space is either zero or an
adjacency row. Each graph therefore refutes the conjecture.

## Authors

- Alex Chan — Harvard University and NBER
- Weilin Meng — Harvard Business School
- Kurt Sweat — UT Southwestern Medical Center

Correspondence: achan@hbs.edu.

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

## Paper

[Read the paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7701198)

[![DOI](https://img.shields.io/badge/DOI-10.7910%2FDVN%2FVG7OBC-blue)](https://doi.org/10.7910/DVN/VG7OBC)

## Research archive and citation

A snapshot of this project is deposited in Harvard Dataverse:

https://doi.org/10.7910/DVN/VG7OBC

Please use the citation provided by Harvard Dataverse when citing the
archived work. This GitHub repository contains ongoing development;
the Dataverse record identifies the archived version.
