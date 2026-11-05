# Lean coverage proofs

This directory contains the complete proof dependencies for the accompanying
paper. Its two main theorems concern unbounded distance sets containing 1 and 2,
and complete residue tails with joint gcd 1. It also includes the quantitative
odd-tail bound and the results in Appendices A–C. Each statement retains its
own hypotheses; the general gcd-1 question and prime coverage remain open.

## Reproduce

Install the official Lean 4.35.0 toolchain with its bundled standard library.
Then run from the package root, supplying the actual Lean executable or an
elan proxy that selects this version:

```sh
python3 scripts/verify_lean.py --lean /path/to/lean --output build/lean
```

The pin in [lean-toolchain](lean-toolchain) identifies the required version.
No Mathlib or compiled project objects are needed. The runner rebuilds all
44 modules, audits 296 theorems and checks 40 intended mathematical
rejections. Choose a new output directory for each run. The full command
logs and `run.json` are written there. See
[reproduction instructions](../docs/reproducibility.md) and
[verification scope](../docs/verification.md).

## Review the statements

Start with [UniversalLiteral.lean](UniversalLiteral.lean) for Theorem A and
[ResidueCoverage.lean](ResidueCoverage.lean) for Theorem B. Their coverage and
existence declarations are identified in the
[statement-to-proof guide](../docs/REVIEW_GUIDE.md), alongside every numbered
result and appendix. Follow the imports to inspect the rule and hypotheses.

[proof-manifest.json](proof-manifest.json) records the module order, proof
source hashes, expected transitive axiom sets and negative fixtures.
`PaperAudit.lean` checks the retained theorem declarations. The files in
`negative/` deliberately assert false propositions and are supposed to fail;
they are regression tests, not additional theorem sources.

Only `propext`, `Classical.choice` and `Quot.sound` are permitted as transitive
axioms. The compiler/kernel and bundled standard library remain trusted.
Original declaration bodies are preserved and their compiled types were
compared with the accepted research sources; imports were narrowed to this
paper's dependencies. [Provenance](../docs/provenance.md) explains that selection.
Kernel checking does not establish historical priority or replace comparison
of the formal statements with the paper. Independent human review remains open.
