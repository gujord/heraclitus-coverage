# Verification scope

The walk starts at zero and uses a fixed set of allowed distances. Each move
chooses an unused integer of least absolute value, preferring the positive
integer in a tie. The paper's coverage theorems retain their stated distance
hypotheses; local transition lemmas also retain their explicit state hypotheses.
Independent human mathematical review and historical priority remain open.

| Layer | What is checked | What it does not establish |
| --- | --- | --- |
| Distribution integrity | Exact inventory, source identities and receipt bindings | Mathematical truth or authorship |
| Python finite prefix | All 72 Appendix C moves, exact states at times 64, 68 and 72, and three damaged-prefix rejections | Coverage at every later index |
| Lean | The stated rule, existence, coverage, checkpoints, first-visit bound and local results under their respective hypotheses | Human review, historical priority or automatic fidelity of the prose |
| Declaration preservation | All 402 retained compiled types match the accepted originals; statement/proof bodies are preserved | A substitute for compiling the selected sources |
| Rejection fixtures | Forty specified false-proposition fixtures are rejected for the intended reason | Exhaustive detection of every possible defect |
| PDF review | The recorded PDF/source pair and page layout | Mathematical correctness |
| GitHub CI | Distribution integrity, finite prefix and distribution rejection tests on Python 3.9 and 3.12 | A Lean build |

## Formal statements and trust

The [statement-to-proof guide](REVIEW_GUIDE.md) maps both main theorems,
the numbered supporting results and Appendices A–C to their Lean declarations.
Read the exact definitions, quantifiers and imported hypotheses with each
statement. Theorem A requires an unbounded distance set containing 1 and 2.
Theorem B requires complete residue tails with joint gcd 1. Neither is a
claim about arbitrary infinite sets of gcd 1 or about the prime-distance walk.

The combined runner compiles 44 modules and audits the transitive axioms of
296 retained theorems. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. The trust boundary includes Lean 4.35.0, its kernel and bundled
standard library, the allowed axioms, and fidelity to the intended problem.
No trajectory sample or Python execution is a premise of the formal theorems.
The independent Python finite-prefix check is not a Lean axiom.

## Evidence and limits

The included combined run finished on 5 November 2026 at 09:12:14 UTC.
Its exact inputs, commands, logs and outcome are in
[`evidence/combined/run.json`](../evidence/combined/run.json). Later prose,
layout or documentation changes do not turn that receipt into a new proof run.
[Provenance](provenance.md) explains extraction and comparison of the proof
sources; [reproduction](reproducibility.md) gives commands for a new run.

The lane-hole example limits a proposed way of counting holes; its entire
family has coverage. The moving-hole example proves coverage despite
repeatedly creating a new boundary hole. Neither is a counterexample to
Sloane's general question. The prime discussion supplies open questions,
not an additional coverage theorem or prime-gap law.

AI tools assisted exploration, proof drafts, exposition and formalization
under Roger Gujord's direction. Roger is the author responsible for the paper.
Machine checking, AI review, historical originality and independent human
review are distinct; the last two remain unresolved.
