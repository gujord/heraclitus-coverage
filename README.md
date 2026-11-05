# Coverage in Heraclitus walks

**Version 1.0.0 — manuscript and reproducible proof package.**

*Interval filling and residue connectivity*, by Roger Gujord.

The paper proves coverage for every unbounded distance set containing 1 and 2,
and for complete residue tails whose representatives together with the
modulus have gcd 1. The paper also gives exact checkpoints, an odd-tail
first-visit bound and covered examples outside the two main criteria.
The package contains the manuscript, complete required Lean sources,
a separate Python check of the printed finite prefix, and reproduction tools.
The work was AI-assisted under Roger Gujord's direction and has not received
independent human mathematical review.

Read the [manuscript](paper/heraclitus-coverage.pdf), then the
[verification scope](docs/verification.md) and
[reproduction instructions](docs/reproducibility.md). The
[proof guide](docs/REVIEW_GUIDE.md) maps the paper's statements to Lean.
Prime coverage and general gcd-1 sufficiency remain open. Historical priority
is unresolved; known antecedents are credited in the paper and
[prior-work note](docs/prior-work.md).

## Exact rule

Start at `a(0)=0`. Fix a set `D` of allowed nonnegative integer distances.
From `a(n)`, choose an unused integer `v` with `|v-a(n)|` in `D`, minimizing
`|v|`; prefer the positive integer in a tie. The same distance can be used
again; `D` is not a prescribed chronological sequence of jumps.

Theorem A assumes that `D` is unbounded and contains 1 and 2. Theorem B assumes
complete tails in residue classes whose representatives, together with the
modulus, have gcd 1. Each theorem proves existence and coverage for its
stated class. See [UniversalLiteral.lean](formal/UniversalLiteral.lean) and
[ResidueCoverage.lean](formal/ResidueCoverage.lean), with their hypotheses
explained in the proof guide.

## Run

Python 3.9 or newer; only the standard library is required for these checks:

```sh
python3 scripts/check_release.py
python3 scripts/check_entrance.py
python3 scripts/test_release.py
```

The first checks distribution integrity and source/receipt bindings. The
second checks the 72-move prefix printed in Appendix C, three exact states
and three damaged-prefix rejections. The third checks that the distribution
validator rejects altered packages. These commands do not compile Lean.

With the pinned Lean 4.35.0 toolchain installed, run separately:

```sh
python3 scripts/verify_lean.py --lean /path/to/lean --output build/lean
```

This builds 44 modules from source, audits 296 theorems and checks
40 intended mathematical rejections. It uses no compiled project objects,
Mathlib, AI service, account or private repository. The initial compiler
installation may require a download. The [Lean guide](formal/README.md)
describes the entry points and trust boundary.
The bundled CI workflow runs **distribution integrity, finite-prefix checks
and distribution rejection tests**; its green status does not represent a
Lean build.

## Package layout

| Directory | Purpose |
| --- | --- |
| `paper/` | PDF, editable LaTeX with bibliography, and generated search text |
| `formal/` | Complete required Lean proof sources, proof manifest and pinned toolchain |
| `formal/negative/` | Forty intended mathematical rejection fixtures |
| `scripts/` | Distribution and finite-prefix checks, rejection tests, Lean runner and PDF builder |
| `docs/` | Verification scope, reproduction, statement review, provenance and bounded prior-work search |
| `evidence/combined/` | Accepted combined proof-build report and command logs |
| `evidence/` | Declaration-type comparison and PDF-review receipt |

The package is self-contained. Private development history, discarded
investigations and unrelated research notes are excluded. Earlier receipt
identities remain in the source map; [provenance](docs/provenance.md)
explains the selected sources and the dated evidence. The same reviewed PDF
and ZIP are intended for GitHub release v1.0.0 and the Zenodo record.

## Citation and licenses

Roger Gujord, *Coverage in Heraclitus walks: interval filling and residue
connectivity*, manuscript and reproducible proof package, version 1.0.0.
Version DOI: [10.5281/zenodo.23973601](https://doi.org/10.5281/zenodo.23973601).
Project repository: [gujord/heraclitus-coverage](https://github.com/gujord/heraclitus-coverage).
The source archive is self-contained and requires no repository access.

**MIT for code; CC BY 4.0 for prose and data**, by component.
See [LICENSE](LICENSE) and [CITATION.cff](CITATION.cff).
`release-manifest.json` inventories all distributed bytes except itself;
`EXPORT_PROVENANCE.json` records the actual source mapping. Integrity checks
establish byte identity, not mathematical validity.
