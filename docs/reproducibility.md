# Reproduction

Extract the source ZIP and run commands from its root. Use Python >=3.9
without `-O`, `-OO` or `PYTHONOPTIMIZE`. No Python packages are required.

```sh
python3 scripts/check_release.py
python3 scripts/check_entrance.py
python3 scripts/test_release.py
```

The first checks the exact distribution inventory and source/receipt bindings.
The second checks all 72 Appendix C moves, exact states at times 64, 68 and
72, and rejection of three damaged prefixes. This is a finite check only.
The third checks rejection of missing, altered and unsafe package contents.
These Python commands do not compile Lean. See the
[verification scope](verification.md) for the limits of each check.

## Combined Lean build

Install the official `leanprover/lean4:v4.35.0` toolchain (for example through
[elan](https://github.com/leanprover/elan)); the proofs require only bundled
Std. Run with the actual Lean binary or an elan Lean proxy selecting this
version. The package does not install software automatically.

```sh
python3 scripts/verify_lean.py --lean /path/to/lean --output build/lean
```

Choose a new output directory for every run. All 44 modules are rebuilt with
warnings as errors and an isolated project import directory. All 296 retained
theorems are audited against the accepted transitive axiom sets; only
`propext`, `Classical.choice` and `Quot.sound` are allowed. Each of the 40
negative fixtures must fail for the intended false-proposition reason, not
because of missing imports or malformed syntax. Logs and `run.json` are
written under the chosen build directory, with failures retained as failures.
The compiler and its bundled compiled standard library remain trusted.

`formal/proof-manifest.json` gives the topological module order, full fixture
inventory, expected axiom sets and selected proof-source hashes. Original
statement/proof bodies are preserved;
`EXPORT_PROVENANCE.json` records their source identities and extraction. All
retained declaration types were compared with the accepted original environment.
The final package's fresh combined receipt is `evidence/combined/run.json`.
A fresh run's elapsed time and binary/object hashes may depend on the machine;
source identities, theorem statements and allowed axioms must agree.

## Rebuild the PDF

Install pdfLaTeX with the usual AMS packages, Latin Modern, microtype, xurl,
hyperref and fancyhdr, plus Poppler's `pdftotext` and `pdftoppm`.

```sh
python3 scripts/build_paper.py --output build/paper
```

The command runs three TeX passes, checks the log and exports search text.
Render the resulting PDF and inspect every page; successful compilation is
not a visual review. A rebuilt PDF may differ in bytes due to TeX versions
or metadata. Preserve the original release when validating its inventory.

No check here constitutes independent human mathematical review or establishes
priority. Python finite checks are not Lean axioms.
