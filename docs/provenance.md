# Provenance

This is a paper-specific distribution of Roger Gujord's Heraclitus research.
It follows the separate base-seven packaging model: explicit selection,
source mapping, fresh reproduction after extraction and an exact inventory.
Private research history, discarded investigations and unrelated prime cases
are excluded.

The separate [verification scope](verification.md) describes what each check
establishes; this note records source selection and the history of the evidence.

## Selection of the proof sources

The inclusion boundary is the paper's statements and Appendices A–C, the
residue examples, and tests of their hypotheses. Required definitions and
lemmas are retained. Earlier separate Fibonacci, powers-of-two and
squares-plus-2 constructions and their case-specific tests are excluded;
the general theorem covers the relevant examples in the paper.

Each retained declaration body (statement and proof) is copied verbatim from
an accepted research source. Imports are narrowed and unused declarations
are removed, so whole-file hashes differ from the original research files.
`EXPORT_PROVENANCE.json` maps source files, original hashes, declaration
names and body hashes. The research originals were not modified. Internal
case namespaces preserve declaration identity; they are not extra claims.

The 402 selected declarations include 296 named theorems, each checked for
its transitive axioms in `PaperAudit.lean`. The compiled types of every
selected declaration are compared with the original accepted environment.
The fresh build, not a source-selection heuristic, establishes that the
extracted proof library compiles and retains the audited assumptions.

Forty negative fixtures test the retained article families. Thirty-two
fixtures specific to excluded earlier branches are omitted; none was removed
because it failed an intended check. These fixtures deliberately assert false
propositions and must be rejected for the specified mathematical reason.
They are regression checks, not additional coverage proofs.

## Evidence

`evidence/combined/` contains one fresh combined run and all its command logs.
The five earlier case receipts remain in the research archive; their hashes
and dates are recorded in the provenance map, not presented as new runs.
The final export requires matching proof inputs, runner, intended rejections
and review of the exact PDF/source pair. Integrity checks establish byte
identity, not mathematical validity.

AI agents contributed exploration, proof drafts, exposition and formalization
under Roger Gujord's direction. The human author is responsible for the
manuscript. Machine checking and AI reviews are not independent human review;
human review and historical priority remain open. No comparative claim about
AI research performance is made.
