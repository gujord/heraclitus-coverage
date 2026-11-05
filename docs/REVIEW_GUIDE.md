# Proof and statement guide

The paper and this package use a fixed allowed-distance set, start at zero,
choose an unused destination of least absolute value, and prefer positive
values in ties. Coverage means every integer is visited exactly once.
Theorem A requires unbounded distances including 1 and 2; Theorem B requires
complete residue tails with joint gcd 1. Neither settles the prime walk.

The table uses stable LaTeX labels. Internal case IDs identify source
namespaces only. Read the complete definitions and imported hypotheses with
each declaration. Kernel acceptance, fidelity to the paper, originality and
independent human mathematical review are separate questions.

| Article label | Formal source and declarations | Point to check |
| --- | --- | --- |
| `thm:main` | [UniversalLiteral.lean](../formal/UniversalLiteral.lean): `G06.literal_checkpoints`, `G06.literal_coverage`, `G06.literal_exists` | Arbitrary predicate D, unboundedness, distances 1 and 2, all allowed checkpoints d ≥ 2. |
| `lem:finite-priority` | [ResidueOmission.lean](../formal/ResidueOmission.lean): `G18.missing_avoids` | An infinite literal walk and a permanently missing target; eventually no allowed distance to that target. Equal-magnitude positive ties are included. |
| `lem:fill` | [OneSide.lean](../formal/OneSide.lean): `G01.one_side_filling` | Either sign, strict interior and arbitrary exterior occupancy; the empty-hole case is separate. |
| `lem:transition` | [UniversalTransition.lean](../formal/UniversalTransition.lean): `G06.transition`, `G06.adjacent_transition`, `G06.separated_transition` | Both adjacent and separated consecutive allowed distances; four possible endpoint states. |
| `cor:completion` | [UniversalLiteral.lean](../formal/UniversalLiteral.lean): `G06.completion_coverage`, `G06.completion_exists` | Adding 1 and 2 to any unbounded set. |
| `thm:residue-tail` | [ResidueCoverage.lean](../formal/ResidueCoverage.lean): `G18.literal_coverage`, `G18.literal_exists` | q > 0, nonempty canonical finite list, gcd including q equals 1, all required positive distances beyond M. |
| `prop:odd-tail` | [CofiniteGlobal.lean](../formal/CofiniteGlobal.lean): `G10.literal_coverage`, `G10.literal_exists`; [CofiniteResults.lean](../formal/CofiniteResults.lean): `G10.literal_first_visit_unique`, `G10.literal_unique` | Full odd tail, arbitrary other distances, exact index bound and uniqueness. |
| `prop:many-holes` | [EntranceGlobal.lean](../formal/EntranceGlobal.lean): `G08E.actual_entrance`, `G08E.exact_entrance`; [EntranceResults.lean](../formal/EntranceResults.lean): `G08E.actual_hole_enumeration`, `G08E.actual_hole_count`, `G08E.no_uniform_hole_bound` | Actual zero-start histories for all k ≥ 1, not just auxiliary states or a finite census. |
| `prop:lane-fill` | [LaneLiteral.lean](../formal/LaneLiteral.lean): `G08.conditional_lane_filling`, `G08.literal_walk_lane` | The exact single-lane entrance is a hypothesis; 2 is the only positive even distance. |
| `thm:triple` | [TripleGlobal.lean](../formal/TripleGlobal.lean): `G07.literal_checkpoints`, `G07.literal_coverage`, `G07.literal_exists`, `G07.optional_result` | Required and forbidden distances; arbitrary optional subset in the stated family. |
| `prop:triple-obstruction` | [TripleObstruction.lean](../formal/TripleObstruction.lean): `G07.local_filling_impossible`, `G07.same_rule_global_coverage` | Failure of a local auxiliary-state interface does not imply failure of global coverage. |
| `rem:moving-hole` | [RepairGlobal.lean](../formal/RepairGlobal.lean): `G09.literal_exists`, `G09.literal_checkpoints`, `G09.literal_repairs`, `G09.literal_repair_bound`, `G09.literal_coverage` | Exact states at 72+4j and immediate repair; the finite entrance and full transition proof are checked in Lean and printed in Appendix C. |
| `thm:repair` | [RepairGlobal.lean](../formal/RepairGlobal.lean): `G09.literal_exists`, `G09.literal_checkpoints`, `G09.literal_repairs`, `G09.literal_repair_bound`, `G09.literal_coverage` | Exact states at 72+4j and immediate repair; the finite entrance and full transition proof are checked in Lean and printed in Appendix C. |

The finite set S in Theorem B is represented by a finite list in Lean;
the gcd condition is `S.foldl Nat.gcd q = 1`. Enumerating S gives that list,
and repetition does not alter its gcd. Equal-magnitude positive ties matter.

Appendix C prints all 72 initial destinations. `RepairEntrance.lean` proves
`G09.entrance_certificate`, `G09.entrance_history` and `G09.entrance_frontier`.
The separate Python entrance check verifies this finite list directly from
the rule. It is not a premise of the Lean coverage theorem.

The lane-hole example limits a particular count across a family; every
member still has coverage. Local transition hypotheses are not automatic
claims about every zero-start history. The open prime-repair discussion is
not an additional formal theorem or a dependency of this package.

See [reproduction](reproducibility.md), [provenance](provenance.md) and
[prior work](prior-work.md). Independent human review and priority remain open.
