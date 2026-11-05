import TripleBlocks

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace G07
open G01 G02

def initialPrefix : List Int := [1,2,-1,-2,-3,3]

theorem initial_certificate {D : Nat → Prop} (family : Family D) : Certificate D zeroState initialPrefix := by
  have one := family.1
  have three := family.2.1
  have no2 := family.2.2.1
  have no5 := family.2.2.2.1
  have six : D 6 := by simpa using family.2.2.2.2.1 0
  simp [initialPrefix, Certificate, FiniteGreedy, zeroState, visit, Allowed, Preferred,
    candidates, List.range_succ, one, three, no2, no5, six]

theorem initial_history {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : Rule D a) :
    history a 6=finish zeroState initialPrefix := by
  simpa [initialPrefix] using certificate_from_zero rule initialPrefix (initial_certificate family)

theorem initial_box {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : Rule D a) :
    Interval (-3) 3 (history a 6) ∧ a 6=3 := by
  have state := initial_history family rule
  constructor
  · rw [state]
    intro z
    simp only [initialPrefix, finish, visit, zeroState]
    omega
  · have current := congrArg State.current state
    simpa only [history, initialPrefix, finish, visit] using current

def Checkpoints (a : Nat → Int) : Prop :=
  (∀ j, Interval (-((3+2*j : Nat) : Int)) ((3+2*j : Nat) : Int) (history a (6+4*j))) ∧
  a 6=3 ∧ ∀ j, a (10+4*j)= -((4+2*j : Nat) : Int)

theorem family_blocks {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : Rule D a) (j : Nat) :
    Interval (-((3+2*j : Nat) : Int)) ((3+2*j : Nat) : Int) (history a (6+4*j)) ∧
    (a (6+4*j)=((3+2*j : Nat) : Int) ∨ a (6+4*j)=1-((3+2*j : Nat) : Int)) := by
  induction j with
  | zero =>
    have first := initial_box family rule
    exact ⟨first.1, Or.inl first.2⟩
  | succ j ih =>
    have previous : D (2*(3+2*j)) := by
      have eq : 2*(3+2*j)=6+4*j := by omega
      simpa only [eq] using family.2.2.2.2.1 j
    have next : D (2*(3+2*j)+4) := by
      have eq : 2*(3+2*j)+4=6+4*(j+1) := by omega
      simpa only [eq] using family.2.2.2.2.1 (j+1)
    have no2 : ¬D (2*(3+2*j)+2) := by
      have eq : 2*(3+2*j)+2=8+4*j := by omega
      simpa only [eq] using family.2.2.2.2.2.1 j
    have no3 : ¬D (2*(3+2*j)+3) := by
      have eq : 2*(3+2*j)+3=9+4*j := by omega
      simpa only [eq] using family.2.2.2.2.2.2 j
    have cert := block_certificate (history a (6+4*j)) family.1 previous next no2 no3 (by omega) ih.1 ih.2
    have state := certificate_history rule (block (3+2*j)) (6+4*j) (history a (6+4*j)) rfl cert
    have full := block_finish ih.1
    have index : 6+4*j+(block (3+2*j)).length=6+4*(j+1) := by simp only [block, List.length_cons, List.length_nil]; omega
    rw [index] at state
    have rad : 3+2*j+2=3+2*(j+1) := by omega
    refine ⟨?_, Or.inr ?_⟩
    · simpa only [←state, rad] using full.1
    · have last := full.2
      rw [←state] at last
      change a (6+4*(j+1))=1-((3+2*j+2 : Nat) : Int) at last
      simpa only [rad] using last

theorem family_checkpoints {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : Rule D a) : Checkpoints a := by
  refine ⟨fun j => (family_blocks family rule j).1, (initial_box family rule).2, ?_⟩
  intro j
  have previous := family_blocks family rule j
  have hcore : D (2*(3+2*j)) := by
    have eq : 2*(3+2*j)=6+4*j := by omega
    simpa only [eq] using family.2.2.2.2.1 j
  have next : D (2*(3+2*j)+4) := by
    have eq : 2*(3+2*j)+4=6+4*(j+1) := by omega
    simpa only [eq] using family.2.2.2.2.1 (j+1)
  have no2 : ¬D (2*(3+2*j)+2) := by
    have eq : 2*(3+2*j)+2=8+4*j := by omega
    simpa only [eq] using family.2.2.2.2.2.1 j
  have no3 : ¬D (2*(3+2*j)+3) := by
    have eq : 2*(3+2*j)+3=9+4*j := by omega
    simpa only [eq] using family.2.2.2.2.2.2 j
  have cert := block_certificate (history a (6+4*j)) family.1 hcore next no2 no3 (by omega) previous.1 previous.2
  have state := certificate_history rule (block (3+2*j)) (6+4*j) (history a (6+4*j)) rfl cert
  have last := congrArg State.current state
  simp only [history, block, finish, visit, List.length_cons, List.length_nil] at last
  have index : 6+4*j+4=10+4*j := by omega
  rw [index] at last
  omega

theorem family_coverage {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : Rule D a) : Coverage a := by
  intro z
  have hz := Int.natAbs_eq z
  have used := ((family_blocks family rule z.natAbs).1 z).mpr ⟨by omega, by omega⟩
  obtain ⟨i, _, eq⟩ := used
  exact ⟨i, eq, fun j same => walk_injective rule.2 j i (same.trans eq.symm)⟩

theorem family_unbounded {D : Nat → Prop} (family : Family D) : Unbounded D := by
  intro N
  exact ⟨6+4*N, by omega, family.2.2.2.2.1 N⟩

theorem literal_checkpoints {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : G06.LiteralRule D a) : Checkpoints a :=
  family_checkpoints family ((G06.literal_iff D a).mp rule)

theorem literal_coverage {D : Nat → Prop} {a : Nat → Int} (family : Family D) (rule : G06.LiteralRule D a) : Coverage a :=
  family_coverage family ((G06.literal_iff D a).mp rule)

theorem literal_exists (D : Nat → Prop) (family : Family D) :
    ∃ a, G06.LiteralRule D a ∧ Checkpoints a ∧ Coverage a := by
  obtain ⟨a, rule⟩ := G02.unbounded_exists D (family_unbounded family)
  exact ⟨a, (G06.literal_iff D a).mpr rule, family_checkpoints family rule, family_coverage family rule⟩

def reference (d : Nat) : Prop := d=1 ∨ d=3 ∨ (6≤d ∧ d%4=2)

theorem reference_family : Family reference := by
  constructor
  · unfold reference; decide
  constructor
  · unfold reference; decide
  constructor
  · unfold reference; decide
  constructor
  · unfold reference; decide
  constructor
  · intro j; unfold reference; omega
  constructor
  · intro j; unfold reference; omega
  · intro j; unfold reference; omega

def optional (P : Nat → Prop) (d : Nat) : Prop :=
  reference d ∨ ((d=4 ∨ (7≤d ∧ d%4=3)) ∧ P d)

theorem optional_family (P : Nat → Prop) : Family (optional P) := by
  refine ⟨Or.inl reference_family.1, Or.inl reference_family.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · unfold optional reference; omega
  · unfold optional reference; omega
  · intro j; exact Or.inl (reference_family.2.2.2.2.1 j)
  · intro j; unfold optional reference; omega
  · intro j; unfold optional reference; omega

theorem optional_result (P : Nat → Prop) :
    ∃ a, G06.LiteralRule (optional P) a ∧ Checkpoints a ∧ Coverage a :=
  literal_exists (optional P) (optional_family P)

end G07
