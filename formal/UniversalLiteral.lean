import UniversalGlobal

set_option autoImplicit false

namespace G06
open G01

def LiteralRule (D : Nat → Prop) (a : Nat → Int) : Prop :=
  a 0=0 ∧ ∀ n,
    (¬∃ i, i≤n ∧ a i=a (n+1)) ∧ D (a (n+1)-a n).natAbs ∧
    ∀ v, (¬∃ i, i≤n ∧ a i=v) → D (v-a n).natAbs →
      (a (n+1)).natAbs ≤ v.natAbs ∧ ((a (n+1)).natAbs=v.natAbs → v≤a (n+1))

theorem allowed_of_unused {D : Nat → Prop} (a : Nat → Int) (n : Nat) (v : Int)
    (unused : ¬∃ i, i≤n ∧ a i=v) (distance : D (v-a n).natAbs) : Allowed D (a n) v := by
  refine ⟨by simpa only [history, difference_symm (a n) v] using distance, ?_⟩
  have neq : a n ≠ v := fun eq => unused ⟨n, Nat.le_refl _, eq⟩
  have hd := Int.natAbs_eq (a n-v)
  omega

theorem literal_iff (D : Nat → Prop) (a : Nat → Int) : G06.LiteralRule D a ↔ G02.Rule D a := by
  constructor
  · intro literal
    refine ⟨literal.1, ?_⟩
    intro n
    obtain ⟨unused, distance, minimal⟩ := literal.2 n
    refine ⟨unused, allowed_of_unused a n (a (n+1)) unused distance, ?_⟩
    intro v vu vd
    exact minimal v vu (by simpa only [history, difference_symm (a n) v] using vd.1)
  · intro rule
    refine ⟨rule.1, ?_⟩
    intro n
    have choice := rule.2 n
    refine ⟨choice.1, ?_, ?_⟩
    · simpa only [history, difference_symm (a n) (a (n+1))] using choice.2.1.1
    · intro v vu vd
      exact choice.2.2 v vu (allowed_of_unused a n v vu vd)

theorem literal_checkpoints {D : Nat → Prop} {a : Nat → Int}
    (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) (rule : G06.LiteralRule D a) :
    G06.Checkpoints D a := all_checkpoints one two unbounded ((literal_iff D a).mp rule)

theorem literal_coverage {D : Nat → Prop} {a : Nat → Int}
    (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) (rule : G06.LiteralRule D a) : Coverage a :=
  unbounded_coverage one two unbounded ((literal_iff D a).mp rule)

theorem literal_exists (D : Nat → Prop) (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) :
    ∃ a, G06.LiteralRule D a ∧ G06.Checkpoints D a ∧ Coverage a := by
  obtain ⟨a, rule, checkpoints, coverage⟩ := G06.unbounded_exists D one two unbounded
  exact ⟨a, (literal_iff D a).mpr rule, checkpoints, coverage⟩

def complete12 (S : Nat → Prop) (d : Nat) : Prop := d=1 ∨ d=2 ∨ S d

theorem completion_unbounded {S : Nat → Prop} (unbounded : G02.Unbounded S) : G02.Unbounded (complete12 S) := by
  intro N
  obtain ⟨d, large, member⟩ := unbounded N
  exact ⟨d, large, Or.inr (Or.inr member)⟩

theorem completion_coverage {S : Nat → Prop} {a : Nat → Int} (unbounded : G02.Unbounded S)
    (rule : G06.LiteralRule (complete12 S) a) : Coverage a :=
  literal_coverage (Or.inl rfl) (Or.inr (Or.inl rfl)) (completion_unbounded unbounded) rule

theorem completion_exists (S : Nat → Prop) (unbounded : G02.Unbounded S) :
    ∃ a, G06.LiteralRule (complete12 S) a ∧ G06.Checkpoints (complete12 S) a ∧ Coverage a :=
  literal_exists (complete12 S) (Or.inl rfl) (Or.inr (Or.inl rfl)) (completion_unbounded unbounded)

end G06
