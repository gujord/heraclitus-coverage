import UniversalTransition

set_option autoImplicit false

namespace G06
open G01 G03 G05

noncomputable def nextDistance (D : Nat → Prop) (unbounded : G02.Unbounded D) (q : Nat) : Nat :=
  Classical.choose (least_nat (fun d => q<d ∧ D d) (unbounded q))

theorem nextDistance_spec (D : Nat → Prop) (unbounded : G02.Unbounded D) (q : Nat) :
    q < nextDistance D unbounded q ∧ D (nextDistance D unbounded q) ∧
    ∀ d, q<d → d<nextDistance D unbounded q → ¬D d := by
  have spec := Classical.choose_spec (least_nat (fun d => q<d ∧ D d) (unbounded q))
  refine ⟨spec.1.1, spec.1.2, ?_⟩
  intro d lower upper member
  have least := spec.2 d ⟨lower, member⟩
  change nextDistance D unbounded q ≤ d at least
  omega

noncomputable def scales (D : Nat → Prop) (unbounded : G02.Unbounded D) : Nat → Nat
  | 0 => 2
  | j+1 => nextDistance D unbounded (scales D unbounded j)

theorem scales_growth (D : Nat → Prop) (unbounded : G02.Unbounded D) (j : Nat) :
    j+2 ≤ scales D unbounded j := by
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih =>
    have step := (nextDistance_spec D unbounded (scales D unbounded j)).1
    change j+1+2 ≤ nextDistance D unbounded (scales D unbounded j)
    omega

theorem scales_member {D : Nat → Prop} (two : D 2) (unbounded : G02.Unbounded D) (j : Nat) :
    D (scales D unbounded j) := by
  cases j with
  | zero => exact two
  | succ j => exact (nextDistance_spec D unbounded (scales D unbounded j)).2.1

theorem every_distance {D : Nat → Prop} (unbounded : G02.Unbounded D) (d : Nat)
    (large : 2 ≤ d) (member : D d) : ∃ j, scales D unbounded j=d := by
  have existsAbove : ∃ j, d ≤ scales D unbounded j := by
    have grow := scales_growth D unbounded d
    exact ⟨d, by omega⟩
  obtain ⟨j, above, least⟩ := least_nat (fun j => d ≤ scales D unbounded j) existsAbove
  refine ⟨j, ?_⟩
  cases j with
  | zero => change d ≤ 2 at above; change 2=d; omega
  | succ j =>
    have below : scales D unbounded j < d := by
      by_cases h : scales D unbounded j < d
      · exact h
      · have impossible := least j (by omega); omega
    have spec := nextDistance_spec D unbounded (scales D unbounded j)
    change d ≤ nextDistance D unbounded (scales D unbounded j) at above
    change nextDistance D unbounded (scales D unbounded j)=d
    by_cases eq : nextDistance D unbounded (scales D unbounded j)=d
    · exact eq
    · exact False.elim (spec.2.2 d below (by omega) member)

theorem initial_checkpoint {D : Nat → Prop} {a : Nat → Int}
    (one : D 1) (two : D 2) (rule : G02.Rule D a) :
    Box 2 (history a 2) ∧ Ends 2 (history a 2) := by
  let t := visit (visit zeroState 1) (-1)
  have path : Reaches D zeroState t := .cons (initial_positive one) (.cons (second_negative two) (.refl _))
  have full : Box 2 t := by
    intro z
    change ((z=0 ∨ z=1) ∨ z= -1) ↔ _
    omega
  have eq := reached_box rule.2 0 2 (history_zero a rule.1).symm path full
  exact ⟨eq ▸ full, eq ▸ Or.inr (Or.inr (Or.inr (show t.current= -(2/2 : Nat) from rfl)))⟩

theorem scale_checkpoints {D : Nat → Prop} {a : Nat → Int}
    (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) (rule : G02.Rule D a) (j : Nat) :
    Box (scales D unbounded j) (history a (scales D unbounded j)) ∧
    Ends (scales D unbounded j) (history a (scales D unbounded j)) := by
  induction j with
  | zero => exact initial_checkpoint one two rule
  | succ j ih =>
    have grow := scales_growth D unbounded j
    have spec := nextDistance_spec D unbounded (scales D unbounded j)
    obtain ⟨t, path, full, endpoint⟩ := G06.transition (history a (scales D unbounded j)) one two
      (by omega) spec.1 (scales_member two unbounded j) spec.2.1 spec.2.2 ih.1 ih.2
    have eq := reached_box rule.2 (scales D unbounded j) (scales D unbounded (j+1)) rfl path full
    exact ⟨eq ▸ full, eq ▸ endpoint⟩

def Checkpoints (D : Nat → Prop) (a : Nat → Int) : Prop :=
  ∀ d, 2 ≤ d → D d → Box d (history a d) ∧ Ends d (history a d)

theorem all_checkpoints {D : Nat → Prop} {a : Nat → Int}
    (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) (rule : G02.Rule D a) :
    G06.Checkpoints D a := by
  intro d large member
  obtain ⟨j, eq⟩ := every_distance unbounded d large member
  simpa only [eq] using scale_checkpoints one two unbounded rule j

theorem unbounded_coverage {D : Nat → Prop} {a : Nat → Int}
    (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) (rule : G02.Rule D a) : Coverage a := by
  intro z
  have grow := scales_growth D unbounded (2*z.natAbs)
  have hz := Int.natAbs_eq z
  have used := ((scale_checkpoints one two unbounded rule (2*z.natAbs)).1 z).mpr ⟨by omega, by omega⟩
  obtain ⟨i, _, eq⟩ := used
  exact ⟨i, eq, fun j same => walk_injective rule.2 j i (same.trans eq.symm)⟩

theorem unbounded_exists (D : Nat → Prop) (one : D 1) (two : D 2) (unbounded : G02.Unbounded D) :
    ∃ a, G02.Rule D a ∧ G06.Checkpoints D a ∧ Coverage a := by
  obtain ⟨a, rule⟩ := G02.unbounded_exists D unbounded
  exact ⟨a, rule, all_checkpoints one two unbounded rule, unbounded_coverage one two unbounded rule⟩

end G06
