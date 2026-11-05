import TripleGlobal

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace G07
open G01 G02

def seed : State := ⟨-8, fun z => z= -8 ∨ (0≤z ∧ z≤8)⟩

def inwardPrefix : List Int := [-2,-1,-4,-3,-6,-5]

def blockedState : State := finish seed inwardPrefix

theorem inward_certificate : Certificate reference seed inwardPrefix := by
  simp [inwardPrefix, Certificate, FiniteGreedy, seed, visit, Allowed, Preferred,
    reference, candidates, List.range_succ]

theorem blocked_used (z : Int) : blockedState.used z ↔ -8≤z ∧ z≤8 ∧ z≠ -7 := by
  simp only [blockedState, inwardPrefix, finish, visit, seed]
  omega

theorem blocked_no_interior (v : Int) (unused : ¬blockedState.used v)
    (inside : v.natAbs≤8) : ¬Allowed reference blockedState.current v := by
  have hv := Int.natAbs_eq v
  have absent : ¬(-8≤v ∧ v≤8 ∧ v≠ -7) := fun h => unused ((blocked_used v).mpr h)
  have eq : v= -7 := by omega
  subst v
  simp [blockedState, inwardPrefix, finish, visit, Allowed, reference]

theorem reaches_used {D : Nat → Prop} {s t : State} (path : Reaches D s t) (z : Int) : s.used z → t.used z := by
  induction path with
  | refl => exact fun h => h
  | cons _ _ ih => exact fun h => ih (Or.inl h)

theorem blocked_no_completion : ¬∃ t, Reaches reference blockedState t ∧ Complete 8 t := by
  rintro ⟨t, path, full⟩
  cases path with
  | refl =>
    have used := (full (-7)).mpr (by decide)
    have impossible := (blocked_used (-7)).mp used
    omega
  | @cons _ t v choice rest =>
    have used : t.used v := reaches_used rest v (Or.inr rfl)
    exact blocked_no_interior v choice.1 ((full v).mp used) choice.2.1

theorem finish_preserves_used (vs : List Int) (s : State) (z : Int) : s.used z → (finish s vs).used z := by
  induction vs generalizing s with
  | nil => exact fun h => h
  | cons v vs ih => exact fun h => ih (visit s v) (Or.inl h)

theorem certificate_prevents_completion {D : Nat → Prop} (vs : List Int) (s : State) (B : Nat) (z : Int)
    (cert : Certificate D s vs) (bound : z.natAbs≤B) (missing : ¬(finish s vs).used z)
    (failure : ¬∃ t, Reaches D (finish s vs) t ∧ Complete B t) :
    ¬∃ t, Reaches D s t ∧ Complete B t := by
  induction vs generalizing s with
  | nil => exact failure
  | cons v vs ih =>
    have next := ih (visit s v) cert.2 missing failure
    rintro ⟨t, path, full⟩
    cases path with
    | refl => exact missing (finish_preserves_used (v::vs) s z ((full z).mpr bound))
    | @cons _ t w choice rest =>
      have eq := greedy_unique choice (finite_greedy_sound cert.1)
      subst w
      exact next ⟨t, rest, full⟩

theorem local_filling_impossible : ¬∃ t, Reaches reference seed t ∧ Complete 8 t := by
  apply certificate_prevents_completion inwardPrefix seed 8 (-7) inward_certificate (by decide)
  · have absent : ¬blockedState.used (-7) := by rw [blocked_used]; omega
    exact absent
  · exact blocked_no_completion

theorem same_rule_global_coverage : ∃ a, G06.LiteralRule reference a ∧ Checkpoints a ∧ Coverage a :=
  literal_exists reference reference_family

end G07
