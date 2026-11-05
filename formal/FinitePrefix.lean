import OriginalRule

set_option autoImplicit false

namespace G02
open G01

def candidates (r : Nat) : List Int :=
  (List.range (2*r+1)).map (fun (n : Nat) => (n : Int)-(r : Int))

theorem mem_candidates (r : Nat) (w : Int) (h : w.natAbs ≤ r) :
    w ∈ candidates r := by
  have hw := Int.natAbs_eq w
  have nonneg : 0 ≤ w+(r : Int) := by omega
  have cast := Int.toNat_of_nonneg nonneg
  apply List.mem_map.mpr
  refine ⟨(w+(r : Int)).toNat, ?_, ?_⟩
  · apply List.mem_range.mpr
    omega
  · omega

def FiniteGreedy (D : Nat → Prop) (st : State) (v : Int) : Prop :=
  ¬st.used v ∧ Allowed D st.current v ∧
    ∀ w ∈ candidates v.natAbs, ¬st.used w → Allowed D st.current w → Preferred v w

theorem finite_greedy_sound {D : Nat → Prop} {st : State} {v : Int}
    (h : FiniteGreedy D st v) : Greedy D st v := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro w unused allowed
  by_cases bound : w.natAbs ≤ v.natAbs
  · exact h.2.2 w (mem_candidates v.natAbs w bound) unused allowed
  · constructor
    · omega
    · intro eq; omega

def Certificate (D : Nat → Prop) (st : State) : List Int → Prop
  | [] => True
  | v::vs => FiniteGreedy D st v ∧ Certificate D (visit st v) vs

def finish (st : State) : List Int → State
  | [] => st
  | v::vs => finish (visit st v) vs

def Rule (D : Nat → Prop) (a : Nat → Int) : Prop :=
  a 0 = 0 ∧ ∀ n, Greedy D (history a n) (a (n+1))

theorem certificate_history {D : Nat → Prop} {a : Nat → Int}
    (rule : Rule D a) (vs : List Int) (n : Nat) (st : State)
    (start : history a n = st) (h : Certificate D st vs) :
    history a (n+vs.length) = finish st vs := by
  induction vs generalizing n st with
  | nil => simpa [finish] using start
  | cons v vs ih =>
    have step := rule.2 n
    rw [start] at step
    have eq := greedy_unique step (finite_greedy_sound h.1)
    have next : history a (n+1) = visit st v := by
      rw [← history_succ, start, eq]
    have result := ih (n+1) (visit st v) next h.2
    simpa [finish, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result

theorem certificate_from_zero {D : Nat → Prop} {a : Nat → Int}
    (rule : Rule D a) (vs : List Int) (h : Certificate D zeroState vs) :
    history a vs.length = finish zeroState vs := by
  simpa using certificate_history rule vs 0 zeroState (history_zero a rule.1) h

end G02
