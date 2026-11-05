import FinitePrefix

set_option autoImplicit false

namespace G02
open G01

def Unbounded (D : Nat → Prop) : Prop := ∀ N, ∃ d, N < d ∧ D d

theorem unbounded_admissible {D : Nat → Prop} (unbounded : Unbounded D)
    (st : State) (bounded : Bounded st) : ∃ v, ¬st.used v ∧ Allowed D st.current v := by
  obtain ⟨B, hb⟩ := bounded
  obtain ⟨d, large, member⟩ := unbounded (B+st.current.natAbs)
  let v : Int := st.current+(d : Int)
  have hc := Int.natAbs_eq st.current
  have beyond : (B : Int) < v := by dsimp [v]; omega
  refine ⟨v, ?_, ?_⟩
  · intro used
    have bound := hb v used
    have lower := Int.le_natAbs (a := v)
    omega
  · exact allowed_eq member (by omega) (Or.inr (by dsimp [v]; omega))

noncomputable def next (D : Nat → Prop) (unbounded : Unbounded D) (st : BoundedState) : Int :=
  Classical.choose (greedy_exists (unbounded_admissible unbounded st.state st.bounded))

theorem next_spec (D : Nat → Prop) (unbounded : Unbounded D) (st : BoundedState) :
    Greedy D st.state (next D unbounded st) :=
  Classical.choose_spec (greedy_exists (unbounded_admissible unbounded st.state st.bounded))

noncomputable def orbit (D : Nat → Prop) (unbounded : Unbounded D) : Nat → BoundedState
  | 0 => ⟨zeroState, zero_bounded⟩
  | n+1 => ⟨visit (orbit D unbounded n).state (next D unbounded (orbit D unbounded n)),
      visit_bounded _ (orbit D unbounded n).bounded⟩

noncomputable def sequence (D : Nat → Prop) (unbounded : Unbounded D) (n : Nat) : Int :=
  (orbit D unbounded n).state.current

theorem orbit_history (D : Nat → Prop) (unbounded : Unbounded D) (n : Nat) :
    (orbit D unbounded n).state = history (sequence D unbounded) n := by
  induction n with
  | zero => exact (history_zero (sequence D unbounded) rfl).symm
  | succ n ih =>
    change visit (orbit D unbounded n).state (sequence D unbounded (n+1)) = _
    rw [ih, history_succ]

theorem unbounded_exists (D : Nat → Prop) (unbounded : Unbounded D) : ∃ a, Rule D a := by
  refine ⟨sequence D unbounded, rfl, ?_⟩
  intro n
  have choice := next_spec D unbounded (orbit D unbounded n)
  rw [orbit_history] at choice
  exact choice

end G02
