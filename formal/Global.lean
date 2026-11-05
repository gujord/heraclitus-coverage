import History

set_option autoImplicit false

namespace G01


def Bounded (st : State) : Prop := ∃ B : Nat, ∀ z, st.used z → z.natAbs ≤ B

theorem zero_bounded : Bounded zeroState := by
  refine ⟨0, ?_⟩
  intro z used
  change z = 0 at used
  simp only [used, Int.natAbs_zero, Nat.le_refl]

theorem visit_bounded {st : State} (v : Int) (bound : Bounded st) : Bounded (visit st v) := by
  obtain ⟨B, hb⟩ := bound
  refine ⟨B+v.natAbs, ?_⟩
  intro z used
  rcases used with old | eq
  · have h := hb z old; omega
  · subst z; omega

structure BoundedState where
  state : State
  bounded : Bounded state

end G01
