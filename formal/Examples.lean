import OneSide

set_option autoImplicit false

namespace G01


def entranceState (p : Bool) (L B : Nat) : State :=
  ⟨point p B, fun z => z.natAbs ≤ B ∧ ¬∃ t, L ≤ t ∧ t < B ∧ z = point p t⟩

theorem entranceState_spec (p : Bool) (L B : Nat) :
    Entrance p L B (entranceState p L B) := ⟨rfl, fun _ => Iff.rfl⟩

def zeroState : State := ⟨0, fun z => z = 0⟩

theorem initial_positive {D : Nat → Prop} (one : D 1) : Greedy D zeroState 1 := by
  refine ⟨by change (1 : Int) ≠ 0; decide, ?_, ?_⟩
  · exact ⟨one, by decide⟩
  · intro w wu _
    change w ≠ 0 at wu
    have hw := Int.natAbs_eq w
    constructor
    · change 1 ≤ w.natAbs
      omega
    · intro eq
      change 1 = w.natAbs at eq
      omega

end G01
