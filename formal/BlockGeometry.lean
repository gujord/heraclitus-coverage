import Examples

set_option autoImplicit false

namespace G01


theorem state_ext {s t : State} (hc : s.current = t.current)
    (hu : ∀ z, s.used z ↔ t.used z) : s = t := by
  cases s with
  | mk c u =>
    cases t with
    | mk d v =>
      dsimp at hc hu
      have he : u = v := funext (fun z => propext (hu z))
      cases hc; cases he; rfl

def Interval (l h : Int) (s : State) : Prop :=
  ∀ z, s.used z ↔ l ≤ z ∧ z ≤ h

theorem interval_visit_left {l h : Int} {s : State} (lh : l ≤ h+1)
    (iv : Interval l h s) : Interval (l-1) h (visit s (l-1)) := by
  intro z
  change (s.used z ∨ z = l-1) ↔ _
  rw [iv z]
  omega

theorem interval_visit_right {l h : Int} {s : State} (lh : l ≤ h+1)
    (iv : Interval l h s) : Interval l (h+1) (visit s (h+1)) := by
  intro z
  change (s.used z ∨ z = h+1) ↔ _
  rw [iv z]
  omega

theorem allowed_eq {D : Nat → Prop} {c v : Int} {d : Nat}
    (hd : D d) (pos : 0 < d) (eq : c-v = (d : Int) ∨ c-v = -(d : Int)) :
    Allowed D c v := by
  unfold Allowed
  rcases eq with h | h <;> rw [h] <;> simpa using And.intro hd pos

theorem second_negative {D : Nat → Prop} (two : D 2) :
    Greedy D (visit zeroState 1) (-1) := by
  refine ⟨?_, ?_, ?_⟩
  · change ¬((-1 : Int) = 0 ∨ (-1 : Int) = 1)
    omega
  · exact ⟨two, by decide⟩
  · intro w wu _
    change ¬(w = 0 ∨ w = 1) at wu
    have hw := Int.natAbs_eq w
    constructor
    · change 1 ≤ w.natAbs; omega
    · intro eq
      change 1 = w.natAbs at eq
      omega

theorem next_positive {D : Nat → Prop} {b : Nat} {s : State}
    (hb : 1 ≤ b) (two : D 2) (large : D (2*b)) (full : Complete b s)
    (hc : s.current = (b : Int)-1 ∨ s.current = 1-(b : Int)) :
    Greedy D s ((b+1 : Nat) : Int) := by
  refine ⟨?_, ?_, ?_⟩
  · intro used
    have bound := (full _).mp used
    rw [Int.natAbs_natCast] at bound
    omega
  · rcases hc with hc | hc
    · exact allowed_eq two (by decide) (Or.inr (by rw [hc]; omega))
    · exact allowed_eq large (by omega) (Or.inr (by rw [hc]; omega))
  · intro w wu _
    have outside : ¬w.natAbs ≤ b := fun h => wu ((full w).mpr h)
    constructor
    · rw [Int.natAbs_natCast]; omega
    · intro eq
      rw [Int.natAbs_natCast] at eq
      have bound := Int.le_natAbs (a := w)
      omega

end G01
