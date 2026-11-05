import MixedGeometry

set_option autoImplicit false

namespace G03
open G01

theorem fill_positive {D : Nat → Prop} {u B T : Nat} {s : State}
    (one : D 1) (two : D 2) (ut : u+1 < T) (halves : B ≤ T ∧ T ≤ B+1)
    (iv : Interval (-(B : Int)) u s) :
    ∃ t, Reaches D (visit s (T : Int)) t ∧
      Interval (-(B : Int)) T t ∧ t.current = (T : Int)-1 := by
  have interior : ∀ z, z.natAbs < T →
      ((visit s (T : Int)).used z ↔ ¬∃ r, u+1 ≤ r ∧ r < T ∧ z = point true r) := by
    intro z zb
    change (s.used z ∨ z=(T : Int)) ↔ _
    rw [iv z]
    have hz := Int.natAbs_eq z
    constructor
    · intro used
      rintro ⟨r, ur, rt, eq⟩
      simp only [point, ite_true] at eq
      rcases used with used | used <;> omega
    · intro holes
      by_cases inside : -(B : Int) ≤ z ∧ z ≤ (u : Int)
      · exact Or.inl inside
      · exact False.elim (holes ⟨z.natAbs, by omega, zb, by simp only [point, ite_true]; omega⟩)
  obtain ⟨t, path, endpoint, filled⟩ :=
    shielded_filling D true (u+1) T (visit s (T : Int)) one two (by omega) ut rfl interior
  refine ⟨t, path, ?_, ?_⟩
  · intro z
    rw [filled z]
    change (z.natAbs < T ∨ (s.used z ∨ z=(T : Int))) ↔ _
    rw [iv z]
    have hz := Int.natAbs_eq z
    omega
  · simp only [point, ite_true] at endpoint
    omega

theorem fill_negative {D : Nat → Prop} {b B T : Nat} {s : State}
    (one : D 1) (two : D 2) (bB : b+1 < B) (halves : B ≤ T ∧ T ≤ B+1)
    (iv : Interval (-(b : Int)) T s) :
    ∃ t, Reaches D (visit s (-(B : Int))) t ∧
      Interval (-(B : Int)) T t ∧ t.current = 1-(B : Int) := by
  have interior : ∀ z, z.natAbs < B →
      ((visit s (-(B : Int))).used z ↔ ¬∃ r, b+1 ≤ r ∧ r < B ∧ z = point false r) := by
    intro z zb
    change (s.used z ∨ z=-(B : Int)) ↔ _
    rw [iv z]
    have hz := Int.natAbs_eq z
    constructor
    · intro used
      rintro ⟨r, br, rb, eq⟩
      simp only [point, Bool.false_eq_true, ite_false] at eq
      rcases used with used | used <;> omega
    · intro holes
      by_cases inside : -(b : Int) ≤ z ∧ z ≤ (T : Int)
      · exact Or.inl inside
      · exact False.elim (holes ⟨z.natAbs, by omega, zb,
          by simp only [point, Bool.false_eq_true, ite_false]; omega⟩)
  obtain ⟨t, path, endpoint, filled⟩ :=
    shielded_filling D false (b+1) B (visit s (-(B : Int))) one two (by omega) bB rfl interior
  refine ⟨t, path, ?_, ?_⟩
  · intro z
    rw [filled z]
    change (z.natAbs < B ∨ (s.used z ∨ z=-(B : Int))) ↔ _
    rw [iv z]
    have hz := Int.natAbs_eq z
    omega
  · simp only [point, Bool.false_eq_true, ite_false] at endpoint
    omega

theorem odd_next {D : Nat → Prop} {b : Nat} {s : State}
    (two : D 2) (previous : D (2*b+1))
    (iv : Interval (-(b : Int)) ((b+1 : Nat) : Int) s)
    (hc : s.current = (b : Int) ∨ s.current = 1-(b : Int)) :
    Greedy D s (-((b+1 : Nat) : Int)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · rcases hc with hc | hc
    · exact allowed_eq previous (by omega) (Or.inl (by rw [hc]; omega))
    · exact allowed_eq two (by decide) (Or.inl (by rw [hc]; omega))
  · intro w wu _
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ ((b+1 : Nat) : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    constructor
    · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
    · intro eq
      rw [Int.natAbs_neg, Int.natAbs_natCast] at eq
      omega

end G03
