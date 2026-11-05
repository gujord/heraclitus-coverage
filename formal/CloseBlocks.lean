import CloseGeometry

set_option autoImplicit false

namespace G05
open G01 G03

theorem fill_negative_closed {D : Nat → Prop} {b B T : Nat} {s : State}
    (one : D 1) (two : D 2) (bB : b+1 ≤ B) (halves : B ≤ T ∧ T ≤ B+1)
    (iv : Interval (-(b : Int)) T s) :
    ∃ t, Reaches D (visit s (-(B : Int))) t ∧ Interval (-(B : Int)) T t ∧
      (t.current = 1-(B : Int) ∨ t.current = -(B : Int)) := by
  by_cases eq : b+1=B
  · refine ⟨visit s (-(B : Int)), .refl _, ?_, Or.inr rfl⟩
    intro z
    change (s.used z ∨ z= -(B : Int)) ↔ _
    rw [iv z]
    omega
  · obtain ⟨t, path, full, last⟩ := G03.fill_negative one two (by omega) halves iv
    exact ⟨t, path, full, Or.inl last⟩

theorem fill_positive_closed {D : Nat → Prop} {u B T : Nat} {s : State}
    (one : D 1) (two : D 2) (uT : u+1 ≤ T) (halves : B ≤ T ∧ T ≤ B+1)
    (iv : Interval (-(B : Int)) u s) :
    ∃ t, Reaches D (visit s (T : Int)) t ∧ Interval (-(B : Int)) T t ∧
      (t.current = (T : Int)-1 ∨ t.current = (T : Int)) := by
  by_cases eq : u+1=T
  · refine ⟨visit s (T : Int), .refl _, ?_, Or.inr rfl⟩
    intro z
    change (s.used z ∨ z= (T : Int)) ↔ _
    rw [iv z]
    omega
  · obtain ⟨t, path, full, last⟩ := G03.fill_positive one two (by omega) halves iv
    exact ⟨t, path, full, Or.inl last⟩

theorem positive_block {D : Nat → Prop} {q b B T x : Nat} (s : State)
    (one : D 1) (two : D 2) (qb : q < 2*b+2) (bx : b+1 ≤ x)
    (xT : x ≤ T) (bB : b+1 ≤ B) (halves : B ≤ T ∧ T ≤ B+1)
    (large : D (B+T)) (gap : ∀ d, q < d → d < B+T → ¬D d)
    (hc : s.current = (x : Int)) (iv : Interval (-(b : Int)) x s) :
    ∃ t, Reaches D s t ∧ Interval (-(B : Int)) T t ∧
      (t.current = 1-(B : Int) ∨ t.current = -(B : Int)) := by
  obtain ⟨v, path, current, used⟩ :=
    G05.positive_run one qb halves gap T x s bx xT (by omega) hc iv
  have cross := G05.cross_negative qb bB halves large gap current used
  obtain ⟨t, fill, complete, endpoint⟩ := fill_negative_closed one two bB halves used
  exact ⟨t, path.trans (.cons cross fill), complete, endpoint⟩

theorem negative_block {D : Nat → Prop} {q u B T x : Nat} (s : State)
    (one : D 1) (two : D 2) (qu : q < 2*u+1) (ux : u ≤ x)
    (xB : x ≤ B) (uT : u+1 ≤ T) (halves : B ≤ T ∧ T ≤ B+1)
    (large : D (B+T)) (gap : ∀ d, q < d → d < B+T → ¬D d)
    (hc : s.current = -(x : Int)) (iv : Interval (-(x : Int)) u s) :
    ∃ t, Reaches D s t ∧ Interval (-(B : Int)) T t ∧
      (t.current = (T : Int)-1 ∨ t.current = (T : Int)) := by
  obtain ⟨v, path, current, used⟩ :=
    G03.negative_run one qu halves gap B x s ux xB (by omega) hc iv
  have cross := G03.cross_positive qu (by omega) (by omega) halves large gap current used
  obtain ⟨t, fill, complete, endpoint⟩ := fill_positive_closed one two uT halves used
  exact ⟨t, path.trans (.cons cross fill), complete, endpoint⟩

theorem even_boundary_positive {D : Nat → Prop} {b : Nat} {s : State}
    (one : D 1) (iv : Interval (-(b : Int)) b s) (hc : s.current = (b : Int)) :
    Greedy D s ((b+1 : Nat) : Int) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inr (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu _
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ (b : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    constructor
    · rw [Int.natAbs_natCast]; omega
    · intro eq
      rw [Int.natAbs_natCast] at eq
      omega

theorem odd_boundary_negative {D : Nat → Prop} {b : Nat} {s : State}
    (one : D 1) (iv : Interval (-(b : Int)) ((b+1 : Nat) : Int) s)
    (hc : s.current = -(b : Int)) : Greedy D s (-((b+1 : Nat) : Int)) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inl (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu _
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ ((b+1 : Nat) : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    constructor
    · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
    · intro eq
      rw [Int.natAbs_neg, Int.natAbs_natCast] at eq
      omega

end G05
