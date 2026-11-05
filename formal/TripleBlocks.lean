import UniversalLiteral

set_option autoImplicit false

namespace G07
open G01

def Family (D : Nat → Prop) : Prop :=
  D 1 ∧ D 3 ∧ ¬D 2 ∧ ¬D 5 ∧ (∀ j, D (6+4*j)) ∧
    (∀ j, ¬D (8+4*j)) ∧ (∀ j, ¬D (9+4*j))

theorem next_positive {D : Nat → Prop} {b : Nat} {s : State}
    (one : D 1) (previous : D (2*b)) (hb : 1 ≤ b)
    (iv : Interval (-(b : Int)) b s)
    (hc : s.current = (b : Int) ∨ s.current = 1-(b : Int)) :
    Greedy D s ((b+1 : Nat) : Int) := by
  refine ⟨?_, ?_, ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · rcases hc with hc | hc
    · exact allowed_eq one (by decide) (Or.inr (by rw [hc]; omega))
    · exact allowed_eq previous (by omega) (Or.inr (by rw [hc]; omega))
  · intro w wu _
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ (b : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    constructor
    · rw [Int.natAbs_natCast]; omega
    · intro eq; rw [Int.natAbs_natCast] at eq; omega

theorem second_positive {D : Nat → Prop} {b : Nat} {s : State}
    (one : D 1) (absent : ¬D (2*b+2))
    (iv : Interval (-(b : Int)) ((b+1 : Nat) : Int) s)
    (hc : s.current = ((b+1 : Nat) : Int)) :
    Greedy D s ((b+2 : Nat) : Int) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inr (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ ((b+1 : Nat) : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    have bound : b+2 ≤ w.natAbs := by
      by_cases large : b+2 ≤ w.natAbs
      · exact large
      · have eq : w= -((b+1 : Nat) : Int) := by omega
        have dist : (s.current-w).natAbs=2*b+2 := by
          rw [hc, eq]
          have hd := Int.natAbs_eq ((((b+1 : Nat) : Int))- -((b+1 : Nat) : Int))
          omega
        exact False.elim (absent (dist ▸ wd.1))
    constructor
    · simpa only [Int.natAbs_natCast] using bound
    · intro eq
      rw [Int.natAbs_natCast] at eq
      have le := Int.le_natAbs (a := w)
      omega

theorem cross_negative {D : Nat → Prop} {b : Nat} {s : State}
    (next : D (2*b+4)) (absent : ¬D (2*b+3))
    (iv : Interval (-(b : Int)) ((b+2 : Nat) : Int) s)
    (hc : s.current = ((b+2 : Nat) : Int)) :
    Greedy D s (-((b+2 : Nat) : Int)) := by
  refine ⟨?_, allowed_eq next (by omega) (Or.inl (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ ((b+2 : Nat) : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    by_cases small : w.natAbs ≤ b+2
    · have eq : w= -((b+2 : Nat) : Int) := by
        by_cases yes : w= -((b+2 : Nat) : Int)
        · exact yes
        · have wrong : w= -((b+1 : Nat) : Int) := by omega
          have dist : (s.current-w).natAbs=2*b+3 := by
            rw [hc, wrong]
            have hd := Int.natAbs_eq ((((b+2 : Nat) : Int))- -((b+1 : Nat) : Int))
            omega
          exact False.elim (absent (dist ▸ wd.1))
      rw [eq]
      exact ⟨Nat.le_refl _, fun _ => Int.le_refl _⟩
    · constructor
      · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
      · intro eq; rw [Int.natAbs_neg, Int.natAbs_natCast] at eq; omega

theorem repair_negative {D : Nat → Prop} {b : Nat} {s : State}
    (one : D 1) (iv : Interval (-(b : Int)) ((b+2 : Nat) : Int) s) :
    Greedy D (visit s (-((b+2 : Nat) : Int))) (-((b+1 : Nat) : Int)) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inr (by simp only [visit]; omega)), ?_⟩
  · intro used
    change s.used (-((b+1 : Nat) : Int)) ∨ -((b+1 : Nat) : Int)= -((b+2 : Nat) : Int) at used
    rw [iv _] at used
    omega
  · intro w wu _
    have old : ¬s.used w := fun h => wu (Or.inl h)
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ ((b+2 : Nat) : Int)) := fun h => old ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    constructor
    · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
    · intro eq; rw [Int.natAbs_neg, Int.natAbs_natCast] at eq; omega

def block (b : Nat) : List Int := [((b+1 : Nat) : Int), ((b+2 : Nat) : Int), -((b+2 : Nat) : Int), -((b+1 : Nat) : Int)]

theorem finite_of_greedy {D : Nat → Prop} {s : State} {v : Int} (h : Greedy D s v) : G02.FiniteGreedy D s v :=
  ⟨h.1, h.2.1, fun w _ unused allowed => h.2.2 w unused allowed⟩

theorem block_certificate {D : Nat → Prop} {b : Nat} (s : State)
    (one : D 1) (previous : D (2*b)) (next : D (2*b+4))
    (absent2 : ¬D (2*b+2)) (absent3 : ¬D (2*b+3)) (hb : 1 ≤ b)
    (iv : Interval (-(b : Int)) b s) (hc : s.current = (b : Int) ∨ s.current = 1-(b : Int)) :
    G02.Certificate D s (block b) := by
  have choice1 := next_positive one previous hb iv hc
  have iv1 : Interval (-(b : Int)) ((b+1 : Nat) : Int) (visit s ((b+1 : Nat) : Int)) := by
    simpa only [Int.natCast_add, Int.natCast_one] using interval_visit_right (show -(b : Int) ≤ (b : Int)+1 by omega) iv
  have choice2 := second_positive one absent2 iv1 rfl
  have iv2 : Interval (-(b : Int)) ((b+2 : Nat) : Int)
      (visit (visit s ((b+1 : Nat) : Int)) ((b+2 : Nat) : Int)) := by
    have eq : ((b+1 : Nat) : Int)+1=((b+2 : Nat) : Int) := by omega
    simpa only [eq] using interval_visit_right (show -(b : Int) ≤ ((b+1 : Nat) : Int)+1 by omega) iv1
  have choice3 := cross_negative next absent3 iv2 rfl
  have choice4 := repair_negative one iv2
  exact ⟨finite_of_greedy choice1, finite_of_greedy choice2, finite_of_greedy choice3, finite_of_greedy choice4, True.intro⟩

theorem block_finish {b : Nat} {s : State} (iv : Interval (-(b : Int)) b s) :
    Interval (-((b+2 : Nat) : Int)) ((b+2 : Nat) : Int) (G02.finish s (block b)) ∧
    (G02.finish s (block b)).current=1-((b+2 : Nat) : Int) := by
  constructor
  · intro z
    simp only [block, G02.finish, visit]
    rw [iv z]
    omega
  · simp only [block, G02.finish, visit]
    omega

end G07
