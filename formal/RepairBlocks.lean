import TripleObstruction

set_option autoImplicit false

namespace G09
open G01 G02

def Frontier (b : Nat) (s : State) : Prop :=
  s.current = -(b : Int) ∧
  ∀ z, s.used z ↔ (-(b : Int) ≤ z ∧ z < (b : Int)) ∨ z = (b : Int)+1

def repairBlock (b : Nat) : List Int :=
  [(b : Int), (b : Int)+3, -(b : Int)-1, -(b : Int)-2]

theorem first_repair {D : Nat → Prop} {b : Nat} {s : State}
    (jump : D (2*b)) (hb : 1 ≤ b) (front : Frontier b s) :
    Greedy D s (b : Int) := by
  refine ⟨?_, allowed_eq jump (by omega) (Or.inr (by rw [front.1]; omega)), ?_⟩
  · intro used; have h := (front.2 _).mp used; omega
  · intro w wu _
    have out : ¬((-(b : Int) ≤ w ∧ w < (b : Int)) ∨ w=(b : Int)+1) :=
      fun h => wu ((front.2 w).mpr h)
    have hw := Int.natAbs_eq w
    constructor
    · rw [Int.natAbs_natCast]; omega
    · intro eq; rw [Int.natAbs_natCast] at eq; omega

theorem after_repair {b : Nat} {s : State} (front : Frontier b s) :
    Interval (-(b : Int)) ((b : Int)+1) (visit s (b : Int)) := by
  intro z
  change (s.used z ∨ z=(b : Int)) ↔ _
  rw [front.2 z]
  omega

theorem forward_three {D : Nat → Prop} {b : Nat} {s : State}
    (three : D 3) (no2 : ¬D 2) (no1 : ¬D (2*b+1)) (noCross2 : ¬D (2*b+2))
    (iv : Interval (-(b : Int)) ((b : Int)+1) s) (hc : s.current=(b : Int)) :
    Greedy D s ((b : Int)+3) := by
  refine ⟨?_, allowed_eq three (by decide) (Or.inr (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ (b : Int)+1) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    have dist := Int.natAbs_eq (s.current-w)
    have bound : b+3 ≤ w.natAbs := by
      by_cases large : b+3 ≤ w.natAbs
      · exact large
      · have bad : w=(b : Int)+2 ∨ w= -(b : Int)-1 ∨ w= -(b : Int)-2 := by omega
        rcases bad with h | h | h
        · have eq : (s.current-w).natAbs=2 := by rw [hc] at dist; omega
          exact False.elim (no2 (eq ▸ wd.1))
        · have eq : (s.current-w).natAbs=2*b+1 := by rw [hc] at dist; omega
          exact False.elim (no1 (eq ▸ wd.1))
        · have eq : (s.current-w).natAbs=2*b+2 := by rw [hc] at dist; omega
          exact False.elim (noCross2 (eq ▸ wd.1))
    have chosen : ((b : Int)+3).natAbs=b+3 := by
      have h := Int.natAbs_eq ((b : Int)+3); omega
    constructor
    · rw [chosen]; exact bound
    · intro eq; rw [chosen] at eq; omega

theorem cross_after_three {D : Nat → Prop} {b : Nat} {s : State}
    (jump : D (2*b+4)) (iv : Interval (-(b : Int)) ((b : Int)+1) s) :
    Greedy D (visit s ((b : Int)+3)) (-(b : Int)-1) := by
  refine ⟨?_, allowed_eq jump (by omega) (Or.inl (by simp only [visit]; omega)), ?_⟩
  · intro used
    change s.used (-(b : Int)-1) ∨ -(b : Int)-1=(b : Int)+3 at used
    rw [iv _] at used
    omega
  · intro w wu _
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ (b : Int)+1) := fun h => wu (Or.inl ((iv w).mpr h))
    have hw := Int.natAbs_eq w
    have chosen : (-(b : Int)-1).natAbs=b+1 := by
      have h := Int.natAbs_eq (-(b : Int)-1); omega
    constructor
    · rw [chosen]; omega
    · intro eq; rw [chosen] at eq; omega

theorem last_negative {D : Nat → Prop} {b : Nat} {s : State}
    (one : D 1) (no3 : ¬D (2*b+3))
    (iv : Interval (-(b : Int)) ((b : Int)+1) s) :
    Greedy D (visit (visit s ((b : Int)+3)) (-(b : Int)-1)) (-(b : Int)-2) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inl (by simp only [visit]; omega)), ?_⟩
  · intro used
    change (s.used (-(b : Int)-2) ∨ -(b : Int)-2=(b : Int)+3) ∨ -(b : Int)-2= -(b : Int)-1 at used
    rw [iv _] at used
    omega
  · intro w wu wd
    have outside : ¬((-(b : Int) ≤ w ∧ w ≤ (b : Int)+1) ∨ w=(b : Int)+3 ∨ w= -(b : Int)-1) := by
      intro h; rcases h with h | h | h
      · exact wu (Or.inl (Or.inl ((iv w).mpr h)))
      · exact wu (Or.inl (Or.inr h))
      · exact wu (Or.inr h)
    have hw := Int.natAbs_eq w
    have chosen : (-(b : Int)-2).natAbs=b+2 := by
      have h := Int.natAbs_eq (-(b : Int)-2); omega
    have excluded : w ≠ (b : Int)+2 := by
      intro eq
      have hd : (((visit (visit s ((b : Int)+3)) (-(b : Int)-1)).current)-w).natAbs=2*b+3 := by
        simp only [visit]
        have h := Int.natAbs_eq (-(b : Int)-1-w); omega
      exact no3 (hd ▸ wd.1)
    constructor
    · rw [chosen]; omega
    · intro eq; rw [chosen] at eq; omega

theorem repair_certificate {D : Nat → Prop} {b : Nat} (s : State)
    (one : D 1) (three : D 3) (jump : D (2*b)) (next : D (2*b+4))
    (no2 : ¬D 2) (no1 : ¬D (2*b+1)) (noCross2 : ¬D (2*b+2)) (no3 : ¬D (2*b+3))
    (hb : 1 ≤ b) (front : Frontier b s) : Certificate D s (repairBlock b) := by
  have iv := after_repair front
  exact ⟨G07.finite_of_greedy (first_repair jump hb front),
    G07.finite_of_greedy (forward_three three no2 no1 noCross2 iv rfl),
    G07.finite_of_greedy (cross_after_three next iv),
    G07.finite_of_greedy (last_negative one no3 iv), True.intro⟩

theorem repair_finish {b : Nat} {s : State} (front : Frontier b s) :
    Frontier (b+2) (finish s (repairBlock b)) := by
  constructor
  · simp only [repairBlock, finish, visit]; omega
  · intro z
    simp only [repairBlock, finish, visit]
    rw [front.2 z]
    omega

end G09
