import Shielded

set_option autoImplicit false

namespace G03
open G01

theorem negative_step {D : Nat → Prop} {q u B T x : Nat} {s : State}
    (one : D 1) (qu : q < 2*u+1) (ux : u ≤ x) (xb : x < B)
    (halves : B ≤ T ∧ T ≤ B+1)
    (gap : ∀ d, q < d → d < B+T → ¬D d)
    (hc : s.current = -(x : Int)) (iv : Interval (-(x : Int)) u s) :
    Greedy D s (-((x+1 : Nat) : Int)) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inl (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(x : Int) ≤ w ∧ w ≤ (u : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    by_cases small : w.natAbs ≤ x+1
    · have eq : w = -((x+1 : Nat) : Int) := by
        by_cases negative : w < -(x : Int)
        · omega
        · have hd := Int.natAbs_eq (s.current-w)
          rw [hc] at hd
          exact False.elim (gap _ (by omega) (by omega) wd.1)
      rw [eq]; exact ⟨Nat.le_refl _, fun _ => Int.le_refl _⟩
    · unfold Preferred
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      exact ⟨by omega, fun h => by omega⟩

theorem negative_run {D : Nat → Prop} {q u B T : Nat}
    (one : D 1) (qu : q < 2*u+1) (halves : B ≤ T ∧ T ≤ B+1)
    (gap : ∀ d, q < d → d < B+T → ¬D d)
    (budget x : Nat) (s : State) (ux : u ≤ x) (xb : x ≤ B) (hb : B-x ≤ budget)
    (hc : s.current = -(x : Int)) (iv : Interval (-(x : Int)) u s) :
    ∃ t, Reaches D s t ∧ t.current = -(B : Int) ∧ Interval (-(B : Int)) u t := by
  induction budget generalizing x s with
  | zero => have eq : x=B := by omega
            subst x; exact ⟨s, .refl s, hc, iv⟩
  | succ budget ih =>
    by_cases eq : x=B
    · subst x; exact ⟨s, .refl s, hc, iv⟩
    · have choice := negative_step one qu ux (by omega) halves gap hc iv
      have iv' : Interval (-((x+1 : Nat) : Int)) u (visit s (-((x+1 : Nat) : Int))) := by
        have e : -(x : Int)-1 = -((x+1 : Nat) : Int) := by omega
        simpa only [e] using interval_visit_left (show -(x : Int) ≤ (u : Int)+1 by omega) iv
      obtain ⟨t, path, current, used⟩ :=
        ih (x+1) (visit s (-((x+1 : Nat) : Int))) (by omega) (by omega) (by omega) rfl iv'
      exact ⟨t, .cons choice path, current, used⟩

theorem cross_positive {D : Nat → Prop} {q u B T : Nat} {s : State}
    (qu : q < 2*u+1) (ub : u ≤ B) (ut : u < T) (halves : B ≤ T ∧ T ≤ B+1)
    (large : D (B+T)) (gap : ∀ d, q < d → d < B+T → ¬D d)
    (hc : s.current = -(B : Int)) (iv : Interval (-(B : Int)) u s) :
    Greedy D s (T : Int) := by
  refine ⟨?_, allowed_eq large (by omega) (Or.inr (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(B : Int) ≤ w ∧ w ≤ (u : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    have lower : T ≤ w.natAbs := by
      by_cases h : T ≤ w.natAbs
      · exact h
      · have hd := Int.natAbs_eq (s.current-w)
        rw [hc] at hd
        exact False.elim (gap _ (by omega) (by omega) wd.1)
    constructor
    · simpa only [Int.natAbs_natCast] using lower
    · intro eq
      rw [Int.natAbs_natCast] at eq
      have h := Int.le_natAbs (a := w)
      omega

end G03
