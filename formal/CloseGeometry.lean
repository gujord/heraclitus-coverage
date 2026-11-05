import InfiniteWitnesses
import MixedGlobal

set_option autoImplicit false

namespace G05
open G01 G03

theorem positive_step {D : Nat → Prop} {q b B T x : Nat} {s : State}
    (one : D 1) (qb : q < 2*b+2) (bx : b+1 ≤ x) (xt : x < T) (halves : B ≤ T ∧ T ≤ B+1)
    (gap : ∀ d, q < d → d < B+T → ¬D d)
    (hc : s.current = (x : Int)) (iv : Interval (-(b : Int)) x s) :
    Greedy D s ((x+1 : Nat) : Int) := by
  refine ⟨?_, allowed_eq one (by decide) (Or.inr (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ (x : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    have lower : x+1 ≤ w.natAbs := by
      by_cases h : x+1 ≤ w.natAbs
      · exact h
      · have hd := Int.natAbs_eq (s.current-w)
        rw [hc] at hd
        exact False.elim (gap _ (by omega) (by omega) wd.1)
    constructor
    · simpa only [Int.natAbs_natCast] using lower
    · intro eq
      rw [Int.natAbs_natCast] at eq
      have bound := Int.le_natAbs (a := w)
      omega

theorem positive_run {D : Nat → Prop} {q b B T : Nat}
    (one : D 1) (qb : q < 2*b+2) (halves : B ≤ T ∧ T ≤ B+1)
    (gap : ∀ d, q < d → d < B+T → ¬D d)
    (budget x : Nat) (s : State) (bx : b+1 ≤ x) (xt : x ≤ T) (hb : T-x ≤ budget)
    (hc : s.current = (x : Int)) (iv : Interval (-(b : Int)) x s) :
    ∃ t, Reaches D s t ∧ t.current = (T : Int) ∧ Interval (-(b : Int)) T t := by
  induction budget generalizing x s with
  | zero => have eq : x=T := by omega
            subst x; exact ⟨s, .refl s, hc, iv⟩
  | succ budget ih =>
    by_cases eq : x=T
    · subst x; exact ⟨s, .refl s, hc, iv⟩
    · have choice := positive_step one qb bx (by omega) halves gap hc iv
      have iv' : Interval (-(b : Int)) ((x+1 : Nat) : Int) (visit s ((x+1 : Nat) : Int)) := by
        simpa only [Int.natCast_add, Int.natCast_one] using
          interval_visit_right (show -(b : Int) ≤ (x : Int)+1 by omega) iv
      obtain ⟨t, path, current, used⟩ :=
        ih (x+1) (visit s ((x+1 : Nat) : Int)) (by omega) (by omega) (by omega) rfl iv'
      exact ⟨t, .cons choice path, current, used⟩

theorem cross_negative {D : Nat → Prop} {q b B T : Nat} {s : State}
    (qb : q < 2*b+2) (bB : b+1 ≤ B) (halves : B ≤ T ∧ T ≤ B+1) (large : D (B+T))
    (gap : ∀ d, q < d → d < B+T → ¬D d)
    (hc : s.current = (T : Int)) (iv : Interval (-(b : Int)) T s) :
    Greedy D s (-(B : Int)) := by
  refine ⟨?_, allowed_eq large (by omega) (Or.inl (by rw [hc]; omega)), ?_⟩
  · intro used; have h := (iv _).mp used; omega
  · intro w wu wd
    have outside : ¬(-(b : Int) ≤ w ∧ w ≤ (T : Int)) := fun h => wu ((iv w).mpr h)
    have hw := Int.natAbs_eq w
    by_cases small : w.natAbs ≤ B
    · have eq : w = -(B : Int) := by
        by_cases eq : w = -(B : Int)
        · exact eq
        · have hd := Int.natAbs_eq (s.current-w)
          rw [hc] at hd
          exact False.elim (gap _ (by omega) (by omega) wd.1)
      rw [eq]; exact ⟨Nat.le_refl _, fun _ => Int.le_refl _⟩
    · unfold Preferred
      rw [Int.natAbs_neg, Int.natAbs_natCast]
      exact ⟨by omega, fun h => by omega⟩

end G05
