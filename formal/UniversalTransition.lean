import CloseTransition

set_option autoImplicit false

namespace G06
open G01 G03 G05

theorem separated_transition {D : Nat → Prop} {q r : Nat} (s : State)
    (one : D 1) (two : D 2) (hq : 2 ≤ q) (qr : q+2 ≤ r)
    (previous : D q) (large : D r)
    (gap : ∀ d, q < d → d < r → ¬D d)
    (full : Box q s) (endpoint : Ends q s) :
    ∃ t, Reaches D s t ∧ Box r t ∧ Ends r t := by
  have sum : r/2+(r+1)/2=r := by omega
  have halves : r/2 ≤ (r+1)/2 ∧ (r+1)/2 ≤ r/2+1 := ⟨by omega, by omega⟩
  have next : D (r/2+(r+1)/2) := by simpa only [sum] using large
  have absent : ∀ d, q < d → d < r/2+(r+1)/2 → ¬D d := by simpa only [sum] using gap
  by_cases even : q%2=0
  · have top : (q+1)/2=q/2 := by omega
    have doubled : 2*(q/2)=q := by omega
    have iv : Interval (-(q/2 : Nat)) (q/2 : Nat) s := by simpa only [Box, top] using full
    by_cases neg : s.current = -(q/2 : Nat)
    · obtain ⟨t, path, complete, last⟩ :=
        G05.negative_block (q := q) (u := q/2) (B := r/2) (T := (r+1)/2) (x := q/2)
          s one two (by omega) (by omega) (by omega) (by omega) halves next absent neg iv
      refine ⟨t, path, complete, ?_⟩
      rcases last with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))
    · have complete : Complete (q/2) s := by
        intro z; rw [iv z]; have hz := Int.natAbs_eq z; omega
      have choice : Greedy D s ((q/2+1 : Nat) : Int) := by
        rcases endpoint with h | h | h | h
        · exact next_positive (by omega) two (by simpa only [doubled] using previous)
            complete (Or.inl (by rw [top] at h; exact h))
        · exact next_positive (by omega) two (by simpa only [doubled] using previous) complete (Or.inr h)
        · exact even_boundary_positive one iv (by rw [top] at h; exact h)
        · exact False.elim (neg h)
      have iv' : Interval (-(q/2 : Nat)) ((q/2+1 : Nat) : Int)
          (visit s ((q/2+1 : Nat) : Int)) := by
        simpa only [Int.natCast_add, Int.natCast_one] using
          interval_visit_right (show -(q/2 : Nat) ≤ (q/2 : Nat)+(1 : Int) by omega) iv
      obtain ⟨t, path, used, last⟩ :=
        positive_block (q := q) (b := q/2) (B := r/2) (T := (r+1)/2) (x := q/2+1)
          (visit s ((q/2+1 : Nat) : Int)) one two (by omega) (by omega) (by omega)
          (by omega) halves next absent rfl iv'
      refine ⟨t, .cons choice path, used, ?_⟩
      rcases last with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
  · have top : (q+1)/2=q/2+1 := by omega
    have doubled : 2*(q/2)+1=q := by omega
    have iv : Interval (-(q/2 : Nat)) ((q/2+1 : Nat) : Int) s := by simpa only [Box, top] using full
    by_cases pos : s.current = ((q/2+1 : Nat) : Int)
    · obtain ⟨t, path, complete, last⟩ :=
        positive_block (q := q) (b := q/2) (B := r/2) (T := (r+1)/2) (x := q/2+1)
          s one two (by omega) (by omega) (by omega) (by omega) halves next absent pos iv
      refine ⟨t, path, complete, ?_⟩
      rcases last with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inr h))
    · have choice : Greedy D s (-((q/2+1 : Nat) : Int)) := by
        rcases endpoint with h | h | h | h
        · apply G03.odd_next two (by simpa only [doubled] using previous) iv
          left
          rw [top] at h
          omega
        · exact G03.odd_next two (by simpa only [doubled] using previous) iv (Or.inr h)
        · exact False.elim (pos (by rw [top] at h; exact h))
        · exact odd_boundary_negative one iv h
      have iv' : Interval (-((q/2+1 : Nat) : Int)) ((q/2+1 : Nat) : Int)
          (visit s (-((q/2+1 : Nat) : Int))) := by
        have eq : -(q/2 : Nat)-(1 : Int) = -((q/2+1 : Nat) : Int) := by omega
        simpa only [eq] using interval_visit_left (show -(q/2 : Nat) ≤ ((q/2+1 : Nat) : Int)+1 by omega) iv
      obtain ⟨t, path, used, last⟩ :=
        G05.negative_block (q := q) (u := q/2+1) (B := r/2) (T := (r+1)/2) (x := q/2+1)
          (visit s (-((q/2+1 : Nat) : Int))) one two (by omega) (by omega) (by omega)
          (by omega) halves next absent rfl iv'
      refine ⟨t, .cons choice path, used, ?_⟩
      rcases last with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h))

theorem adjacent_transition {D : Nat → Prop} {q : Nat} (s : State)
    (one : D 1) (two : D 2) (hq : 2 ≤ q) (previous : D q) (next : D (q+1))
    (full : Box q s) (endpoint : Ends q s) :
    ∃ t, Reaches D s t ∧ Box (q+1) t ∧ Ends (q+1) t := by
  by_cases even : q%2=0
  · have top : (q+1)/2=q/2 := by omega
    have iv : Interval (-(q/2 : Nat)) (q/2 : Nat) s := by simpa only [Box, top] using full
    have choice : Greedy D s ((q/2+1 : Nat) : Int) := by
      refine ⟨?_, ?_, ?_⟩
      · intro used; have h := (iv _).mp used; omega
      · rcases endpoint with h | h | h | h
        · rw [top] at h
          exact allowed_eq two (by decide) (Or.inr (by omega))
        · exact allowed_eq previous (by omega) (Or.inr (by omega))
        · rw [top] at h
          exact allowed_eq one (by decide) (Or.inr (by omega))
        · exact allowed_eq next (by omega) (Or.inr (by omega))
      · intro w wu _
        have outside : ¬(-(q/2 : Nat) ≤ w ∧ w ≤ (q/2 : Nat)) := fun h => wu ((iv w).mpr h)
        have hw := Int.natAbs_eq w
        constructor
        · rw [Int.natAbs_natCast]; omega
        · intro eq; rw [Int.natAbs_natCast] at eq; omega
    refine ⟨visit s ((q/2+1 : Nat) : Int), .cons choice (.refl _), ?_, ?_⟩
    · intro z
      change (s.used z ∨ z=((q/2+1 : Nat) : Int)) ↔ _
      rw [iv z]
      omega
    · apply Or.inr; apply Or.inr; apply Or.inl
      change ((q/2+1 : Nat) : Int) = ((q+1+1)/2 : Nat)
      omega
  · have top : (q+1)/2=q/2+1 := by omega
    have iv : Interval (-(q/2 : Nat)) ((q/2+1 : Nat) : Int) s := by simpa only [Box, top] using full
    have choice : Greedy D s (-((q/2+1 : Nat) : Int)) := by
      refine ⟨?_, ?_, ?_⟩
      · intro used; have h := (iv _).mp used; omega
      · rcases endpoint with h | h | h | h
        · rw [top] at h
          exact allowed_eq previous (by omega) (Or.inl (by omega))
        · exact allowed_eq two (by decide) (Or.inl (by omega))
        · rw [top] at h
          exact allowed_eq next (by omega) (Or.inl (by omega))
        · exact allowed_eq one (by decide) (Or.inl (by omega))
      · intro w wu _
        have outside : ¬(-(q/2 : Nat) ≤ w ∧ w ≤ ((q/2+1 : Nat) : Int)) := fun h => wu ((iv w).mpr h)
        have hw := Int.natAbs_eq w
        constructor
        · rw [Int.natAbs_neg, Int.natAbs_natCast]; omega
        · intro eq; rw [Int.natAbs_neg, Int.natAbs_natCast] at eq; omega
    refine ⟨visit s (-((q/2+1 : Nat) : Int)), .cons choice (.refl _), ?_, ?_⟩
    · intro z
      change (s.used z ∨ z= -((q/2+1 : Nat) : Int)) ↔ _
      rw [iv z]
      omega
    · apply Or.inr; apply Or.inr; apply Or.inr
      change -((q/2+1 : Nat) : Int) = -((q+1)/2 : Nat)
      omega

theorem transition {D : Nat → Prop} {q r : Nat} (s : State)
    (one : D 1) (two : D 2) (hq : 2 ≤ q) (qr : q < r)
    (previous : D q) (next : D r) (gap : ∀ d, q < d → d < r → ¬D d)
    (full : Box q s) (endpoint : Ends q s) :
    ∃ t, Reaches D s t ∧ Box r t ∧ Ends r t := by
  by_cases adjacent : r=q+1
  · subst r
    exact adjacent_transition s one two hq previous next full endpoint
  · exact separated_transition s one two hq (by omega) previous next gap full endpoint

end G06
