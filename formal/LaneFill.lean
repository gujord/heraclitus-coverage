import LaneStep

set_option autoImplicit false

namespace G08
open G01

def laneRun (s : State) (p : Bool) (L n : Nat) : Nat → State
  | 0 => s
  | q+1 => visit (laneRun s p L n q) (point p (L+2*(n-(q+1))))

theorem run_current {s : State} {p : Bool} {L n : Nat}
    (current : s.current = point p (L+2*n)) (q : Nat) :
    (laneRun s p L n q).current = point p (L+2*(n-q)) := by
  cases q with
  | zero => simpa only [laneRun,Nat.sub_zero] using current
  | succ q => rfl

theorem run_used {s : State} {p : Bool} {L n q : Nat} (qn : q ≤ n) (z : Int) :
    (laneRun s p L n q).used z ↔
      s.used z ∨ ∃ i, n-q ≤ i ∧ i < n ∧ z = point p (L+2*i) := by
  induction q with
  | zero =>
    simp only [laneRun,Nat.sub_zero]
    constructor
    · exact Or.inl
    · rintro (old | ⟨i,lo,hi,_⟩)
      · exact old
      · omega
  | succ q ih =>
    change ((laneRun s p L n q).used z ∨ z=point p (L+2*(n-(q+1)))) ↔ _
    rw [ih (by omega)]
    constructor
    · rintro ((old | ⟨i,lo,hi,eq⟩) | eq)
      · exact Or.inl old
      · exact Or.inr ⟨i,by omega,hi,eq⟩
      · exact Or.inr ⟨n-(q+1),Nat.le_refl _,by omega,eq⟩
    · rintro (old | ⟨i,lo,hi,eq⟩)
      · exact Or.inl (Or.inl old)
      · by_cases high : n-q ≤ i
        · exact Or.inl (Or.inr ⟨i,high,hi,eq⟩)
        · have same : i=n-(q+1) := by omega
          exact Or.inr (by simpa only [same] using eq)

theorem run_interior {s : State} {p : Bool} {L B n q : Nat}
    (bound : L+2*n ≤ B) (interior : Interior p L B n s) (qn : q ≤ n) :
    Interior p L B (n-q) (laneRun s p L n q) := by
  induction q with
  | zero => simpa only [laneRun,Nat.sub_zero] using interior
  | succ q ih =>
    have prev := ih (by omega)
    have count : n-q = (n-(q+1))+1 := by omega
    rw [count] at prev
    exact interior_visit (by omega) prev

theorem run_greedy {D : Nat → Prop} {s : State} {p : Bool} {L B n q : Nat}
    (even : OnlyEvenTwo D) (positive : 1 ≤ L) (bound : L+2*n ≤ B)
    (interior : Interior p L B n s) (current : s.current = point p (L+2*n))
    (qn : q < n) :
    Greedy D (laneRun s p L n q) (point p (L+2*(n-(q+1)))) := by
  have prev := run_interior bound interior (show q ≤ n by omega)
  have cur := run_current current q
  have count : n-q = (n-(q+1))+1 := by omega
  rw [count] at prev cur
  exact inward_greedy even positive (by omega) prev cur

theorem run_complete_iff {s : State} {p : Bool} {L B n q : Nat}
    (bound : L+2*n ≤ B) (interior : Interior p L B n s) (qn : q ≤ n) :
    (∀ z, z.natAbs ≤ B → (laneRun s p L n q).used z) ↔ q=n := by
  classical
  have frame := run_interior bound interior qn
  constructor
  · intro complete
    apply Classical.byContradiction
    intro ne
    have un : ¬(laneRun s p L n q).used (point p L) := by
      apply (frame _ (by rw [point_abs]; omega)).mpr
      exact ⟨0,by omega,by simp⟩
    exact un (complete _ (by rw [point_abs]; omega))
  · intro same z zb
    apply Classical.byContradiction
    intro un
    obtain ⟨i,hi,_⟩ := (frame z zb).mp un
    omega

def FiniteUsed (s : State) : Prop := ∃ xs : List Int, ∀ z, s.used z ↔ z ∈ xs

theorem finite_visit {s : State} (finite : FiniteUsed s) (v : Int) :
    FiniteUsed (visit s v) := by
  obtain ⟨xs,h⟩ := finite
  refine ⟨v::xs,?_⟩
  intro z
  change (s.used z ∨ z=v) ↔ z ∈ v::xs
  rw [h]
  simp only [List.mem_cons]
  exact or_comm

theorem run_finite {s : State} {p : Bool} {L n : Nat}
    (finite : FiniteUsed s) (q : Nat) : FiniteUsed (laneRun s p L n q) := by
  induction q with
  | zero => exact finite
  | succ q ih => exact finite_visit ih _

end G08
