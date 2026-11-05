import EntranceResults

set_option autoImplicit false

namespace G08E
open G01

theorem boundary_one {a : Nat → Int} (rule : G08.LiteralWalk (distances 1) a) :
    a 10=6 ∧ ∀ z, G08H.LaneHole (history a 10).used z ↔ z=4 := by
  have entry := exact_entrance (by decide : 1≤1) rule
  have holes := (actual_hole_enumeration (by decide : 1≤1) rule).2.2
  refine ⟨entry.1,?_⟩
  intro z
  have h := (holes z).symm
  change G08H.LaneHole (history a 10).used z ↔ z∈G08H.holesList 5 at h
  simpa only [G08H.holes_five,List.mem_cons,List.not_mem_nil,or_false] using h

theorem boundary_two {a : Nat → Int} (rule : G08.LiteralWalk (distances 2) a) :
    a 15=11 ∧ ∀ z, G08H.LaneHole (history a 15).used z ↔ z∈([3,5,7,9] : List Int) := by
  have entry := exact_entrance (by decide : 1≤2) rule
  have holes := (actual_hole_enumeration (by decide : 1≤2) rule).2.2
  refine ⟨entry.1,?_⟩
  intro z
  have h := (holes z).symm
  change G08H.LaneHole (history a 15).used z ↔ z∈G08H.holesList 10 at h
  simpa only [G08H.holes_ten] using h

theorem boundary_previous_index {a : Nat → Int} (rule : G08.LiteralWalk (distances 1) a) :
    a 9=(-7) := congrArg State.current (actual_box (by decide) rule)

theorem endpoint_minus_seven_used {a : Nat → Int} (rule : G08.LiteralWalk (distances 1) a) :
    ∃ i,i≤10 ∧ a i=(-7) := by
  apply (exact_entrance (by decide) rule).2 (-7) |>.mpr
  exact Or.inl ⟨by decide,by decide⟩

def alteredThreshold (d : Nat) : Prop := d=2 ∨ d=3 ∨ ∃ i, d=12+2*i

def before_last_short : State := after (blockState 5) [-3,-5]

theorem altered_threshold_competitor :
    ¬before_last_short.used 7 ∧ Allowed alteredThreshold before_last_short.current 7 ∧
      ¬Preferred (-7) 7 := by
  refine ⟨?_,⟨?_,by decide⟩,?_⟩
  · simp [before_last_short,after,blockState,visit]
  · exact Or.inr (Or.inr ⟨0,rfl⟩)
  · unfold Preferred
    decide

theorem altered_threshold_breaks_short_choice :
    ¬Greedy alteredThreshold before_last_short (-7) := by
  intro choice
  have bad := altered_threshold_competitor
  exact bad.2.2 (choice.2.2 7 bad.1 bad.2.1)

end G08E
