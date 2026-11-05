import EntranceBlocks

set_option autoImplicit false

namespace G08E
open G01

theorem history_zero {D : Nat → Prop} {a : Nat → Int} (rule : G08.LiteralWalk D a) :
    history a 0=zeroState := by
  apply G08.state_ext rule.1
  intro z
  change (∃ i,i≤0 ∧ a i=z) ↔ z=0
  constructor
  · rintro ⟨i,hi,eq⟩
    have zero : i=0 := by omega
    rw [zero,rule.1] at eq
    exact eq.symm
  · intro eq
    exact ⟨0,Nat.le_refl _,rule.1.trans eq.symm⟩

theorem actual_block_states {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) :
    ∀ j, 1≤j → j≤k → history a (5*j+1)=blockState (5*j) := by
  intro j
  induction j with
  | zero => intro impossible _; omega
  | succ j ih =>
    intro jp jk
    by_cases zero : j=0
    · have base := follow_trace rule (history_zero rule) (base_large positive)
      rw [base_state] at base
      simpa only [zero,baseWord,List.length_cons,List.length_nil] using base
    · have entry := ih (by omega) (by omega)
      have step := follow_trace rule entry (block_large (by omega) (by omega))
      rw [block_state (by omega)] at step
      have index : 5*j+1+(blockWord (5*j)).length=5*(j+1)+1 := by simp [blockWord]; omega
      have radius : 5*j+5=5*(j+1) := by omega
      simpa only [index,radius] using step

theorem actual_box {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) :
    history a (5*k+4)=boxState (5*k) := by
  have entry := actual_block_states positive rule k positive (Nat.le_refl _)
  have step := follow_trace rule entry (front_large positive)
  rw [front_state (by omega)] at step
  have index : 5*k+1+(frontWord (5*k)).length=5*k+4 := by simp [frontWord]
  simpa only [index] using step

theorem actual_entrance {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) :
    history a (5*k+5)=entranceState (5*k) := by
  have box := actual_box positive rule
  have choice := walk_greedy rule (5*k+4)
  rw [box] at choice
  have winner := greedy_unique choice (final_jump positive)
  have step := history_next a (5*k+4)
  rw [box,winner] at step
  have index : 5*k+4+1=5*k+5 := by omega
  simpa only [index,final_state] using step

theorem exact_entrance {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) :
    a (5*k+5)=(5*k : Nat)+1 ∧
    ∀ z, (∃ i,i≤5*k+5 ∧ a i=z) ↔ (-(5*k : Nat)-2≤z ∧ z≤2) ∨ z=(5*k : Nat)+1 := by
  have state := actual_entrance positive rule
  refine ⟨congrArg State.current state,?_⟩
  intro z
  change (history a (5*k+5)).used z ↔ _
  rw [state]
  rfl

end G08E
