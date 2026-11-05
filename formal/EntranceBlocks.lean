import EntranceTrace

set_option autoImplicit false

namespace G08E
open G01

def zeroState : State := ⟨0,fun z => z=0⟩

def baseWord : List Int := [2,-1,1,-2,-4,-6]

def blockState (t : Nat) : State :=
  ⟨-(t : Int)-1,fun z => -(t : Int)-1≤z ∧ z≤2 ∧ z≠-(t : Int) ∧ z≠-(t : Int)+2⟩

def blockWord (t : Nat) : List Int :=
  [-(t : Int)+2,-(t : Int),-(t : Int)-2,-(t : Int)-4,-(t : Int)-6]

def frontWord (t : Nat) : List Int := [-(t : Int)+2,-(t : Int),-(t : Int)-2]

def boxState (t : Nat) : State := ⟨-(t : Int)-2,fun z => -(t : Int)-2≤z ∧ z≤2⟩

def entranceState (t : Nat) : State :=
  ⟨(t : Int)+1,fun z => (-(t : Int)-2≤z ∧ z≤2) ∨ z=(t : Int)+1⟩

theorem base_short : Valid shortD zeroState baseWord := by
  refine ⟨?_,?_,?_,?_,?_,?_,trivial⟩
  all_goals
    apply short_signed
    · simp [zeroState,visit]
    · simp [zeroState,visit]
    · intro w hw hu
      dsimp [zeroState,visit] at hw hu
      rcases hw with h | h | h | h <;> subst w <;> simp_all [Preferred]

theorem base_state : after zeroState baseWord=blockState 5 := by
  apply G08.state_ext (s:=after zeroState baseWord) (t:=blockState 5) rfl
  intro z
  simp only [after,baseWord,zeroState,visit,blockState]
  omega

theorem base_large {k : Nat} (positive : 1≤k) : Valid (distances k) zeroState baseWord := by
  apply lift_trace (R:=6) base_short (by decide) _ (by omega)
  intro v hv
  simp only [baseWord,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with h | h | h | h | h | h <;> subst v <;> decide

theorem block_short {t : Nat} (large : 5≤t) : Valid shortD (blockState t) (blockWord t) := by
  refine ⟨?_,?_,?_,?_,?_,trivial⟩
  all_goals
    apply short_signed
    · dsimp [blockState,visit]; omega
    · dsimp [blockState,visit]; omega
    · intro w hw hu
      apply negative_preferred
      · omega
      · dsimp [blockState,visit] at hw hu
        omega

theorem block_state {t : Nat} (large : 5≤t) :
    after (blockState t) (blockWord t)=blockState (t+5) := by
  apply G08.state_ext
  · simp only [after,blockWord,visit,blockState]
    omega
  · intro z
    simp only [after,blockWord,visit,blockState]
    omega

theorem block_large {k j : Nat} (positive : 1≤j) (before : j<k) :
    Valid (distances k) (blockState (5*j)) (blockWord (5*j)) := by
  have large : 5≤5*j := by omega
  apply lift_trace (R:=5*j+6) (block_short large) _ _ (by omega)
  · have absolute := Int.natAbs_eq (-(5*j : Nat)-1 : Int)
    dsimp [blockState]
    omega
  · intro v hv
    have absolute := Int.natAbs_eq v
    simp only [blockWord,List.mem_cons,List.not_mem_nil,or_false] at hv
    omega

theorem front_short {t : Nat} (large : 5≤t) : Valid shortD (blockState t) (frontWord t) := by
  have full := block_short large
  exact ⟨full.1,full.2.1,full.2.2.1,trivial⟩

theorem front_state {t : Nat} (large : 5≤t) :
    after (blockState t) (frontWord t)=boxState t := by
  apply G08.state_ext (s:=after (blockState t) (frontWord t)) (t:=boxState t) rfl
  intro z
  simp only [after,frontWord,visit,blockState,boxState]
  omega

theorem front_large {k : Nat} (positive : 1≤k) :
    Valid (distances k) (blockState (5*k)) (frontWord (5*k)) := by
  have full := front_short (show 5≤5*k by omega)
  refine ⟨short_lift full.1 ?_,short_lift full.2.1 ?_,short_lift full.2.2.1 ?_,trivial⟩
  all_goals
    apply negative_shield
    · dsimp [blockState,visit]; omega
    · omega
    · dsimp [blockState,visit]; omega

theorem final_jump {k : Nat} (positive : 1≤k) :
    Greedy (distances k) (boxState (5*k)) ((5*k : Nat)+1 : Int) := by
  have large : 5≤5*k := by omega
  refine ⟨?_,⟨?_,?_⟩,?_⟩
  · dsimp [boxState]; omega
  · have absolute := Int.natAbs_eq ((boxState (5*k)).current-((5*k : Nat)+1 : Int))
    have dist : ((boxState (5*k)).current-((5*k : Nat)+1 : Int)).natAbs=10*k+3 := by
      dsimp [boxState] at *
      omega
    exact Or.inr (Or.inr ⟨0,by omega⟩)
  · have absolute := Int.natAbs_eq ((boxState (5*k)).current-((5*k : Nat)+1 : Int))
    dsimp [boxState] at *
    omega
  · intro w wu wd
    have aw := Int.natAbs_eq w
    have ad := Int.natAbs_eq ((boxState (5*k)).current-w)
    have winner : ((5*k : Nat)+1 : Int) = ((5*k+1 : Nat) : Int) := by omega
    rw [winner]
    apply positive_preferred
    dsimp [boxState] at wu ad wd
    rcases wd.1 with two | three | ⟨r,tail⟩ <;> omega

theorem final_state (t : Nat) :
    visit (boxState t) ((t : Int)+1)=entranceState t := rfl

end G08E
