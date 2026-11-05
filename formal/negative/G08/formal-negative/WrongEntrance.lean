import LaneExamples

open G01 G08

example : Allowed onlyTwo wrongEntrance.current 3 := by
  unfold Allowed onlyTwo wrongEntrance
  dsimp
  decide
