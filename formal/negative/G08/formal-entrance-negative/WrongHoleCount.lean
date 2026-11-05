import EntranceExamples

open G01 G08E

example : (G08H.holesList 10).length=5 := by
  unfold G08H.holesList
  decide
