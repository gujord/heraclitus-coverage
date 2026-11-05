import LaneExamples

open G01 G08

example : ¬(visit (visit (sampleState true) 3) 1).used (-1) := by
  unfold visit sampleState sampleUsed
  dsimp
  decide
