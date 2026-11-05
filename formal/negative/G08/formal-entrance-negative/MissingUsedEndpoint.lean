import EntranceExamples

open G01 G08E

example : ¬(G08E.entranceState 5).used (-7) := by
  unfold G08E.entranceState
  dsimp
  decide
