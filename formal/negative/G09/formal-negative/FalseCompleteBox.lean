import RepairGlobal

set_option maxRecDepth 20000
set_option synthInstance.maxSize 1024

example : (G02.finish G01.zeroState (G09.entrance.take 72)).used 36 := by
  simp only [G09.entrance, List.take, G02.finish, G01.visit, G01.zeroState]
  decide
