import RepairGlobal

set_option maxRecDepth 20000

example : (G02.finish G01.zeroState (G09.entrance.take 67)).current= -33 := by change (-31 : Int)= -33; decide
