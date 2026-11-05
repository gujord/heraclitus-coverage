import RepairGlobal

set_option maxRecDepth 20000

example : (G02.finish G01.zeroState (G09.entrance.take 64)).current=34 := by change (35 : Int)=34; decide
