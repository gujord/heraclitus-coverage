import RepairGlobal

set_option maxRecDepth 20000

example : G09.distances 73 := by unfold G09.distances; decide
