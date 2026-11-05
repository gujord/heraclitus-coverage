import RepairGlobal

set_option maxRecDepth 20000

example : G09.repairBlock 36=[36,39,-37,38] := by unfold G09.repairBlock; decide
