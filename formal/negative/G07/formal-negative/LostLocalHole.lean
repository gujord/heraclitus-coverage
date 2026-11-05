import TripleObstruction
example : (G02.finish G07.seed G07.inwardPrefix).used (-7) := by dsimp [G07.inwardPrefix, G02.finish, G01.visit, G07.seed]; decide
