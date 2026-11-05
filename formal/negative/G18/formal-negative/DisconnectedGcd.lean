import ResidueResults

example : ([2,4] : List Nat).foldl Nat.gcd 6 = 1 := by decide
