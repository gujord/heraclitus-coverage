import CofiniteResults

example : (G10.opposite (fun i => 2*(i : Int)+1) 0 2).length ≤
    (G10.opposite (fun i => 2*(i : Int)+1) 0 1).length := by
  unfold G10.opposite
  decide
