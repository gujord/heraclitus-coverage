import CofiniteResults

example : G10.nearCode 5 0 1 ≠ G10.nearCode 5 0 2 := by
  unfold G10.nearCode
  decide
