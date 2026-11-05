import Global

set_option autoImplicit false

namespace G01


theorem difference_symm (x y : Int) : (x-y).natAbs = (y-x).natAbs := by
  have eq : x-y = -(y-x) := by omega
  rw [eq, Int.natAbs_neg]

end G01
