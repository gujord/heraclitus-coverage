import CloseBlocks

set_option autoImplicit false

namespace G05
open G01 G03

def Ends (n : Nat) (s : State) : Prop :=
  s.current = ((n+1)/2 : Nat)-(1 : Int) ∨ s.current = 1-(n/2 : Nat) ∨
  s.current = ((n+1)/2 : Nat) ∨ s.current = -(n/2 : Nat)

end G05
