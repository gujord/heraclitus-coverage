import RepairBlocks

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace G09
open G01 G02

def distances (d : Nat) : Prop := d=1 ∨ d=3 ∨ d=10 ∨ (64≤d ∧ d%4=0)

def entrance : List Int :=
  [1,2,-1,-2,-3,-4,-5,5,4,3,6,7,8,9,10,11,12,13,14,15,16,17,18,19,
   20,21,22,23,24,25,26,27,28,29,30,31,32,-32,-22,-12,-9,-6,-7,-8,-11,-10,
   -13,-14,-15,-16,-17,-18,-19,-20,-21,-24,-23,-26,-25,-28,-27,-30,-29,35,
   -33,-34,-31,33,34,37,-35,-36]

instance distances_decidable (d : Nat) : Decidable (distances d) := by
  unfold distances
  infer_instance

instance zero_used_decidable : DecidablePred zeroState.used := fun z =>
  inferInstanceAs (Decidable (z=0))

instance visit_used_decidable (s : State) [DecidablePred s.used] (v : Int) :
    DecidablePred (visit s v).used := fun z =>
  inferInstanceAs (Decidable (s.used z ∨ z=v))

instance finite_greedy_decidable (s : State) [DecidablePred s.used] (v : Int) :
    Decidable (FiniteGreedy distances s v) := by
  unfold FiniteGreedy Allowed Preferred
  infer_instance

instance certificate_decidable (s : State) [DecidablePred s.used] (vs : List Int) :
    Decidable (Certificate distances s vs) :=
  match vs with
  | [] => isTrue True.intro
  | v::vs =>
    have : Decidable (Certificate distances (visit s v) vs) := certificate_decidable (visit s v) vs
    inferInstanceAs (Decidable (FiniteGreedy distances s v ∧ Certificate distances (visit s v) vs))

theorem entrance_certificate : Certificate distances zeroState entrance := by
  decide

theorem certificate_take {D : Nat → Prop} (n : Nat) (vs : List Int) (s : State)
    (cert : Certificate D s vs) : Certificate D s (vs.take n) := by
  induction n generalizing vs s with
  | zero => trivial
  | succ n ih =>
    cases vs with
    | nil => trivial
    | cons v vs => exact ⟨cert.1, ih vs (visit s v) cert.2⟩

theorem entrance_history {a : Nat → Int} (rule : Rule distances a) (n : Nat) (hn : n≤72) :
    history a n = finish zeroState (entrance.take n) := by
  have cert := certificate_take n entrance zeroState entrance_certificate
  have result := certificate_from_zero rule (entrance.take n) cert
  have len : (entrance.take n).length=n := by
    rw [List.length_take]
    have h : entrance.length=72 := by rfl
    rw [h]; omega
  simpa only [len] using result

theorem entrance_frontier {a : Nat → Int} (rule : Rule distances a) : Frontier 36 (history a 72) := by
  rw [entrance_history rule 72 (by decide)]
  constructor
  · rfl
  · intro z
    simp only [entrance, List.take, finish, visit, zeroState]
    omega

theorem first_checkpoint_frame {a : Nat → Int} (rule : Rule distances a) (z : Int) :
    (history a 64).used z ↔ (-32≤z ∧ z≤32 ∧ z≠ -31) ∨ z=35 := by
  rw [entrance_history rule 64 (by decide)]
  simp only [entrance, List.take, finish, visit, zeroState]
  omega

theorem second_checkpoint_frame {a : Nat → Int} (rule : Rule distances a) (z : Int) :
    (history a 68).used z ↔ (-34≤z ∧ z<34) ∨ z=35 := by
  rw [entrance_history rule 68 (by decide)]
  simp only [entrance, List.take, finish, visit, zeroState]
  omega

theorem original_hole {a : Nat → Int} (rule : Rule distances a) :
    a 64=35 ∧ ¬(history a 64).used (-31) ∧ (history a 64).used 35 ∧ a 67= -31 := by
  have h64 := entrance_history rule 64 (by decide)
  have h67 := entrance_history rule 67 (by decide)
  have c64 := congrArg State.current h64
  have c67 := congrArg State.current h67
  refine ⟨c64, ?_, ?_, c67⟩
  · rw [h64]; simp [entrance, List.take, finish, visit, zeroState]
  · rw [h64]; simp [entrance, List.take, finish, visit, zeroState]

theorem second_hole {a : Nat → Int} (rule : Rule distances a) :
    ¬(history a 68).used 34 ∧ a 69=34 := by
  have h68 := entrance_history rule 68 (by decide)
  have h69 := entrance_history rule 69 (by decide)
  constructor
  · rw [h68]; simp [entrance, List.take, finish, visit, zeroState]
  · exact congrArg State.current h69

end G09
