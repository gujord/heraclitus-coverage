import EntranceBridge
import HoleCount

set_option autoImplicit false

namespace G08E
open G01

def HasHoleCount (U : Int → Prop) (n : Nat) : Prop :=
  ∃ xs : List Int, xs.Nodup ∧ xs.length=n ∧ ∀ z, z∈xs ↔ G08H.LaneHole U z

theorem actual_hole_enumeration {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) :
    (G08H.holesList (5*k)).Nodup ∧ (G08H.holesList (5*k)).length=(5*k-2)/2 ∧
    ∀ z, z∈G08H.holesList (5*k) ↔ G08H.LaneHole (history a (5*k+5)).used z := by
  refine ⟨G08H.holesList_nodup _,G08H.holesList_length _,?_⟩
  intro z
  apply G08H.holesList_mem_iff (show 5≤5*k by omega)
  intro w
  rw [actual_entrance positive rule]
  rfl

theorem actual_hole_count {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) :
    HasHoleCount (history a (5*k+5)).used ((5*k-2)/2) :=
  ⟨G08H.holesList (5*k),actual_hole_enumeration positive rule⟩

theorem unbounded_reachable_holes (C : Nat) :
    ∃ (k : Nat) (a : Nat → Int) (xs : List Int), 1≤k ∧ G08.LiteralWalk (distances k) a ∧
      xs.Nodup ∧ (∀ z, z∈xs ↔ G08H.LaneHole (history a (5*k+5)).used z) ∧ C<xs.length := by
  obtain ⟨a,rule⟩ := literal_exists (C+1)
  have result := actual_hole_enumeration (show 1≤C+1 by omega) rule
  refine ⟨C+1,a,G08H.holesList (5*(C+1)),by omega,rule,result.1,result.2.2,?_⟩
  rw [result.2.1]
  omega

theorem no_uniform_hole_bound :
    ¬∃ C : Nat, ∀ (k : Nat) (a : Nat → Int) (xs : List Int), 1≤k → G08.LiteralWalk (distances k) a →
      xs.Nodup → (∀ z, z∈xs ↔ G08H.LaneHole (history a (5*k+5)).used z) → xs.length≤C := by
  rintro ⟨C,bound⟩
  obtain ⟨k,a,xs,positive,rule,nd,exact,large⟩ := unbounded_reachable_holes C
  have small := bound k a xs positive rule nd exact
  omega

theorem entrance_hole_inside {k : Nat} {a : Nat → Int} {z : Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a)
    (hole : G08H.LaneHole (history a (5*k+5)).used z) : z.natAbs≤5*k+2 := by
  have state : ∀ w, (history a (5*k+5)).used w ↔ G08H.FilledPlus (5*k) w := by
    intro w
    rw [actual_entrance positive rule]
    rfl
  have bounds := (G08H.lane_hole_iff (show 5≤5*k by omega) state z).mp hole
  have absolute := Int.natAbs_eq z
  omega

theorem every_entrance_hole_repaired {k : Nat} {a : Nat → Int}
    (positive : 1≤k) (rule : G08.LiteralWalk (distances k) a) {z : Int}
    (hole : G08H.LaneHole (history a (5*k+5)).used z) :
    ∃ n, 5*k+5<n ∧ n≤70*k+33 ∧ n-(5*k+5)≤65*k+28 ∧ a n=z :=
  omitted_entrance_deadline rule hole.1 (entrance_hole_inside positive rule hole)

end G08E
