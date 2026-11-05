import CofiniteCounting

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G10
open G01

theorem opposite_prefix (a : Nat → Int) (y : Int) (N : Nat) :
    (opposite a y (N+1)).length ≤ (opposite a y N).length+1 := by
  unfold opposite
  rw [List.range_succ, List.filter_append, List.length_append]
  have h := List.length_filter_le (fun i => decide (a i % 2 ≠ y % 2)) [N]
  simp only [List.length_cons, List.length_nil] at h
  omega

def lanePoint (B : Nat) (z : Int) (i : Nat) : Int :=
  2*(i : Int)-(B : Int)+(if (-(B : Int))%2=z%2 then 1 else 0)

theorem lane_point_properties {B i : Nat} (z : Int) (hi : i < B) :
    (lanePoint B z i).natAbs ≤ B ∧ lanePoint B z i % 2 ≠ z%2 := by
  have abs := Int.natAbs_eq (lanePoint B z i)
  unfold lanePoint at *
  split at * <;> constructor <;> omega

theorem lane_point_injective (B : Nat) (z : Int) (i j : Nat)
    (eq : lanePoint B z i = lanePoint B z j) : i=j := by
  unfold lanePoint at eq
  omega

theorem second_missing {D : Nat → Prop} {M N : Nat} {a : Nat → Int} {z : Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a)
    (missing : ¬∃ i, i ≤ N ∧ a i=z) :
    ∃ w : Int, w.natAbs ≤ M+2*z.natAbs+3 ∧ w%2 ≠ z%2 ∧
      ¬∃ i, i ≤ N ∧ a i=w := by
  apply Classical.byContradiction
  intro no
  let B := M+2*z.natAbs+3
  let points := (List.range B).map (lanePoint B z)
  have nd : points.Nodup :=
    map_nodup_injective (lanePoint B z) (lane_point_injective B z) _ List.nodup_range
  have sub : points ⊆ (opposite a z (N+1)).map a := by
    intro w hw
    obtain ⟨j,hj,eq⟩ := List.mem_map.mp hw
    have props := lane_point_properties z (List.mem_range.mp hj)
    rw [eq] at props
    have visited : ∃ i, i ≤ N ∧ a i=w := by
      apply Classical.byContradiction
      intro absent
      exact no ⟨w,props.1,props.2,absent⟩
    obtain ⟨i,hi,iv⟩ := visited
    apply List.mem_map.mpr
    refine ⟨i,(opposite_mem a z (N+1) i).mpr ⟨by omega, ?_⟩,iv⟩
    simpa only [iv] using props.2
  have le := nd.length_le_of_subset sub
  have previous := missing_target_count tail rule missing
  have extra := opposite_prefix a z N
  simp only [points,List.length_map,List.length_range] at le
  dsimp [B] at le
  omega

theorem parity_partition (a : Nat → Int) (z w : Int) (different : w%2 ≠ z%2)
    (xs : List Nat) :
    (xs.filter (fun i => decide (a i%2 ≠ z%2))).length +
    (xs.filter (fun i => decide (a i%2 ≠ w%2))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    by_cases hz : a i%2 ≠ z%2
    · have hw : ¬a i%2 ≠ w%2 := by omega
      simp [hz, hw] at *
      omega
    · have hw : a i%2 ≠ w%2 := by omega
      simp [hz, hw] at *
      omega

theorem omission_bound {D : Nat → Prop} {M N : Nat} {a : Nat → Int} {z : Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a)
    (missing : ¬∃ i, i ≤ N ∧ a i=z) : N ≤ 4*M+6*z.natAbs+8 := by
  obtain ⟨w,bound,parity,absent⟩ := second_missing tail rule missing
  have first := missing_target_count tail rule missing
  have second := missing_target_count tail rule absent
  have partition := parity_partition a z w parity (List.range N)
  change (opposite a z N).length+(opposite a w N).length=(List.range N).length at partition
  rw [List.length_range] at partition
  omega

theorem literal_first_visit {D : Nat → Prop} {M : Nat} {a : Nat → Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a) (z : Int) :
    ∃ n, n ≤ 4*M+6*z.natAbs+9 ∧ a n=z := by
  apply Classical.byContradiction
  intro missing
  have bound := omission_bound tail rule missing
  omega

theorem literal_coverage {D : Nat → Prop} {M : Nat} {a : Nat → Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a) : Coverage a := by
  intro z
  obtain ⟨i,_,eq⟩ := literal_first_visit tail rule z
  refine ⟨i,eq,?_⟩
  intro j same
  exact walk_injective ((G06.literal_iff D a).mp rule).2 j i (same.trans eq.symm)

theorem odd_tail_unbounded {D : Nat → Prop} {M : Nat} (tail : OddTail D M) :
    G02.Unbounded D := by
  intro N
  refine ⟨2*(N+M)+1, by omega, tail _ (by omega) (by omega)⟩

theorem literal_exists (D : Nat → Prop) (M : Nat) (tail : OddTail D M) :
    ∃ a, G06.LiteralRule D a ∧ Coverage a ∧
      ∀ z : Int, ∃ n, n ≤ 4*M+6*z.natAbs+9 ∧ a n=z := by
  obtain ⟨a,rule⟩ := G02.unbounded_exists D (odd_tail_unbounded tail)
  have literal := (G06.literal_iff D a).mpr rule
  exact ⟨a,literal,literal_coverage tail literal,literal_first_visit tail literal⟩

end G10
