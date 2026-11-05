import UniversalLiteral

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G10
open G01

def OddTail (D : Nat → Prop) (M : Nat) : Prop :=
  ∀ d, M ≤ d → d % 2 = 1 → D d

def opposite (a : Nat → Int) (y : Int) (N : Nat) : List Nat :=
  (List.range N).filter (fun i => decide (a i % 2 ≠ y % 2))

theorem opposite_mem (a : Nat → Int) (y : Int) (N i : Nat) :
    i ∈ opposite a y N ↔ i < N ∧ a i % 2 ≠ y % 2 := by
  simp [opposite]

theorem map_nodup_on {α β : Type} (xs : List α) (f : α → β)
    (nd : xs.Nodup)
    (inj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp nd
    rw [List.map_cons, List.nodup_cons]
    constructor
    · intro member
      obtain ⟨y, hy, eq⟩ := List.mem_map.mp member
      have same := inj y (by simp [hy]) x (by simp) eq
      exact fresh (same ▸ hy)
    · apply ih rest
      intro u hu v hv eq
      exact inj u (by simp [hu]) v (by simp [hv]) eq

theorem length_le_code (xs : List Nat) (C : Nat) (f : Nat → Nat)
    (nd : xs.Nodup) (bound : ∀ i ∈ xs, f i < C)
    (inj : ∀ i ∈ xs, ∀ j ∈ xs, f i = f j → i = j) : xs.length ≤ C := by
  have mapped := map_nodup_on xs f nd inj
  have sub : xs.map f ⊆ List.range C := by
    intro v hv
    obtain ⟨i, hi, eq⟩ := List.mem_map.mp hv
    rw [← eq]
    exact List.mem_range.mpr (bound i hi)
  have h := mapped.length_le_of_subset sub
  simpa using h

theorem parity_distance {x y : Int} (different : x % 2 ≠ y % 2) :
    (y-x).natAbs % 2 = 1 := by
  have h := Int.natAbs_eq (y-x)
  omega

theorem missing_forces_small {D : Nat → Prop} {M N : Nat} {a : Nat → Int} {y : Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a)
    (missing : ¬∃ i, i ≤ N ∧ a i = y)
    {i : Nat} (hi : i < N) (parity : a i % 2 ≠ y % 2)
    (far : M ≤ (y-a i).natAbs) : (a (i+1)).natAbs ≤ y.natAbs := by
  have unused : ¬∃ j, j ≤ i ∧ a j=y := by
    rintro ⟨j,hj,eq⟩
    exact missing ⟨j, by omega, eq⟩
  exact ((rule.2 i).2.2 y unused (tail _ far (parity_distance parity))).1

def nearCode (M : Nat) (y x : Int) : Nat := ((x-y+(M : Int))/2).toNat

theorem near_code_bound {M : Nat} {y x : Int} (near : (y-x).natAbs < M) :
    nearCode M y x < M := by
  have h := Int.natAbs_eq (y-x)
  unfold nearCode
  omega

theorem near_code_injective {M : Nat} {y x v : Int}
    (nx : (y-x).natAbs < M) (nv : (y-v).natAbs < M)
    (px : x%2 ≠ y%2) (pv : v%2 ≠ y%2)
    (same : nearCode M y x = nearCode M y v) : x = v := by
  have hx := Int.natAbs_eq (y-x)
  have hv := Int.natAbs_eq (y-v)
  unfold nearCode at same
  omega

def countCode (a : Nat → Int) (M : Nat) (y : Int) (i : Nat) : Nat :=
  if (y-a i).natAbs < M then nearCode M y (a i)
  else M+(a (i+1)+(y.natAbs : Int)).toNat

theorem missing_target_count {D : Nat → Prop} {M N : Nat} {a : Nat → Int} {y : Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a)
    (missing : ¬∃ i, i ≤ N ∧ a i=y) :
    (opposite a y N).length ≤ M+2*y.natAbs+1 := by
  have inj := walk_injective ((G06.literal_iff D a).mp rule).2
  apply length_le_code (opposite a y N) (M+2*y.natAbs+1) (countCode a M y)
  · exact List.Nodup.sublist List.filter_sublist List.nodup_range
  · intro i hi
    obtain ⟨hi, parity⟩ := (opposite_mem a y N i).mp hi
    unfold countCode
    split
    · have h := near_code_bound ‹(y-a i).natAbs < M›
      omega
    · have small := missing_forces_small tail rule missing hi parity (by omega)
      have h := Int.natAbs_eq (a (i+1))
      omega
  · intro i hi j hj same
    obtain ⟨hi, pi⟩ := (opposite_mem a y N i).mp hi
    obtain ⟨hj, pj⟩ := (opposite_mem a y N j).mp hj
    unfold countCode at same
    split at same <;> split at same
    · exact inj i j (near_code_injective ‹_› ‹_› pi pj same)
    · have h := near_code_bound (M:=M) (y:=y) (x:=a i) ‹_›
      omega
    · have h := near_code_bound (M:=M) (y:=y) (x:=a j) ‹_›
      omega
    · have si := missing_forces_small tail rule missing hi pi (by omega)
      have sj := missing_forces_small tail rule missing hj pj (by omega)
      have ai := Int.natAbs_eq (a (i+1))
      have aj := Int.natAbs_eq (a (j+1))
      have eq : a (i+1)=a (j+1) := by omega
      have indices := inj (i+1) (j+1) eq
      omega

end G10
