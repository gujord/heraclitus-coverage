import Std

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G08H


def FilledPlus (t : Nat) (z : Int) : Prop :=
  (-(t : Int)-2 ≤ z ∧ z ≤ 2) ∨ z=(t : Int)+1

def LaneHole (U : Int → Prop) (z : Int) : Prop :=
  ¬U z ∧ ∃ lo hi : Int,
    U lo ∧ U hi ∧ lo ≤ z ∧ z ≤ hi ∧ lo%2=z%2 ∧ hi%2=z%2

def holesList (t : Nat) : List Int :=
  (List.range ((t-2)/2)).map (fun i => ((2*i+3+t%2 : Nat) : Int))

theorem lane_hole_iff {t : Nat} {U : Int → Prop} (ht : 5 ≤ t)
    (state : ∀ z, U z ↔ FilledPlus t z) (z : Int) :
    LaneHole U z ↔ 2 < z ∧ z < (t : Int)+1 ∧ z%2=((t : Int)+1)%2 := by
  constructor
  · rintro ⟨unused,lo,hi,usedlo,usedhi,bottom,top,_,parity⟩
    have hlo := (state lo).mp usedlo
    have hhi := (state hi).mp usedhi
    have missing : ¬FilledPlus t z := fun hz => unused ((state z).mpr hz)
    unfold FilledPlus at hlo hhi missing
    have lower : -(t : Int)-2 ≤ z := by rcases hlo with hlo | hlo <;> omega
    have above : 2 < z := by
      by_cases yes : 2 < z
      · exact yes
      · exact False.elim (missing (Or.inl ⟨lower,by omega⟩))
    have upper : hi=(t : Int)+1 := by rcases hhi with hhi | hhi <;> omega
    have different : z≠(t : Int)+1 := fun eq => missing (Or.inr eq)
    exact ⟨above,by omega,by omega⟩
  · rintro ⟨above,top,parity⟩
    constructor
    · intro used
      have h := (state z).mp used
      unfold FilledPlus at h
      rcases h with h | h <;> omega
    · refine ⟨z%2,(t : Int)+1,?_,?_,?_,?_,?_,?_⟩
      · apply (state (z%2)).mpr
        exact Or.inl ⟨by omega,by omega⟩
      · exact (state ((t : Int)+1)).mpr (Or.inr rfl)
      · omega
      · omega
      · omega
      · omega

theorem holesList_mem_formula {t : Nat} (ht : 5 ≤ t) (z : Int) :
    z ∈ holesList t ↔ 2 < z ∧ z < (t : Int)+1 ∧ z%2=((t : Int)+1)%2 := by
  simp only [holesList,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨i,hi,eq⟩
    constructor
    · omega
    · constructor <;> omega
  · rintro ⟨above,top,parity⟩
    have nonneg : 0 ≤ z := by omega
    have cast := Int.toNat_of_nonneg nonneg
    refine ⟨(z.toNat-3-t%2)/2,?_,?_⟩ <;> omega

theorem holesList_mem_iff {t : Nat} {U : Int → Prop} (ht : 5 ≤ t)
    (state : ∀ z, U z ↔ FilledPlus t z) (z : Int) :
    z ∈ holesList t ↔ LaneHole U z :=
  (holesList_mem_formula ht z).trans (lane_hole_iff ht state z).symm

theorem map_injective_nodup {α β : Type} (f : α → β)
    (injective : ∀ x y, f x=f y → x=y) (xs : List α) (nd : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh,rest⟩ := List.nodup_cons.mp nd
    rw [List.map_cons,List.nodup_cons]
    refine ⟨?_,ih rest⟩
    intro member
    obtain ⟨y,hy,eq⟩ := List.mem_map.mp member
    have same := injective y x eq
    exact fresh (same ▸ hy)

theorem holesList_nodup (t : Nat) : (holesList t).Nodup := by
  apply map_injective_nodup (fun i => ((2*i+3+t%2 : Nat) : Int))
  · intro i j eq
    omega
  · exact List.nodup_range

theorem holesList_length (t : Nat) : (holesList t).length=(t-2)/2 := by
  simp [holesList]

theorem holes_five : holesList 5=[4] := by decide

theorem holes_ten : holesList 10=[3,5,7,9] := by decide

end G08H
