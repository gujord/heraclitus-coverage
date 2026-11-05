import MixedBlocks
import OriginalRule

set_option autoImplicit false

namespace G03
open G01

def Box (n : Nat) (st : State) : Prop := Interval (-(n/2 : Nat)) ((n+1)/2 : Nat) st

def boxList (n : Nat) : List Int :=
  (List.range (n+1)).map (fun i : Nat => (i : Int)-(n/2 : Nat))

theorem boxList_mem (n : Nat) (z : Int) :
    z ∈ boxList n ↔ -(n/2 : Nat) ≤ z ∧ z ≤ ((n+1)/2 : Nat) := by
  simp only [boxList, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, bound, eq⟩; omega
  · intro bound
    have eq : (((z+(n/2 : Nat)).toNat : Nat) : Int) = z+(n/2 : Nat) :=
      Int.toNat_of_nonneg (by omega)
    exact ⟨(z+(n/2 : Nat)).toNat, by omega, by omega⟩

theorem box_history_index {D : Nat → Prop} {a : Nat → Int}
    (rule : ∀ n, Greedy D (history a n) (a (n+1))) (m n : Nat)
    (full : Box n (history a m)) : m = n := by
  have hn : (historyList a m).Nodup := map_nodup_injective a (walk_injective rule) _ List.nodup_range
  have bn : (boxList n).Nodup := by
    apply map_nodup_injective (fun i : Nat => (i : Int)-(n/2 : Nat))
    · intro i j eq; omega
    · exact List.nodup_range
  have perm := (List.perm_ext_iff_of_nodup hn bn).mpr (fun z =>
    (historyList_mem a m z).trans ((full z).trans (boxList_mem n z).symm))
  have lengths := perm.length_eq
  simp only [historyList, boxList, List.length_map, List.length_range] at lengths
  omega

theorem reached_box {D : Nat → Prop} {a : Nat → Int}
    (rule : ∀ n, Greedy D (history a n) (a (n+1))) {st t : State} (m n : Nat)
    (start : st = history a m) (path : Reaches D st t) (full : Box n t) :
    t = history a n := by
  obtain ⟨k, _, eq⟩ := reaches_history rule path m start
  have index := box_history_index rule k n (eq ▸ full)
  simpa only [index] using eq

end G03
