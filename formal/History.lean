import BlockGeometry

set_option autoImplicit false

namespace G01


theorem history_zero (a : Nat → Int) (zero : a 0 = 0) : history a 0 = zeroState := by
  apply state_ext zero
  intro z
  change (∃ i, i ≤ 0 ∧ a i = z) ↔ z = 0
  constructor
  · rintro ⟨i, hi, eq⟩
    have iz : i = 0 := by omega
    simpa only [iz, zero] using eq.symm
  · intro eq
    exact ⟨0, Nat.le_refl _, by rw [zero, eq]⟩

theorem history_succ (a : Nat → Int) (n : Nat) :
    visit (history a n) (a (n+1)) = history a (n+1) := by
  refine state_ext (s := visit (history a n) (a (n+1))) (t := history a (n+1)) rfl ?_
  intro z
  change ((∃ i, i ≤ n ∧ a i = z) ∨ z = a (n+1)) ↔ (∃ i, i ≤ n+1 ∧ a i = z)
  constructor
  · rintro (⟨i, hi, eq⟩ | eq)
    · exact ⟨i, by omega, eq⟩
    · exact ⟨n+1, Nat.le_refl _, eq.symm⟩
  · rintro ⟨i, hi, eq⟩
    by_cases small : i ≤ n
    · exact Or.inl ⟨i, small, eq⟩
    · have same : i = n+1 := by omega
      exact Or.inr (by simpa only [same] using eq.symm)

theorem walk_injective {D : Nat → Prop} {a : Nat → Int}
    (rule : ∀ n, Greedy D (history a n) (a (n+1))) :
    ∀ i j, a i = a j → i = j := by
  intro i j eq
  by_cases ij : i < j
  · have unused := (rule (j-1)).1
    have index : j-1+1 = j := by omega
    rw [index] at unused
    exact False.elim (unused ⟨i, by omega, eq⟩)
  · by_cases ji : j < i
    · have unused := (rule (i-1)).1
      have index : i-1+1 = i := by omega
      rw [index] at unused
      exact False.elim (unused ⟨j, by omega, eq.symm⟩)
    · omega

theorem reaches_history {D : Nat → Prop} {a : Nat → Int}
    (rule : ∀ n, Greedy D (history a n) (a (n+1)))
    {s t : State} (path : Reaches D s t) (n : Nat) (start : s = history a n) :
    ∃ m, n ≤ m ∧ t = history a m := by
  induction path generalizing n with
  | refl => exact ⟨n, Nat.le_refl _, start⟩
  | @cons s t v choice _ ih =>
    have equal : v = a (n+1) := by
      apply greedy_unique (s := history a n)
      · simpa only [start] using choice
      · exact rule n
    have next : visit s v = history a (n+1) := by
      rw [start, equal, history_succ]
    obtain ⟨m, bound, endpoint⟩ := ih (n+1) next
    exact ⟨m, by omega, endpoint⟩

theorem map_nodup_injective {α β : Type} (f : α → β)
    (injective : ∀ x y, f x = f y → x = y) (xs : List α) (nodup : xs.Nodup) :
    (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨fresh, rest⟩ := List.nodup_cons.mp nodup
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih rest⟩
    intro member
    obtain ⟨y, ym, eq⟩ := List.mem_map.mp member
    have same := injective y x eq
    exact fresh (same ▸ ym)

def historyList (a : Nat → Int) (n : Nat) : List Int := (List.range (n+1)).map a

theorem historyList_mem (a : Nat → Int) (n : Nat) (z : Int) :
    z ∈ historyList a n ↔ (history a n).used z := by
  simp only [historyList, List.mem_map, List.mem_range, history]
  constructor
  · rintro ⟨i, hi, eq⟩; exact ⟨i, by omega, eq⟩
  · rintro ⟨i, hi, eq⟩; exact ⟨i, by omega, eq⟩

end G01
