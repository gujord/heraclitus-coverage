import History

set_option autoImplicit false

namespace G03
open G01

theorem reaches_used {D : Nat → Prop} {s t : State} (path : Reaches D s t) :
    ∀ z, s.used z → t.used z := by
  induction path with
  | refl => exact fun _ h => h
  | cons _ _ ih => exact fun z h => ih z (Or.inl h)

def Inside (B : Nat) (s t : State) : Prop :=
  s.current = t.current ∧ ∀ z, z.natAbs < B → (s.used z ↔ t.used z)

theorem inside_visit {B : Nat} {s t : State} (same : Inside B s t) (v : Int) :
    Inside B (visit s v) (visit t v) := by
  refine ⟨rfl, ?_⟩
  intro z zb
  change (s.used z ∨ z=v) ↔ (t.used z ∨ z=v)
  rw [same.2 z zb]

theorem inside_greedy {D : Nat → Prop} {B : Nat} {s t : State} {v : Int}
    (same : Inside B s t) (small : v.natAbs < B) (choice : Greedy D s v) :
    Greedy D t v := by
  refine ⟨fun used => choice.1 ((same.2 v small).mpr used), ?_, ?_⟩
  · simpa only [Allowed, same.1] using choice.2.1
  · intro w wu wd
    by_cases wb : w.natAbs < B
    · apply choice.2.2 w (fun h => wu ((same.2 w wb).mp h))
      simpa only [Allowed, same.1] using wd
    · exact ⟨by omega, fun eq => by omega⟩

theorem transfer_inside {D : Nat → Prop} {B : Nat} {s u : State}
    (path : Reaches D s u) (bound : ∀ z, u.used z → z.natAbs ≤ B)
    (edge : ∀ z, z.natAbs = B → s.used z) (t : State) (same : Inside B s t) :
    ∃ v, Reaches D t v ∧ Inside B u v ∧
      ∀ z, B ≤ z.natAbs → (v.used z ↔ t.used z) := by
  induction path generalizing t with
  | refl s => exact ⟨t, .refl t, same, fun _ _ => Iff.rfl⟩
  | @cons s u x choice path ih =>
    have xu : u.used x := reaches_used path x (Or.inr rfl)
    have xb : x.natAbs < B := by
      have le := bound x xu
      have ne : x.natAbs ≠ B := fun eq => choice.1 (edge x eq)
      omega
    have edge' : ∀ z, z.natAbs = B → (visit s x).used z := fun z hz => Or.inl (edge z hz)
    obtain ⟨v, rest, final, outside⟩ := ih bound edge' (visit t x) (inside_visit same x)
    refine ⟨v, .cons (inside_greedy same xb choice) rest, final, ?_⟩
    intro z zb
    rw [outside z zb]
    change (t.used z ∨ z=x) ↔ t.used z
    have ne : z ≠ x := by intro eq; subst z; omega
    simp only [ne, or_false]

theorem shielded_filling (D : Nat → Prop) (p : Bool) (L B : Nat) (s : State)
    (one : D 1) (two : D 2) (hL : 1 ≤ L) (hLB : L < B)
    (current : s.current = point p B)
    (interior : ∀ z, z.natAbs < B →
      (s.used z ↔ ¬∃ r, L ≤ r ∧ r < B ∧ z = point p r)) :
    ∃ t, Reaches D s t ∧ t.current = point p (B-1) ∧
      ∀ z, t.used z ↔ z.natAbs < B ∨ s.used z := by
  let model := entranceState p L B
  obtain ⟨u, path, complete, endpoint⟩ :=
    one_side_filling D p L B model one two hL hLB (entranceState_spec p L B)
  have edge : ∀ z, z.natAbs = B → model.used z := by
    intro z zb
    refine ⟨by omega, ?_⟩
    rintro ⟨r, _, rb, eq⟩
    have ab := point_abs p r
    rw [←eq] at ab
    omega
  have same : Inside B model s := by
    refine ⟨current.symm, ?_⟩
    intro z zb
    change (z.natAbs ≤ B ∧ _) ↔ s.used z
    rw [interior z zb]
    simp only [show z.natAbs ≤ B by omega, true_and]
  obtain ⟨t, realpath, final, outside⟩ :=
    transfer_inside path (fun z h => (complete z).mp h) edge s same
  refine ⟨t, realpath, final.1 ▸ endpoint, ?_⟩
  intro z
  by_cases zb : z.natAbs < B
  · have used := (final.2 z zb).mp ((complete z).mpr (by omega))
    simp only [used, zb, true_or]
  · rw [outside z (by omega)]
    simp only [zb, false_or]

end G03
