import Std

set_option autoImplicit false

namespace G01


structure State where
  current : Int
  used : Int → Prop

def Preferred (v w : Int) : Prop :=
  v.natAbs ≤ w.natAbs ∧ (v.natAbs = w.natAbs → w ≤ v)

def Allowed (D : Nat → Prop) (c v : Int) : Prop :=
  D (c - v).natAbs ∧ 0 < (c - v).natAbs

def Greedy (D : Nat → Prop) (s : State) (v : Int) : Prop :=
  ¬s.used v ∧ Allowed D s.current v ∧
    ∀ w, ¬s.used w → Allowed D s.current w → Preferred v w

def visit (s : State) (v : Int) : State :=
  ⟨v, fun z => s.used z ∨ z = v⟩

inductive Reaches (D : Nat → Prop) : State → State → Prop
  | refl (s) : Reaches D s s
  | cons {s t v} : Greedy D s v → Reaches D (visit s v) t → Reaches D s t

theorem Reaches.trans {D : Nat → Prop} {s t u : State}
    (h : Reaches D s t) (k : Reaches D t u) : Reaches D s u := by
  induction h with
  | refl => exact k
  | cons choice _ ih => exact .cons choice (ih k)

def rank (z : Int) : Nat := 2 * z.natAbs + if 0 ≤ z then 0 else 1

theorem rank_order (v w : Int) : rank v ≤ rank w ↔ Preferred v w := by
  have av := Int.natAbs_eq v
  have aw := Int.natAbs_eq w
  by_cases hv : 0 ≤ v <;> by_cases hw : 0 ≤ w
  all_goals simp only [rank, hv, hw, ite_true, ite_false, Preferred]; omega

theorem least_nat (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases smaller : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hp⟩ := smaller
      exact ih m hm hp
    · refine ⟨n, hn, ?_⟩
      intro m hm
      by_cases hle : n ≤ m
      · exact hle
      · exact False.elim (smaller ⟨m, by omega, hm⟩)

theorem greedy_exists {D : Nat → Prop} {s : State}
    (h : ∃ v, ¬s.used v ∧ Allowed D s.current v) : ∃ v, Greedy D s v := by
  obtain ⟨v, hv, hd⟩ := h
  obtain ⟨n, ⟨w, hw, hwd, he⟩, least⟩ :=
    least_nat (fun n => ∃ w, ¬s.used w ∧ Allowed D s.current w ∧ rank w = n)
      ⟨rank v, v, hv, hd, rfl⟩
  refine ⟨w, hw, hwd, ?_⟩
  intro x hx hxd
  apply (rank_order w x).mp
  rw [he]
  exact least (rank x) ⟨x, hx, hxd, rfl⟩

theorem greedy_unique {D : Nat → Prop} {s : State} {v w : Int}
    (hv : Greedy D s v) (hw : Greedy D s w) : v = w := by
  obtain ⟨av, tv⟩ := hv.2.2 w hw.1 hw.2.1
  obtain ⟨aw, tw⟩ := hw.2.2 v hv.1 hv.2.1
  have eq : v.natAbs = w.natAbs := by omega
  have vbound := tv eq
  have wbound := tw eq.symm
  omega

def point (p : Bool) (r : Nat) : Int := if p then (r : Int) else -(r : Int)

theorem point_abs (p : Bool) (r : Nat) : (point p r).natAbs = r := by
  cases p <;> simp [point] <;> omega

theorem point_injective (p : Bool) (r t : Nat) : point p r = point p t ↔ r = t := by
  cases p <;> simp [point] <;> omega

theorem point_cases (p : Bool) (z : Int) :
    z = point p z.natAbs ∨ z = point (!p) z.natAbs := by
  have h := Int.natAbs_eq z
  cases p <;> simp only [point, Bool.false_eq_true, Bool.not_false,
    Bool.not_true, ite_false, ite_true] <;> omega

theorem point_sub_distance (p : Bool) (r k : Nat) (hk : k ≤ r) :
    (point p r - point p (r-k)).natAbs = k := by
  cases p
  · have eq : point false r - point false (r-k) = -(k : Int) := by simp [point]; omega
    rw [eq]; simp
  · have eq : point true r - point true (r-k) = (k : Int) := by simp [point]; omega
    rw [eq]; simp

theorem point_add_distance (p : Bool) (r k : Nat) :
    (point p r - point p (r+k)).natAbs = k := by
  cases p
  · have eq : point false r - point false (r+k) = (k : Int) := by simp [point]; omega
    rw [eq]; simp
  · have eq : point true r - point true (r+k) = -(k : Int) := by simp [point]; omega
    rw [eq]; simp

def history (a : Nat → Int) (n : Nat) : State :=
  ⟨a n, fun z => ∃ i, i ≤ n ∧ a i = z⟩

def Coverage (a : Nat → Int) : Prop :=
  ∀ z, ∃ i, a i = z ∧ ∀ j, a j = z → j = i

end G01
