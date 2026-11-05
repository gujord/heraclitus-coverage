import Semantics

set_option autoImplicit false

namespace G01


structure Frame (p : Bool) (L B : Nat) (s : State) : Prop where
  bounded : ∀ z, s.used z → z.natAbs ≤ B
  opposite : ∀ t, t ≤ B → s.used (point (!p) t)
  low : ∀ t, t < L → s.used (point p t)

def Sparse (p : Bool) (L B : Nat) (s : State) : Prop :=
  ∀ t, L < t → t < B → s.used (point p t) → ¬s.used (point p (t+1))

theorem unused_active {p : Bool} {L B : Nat} {s : State}
    (fr : Frame p L B s) {z : Int} (hu : ¬s.used z) (hb : z.natAbs ≤ B) :
    z = point p z.natAbs ∧ L ≤ z.natAbs := by
  have active : z = point p z.natAbs := by
    rcases point_cases p z with h | h
    · exact h
    · exact False.elim (hu (h ▸ fr.opposite z.natAbs hb))
  refine ⟨active, ?_⟩
  by_cases h : L ≤ z.natAbs
  · exact h
  · exact False.elim (hu (active ▸ fr.low z.natAbs (by omega)))

theorem frame_visit {p : Bool} {L B q : Nat} {s : State}
    (fr : Frame p L B s) (hq : q ≤ B) : Frame p L B (visit s (point p q)) := by
  constructor
  · intro z hz
    rcases hz with old | same
    · exact fr.bounded z old
    · subst z; simpa only [point_abs] using hq
  · intro t ht; exact Or.inl (fr.opposite t ht)
  · intro t ht; exact Or.inl (fr.low t ht)

theorem descent_step {D : Nat → Prop} {p : Bool} {L B r : Nat} {s : State}
    (one : D 1) (two : D 2) (hL : 1 ≤ L) (hr : L < r) (hrB : r ≤ B)
    (fr : Frame p L B s) (hc : s.current = point p r)
    (holes : ∀ t, L ≤ t → t < r → ¬s.used (point p t)) :
    ∃ q, L ≤ q ∧ q < r ∧ (q = L ∨ q+1 < r) ∧ Greedy D s (point p q) := by
  have unused1 := holes (r-1) (by omega) (by omega)
  have allowed1 : Allowed D s.current (point p (r-1)) := by
    unfold Allowed
    rw [hc, point_sub_distance p r 1 (by omega)]
    exact ⟨one, by decide⟩
  obtain ⟨v, choice⟩ := greedy_exists ⟨point p (r-1), unused1, allowed1⟩
  have bound := (choice.2.2 (point p (r-1)) unused1 allowed1).1
  rw [point_abs] at bound
  obtain ⟨active, low⟩ := unused_active fr choice.1 (by omega)
  refine ⟨v.natAbs, low, by omega, ?_, ?_⟩
  · by_cases gap : L+2 ≤ r
    · have unused2 := holes (r-2) (by omega) (by omega)
      have allowed2 : Allowed D s.current (point p (r-2)) := by
        unfold Allowed
        rw [hc, point_sub_distance p r 2 (by omega)]
        exact ⟨two, by decide⟩
      have bound2 := (choice.2.2 (point p (r-2)) unused2 allowed2).1
      rw [point_abs] at bound2
      exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · rw [←active]; exact choice

theorem sparse_descent_visit {p : Bool} {L B r q : Nat} {s : State}
    (sp : Sparse p L B s)
    (holes : ∀ t, L ≤ t → t < r → ¬s.used (point p t))
    (_ql : L ≤ q) (qr : q < r) (gap : q = L ∨ q+1 < r) :
    Sparse p L B (visit s (point p q)) := by
  intro t tl tb ht ht1
  rcases ht with old | same
  · rcases ht1 with old1 | same1
    · exact sp t tl tb old old1
    · have eq := (point_injective p (t+1) q).mp same1
      exact holes t (by omega) (by omega) old
  · have eq := (point_injective p t q).mp same
    rcases ht1 with old1 | same1
    · exact holes (t+1) (by omega) (by omega) old1
    · have eq1 := (point_injective p (t+1) q).mp same1
      omega

theorem descent_finish {D : Nat → Prop} {p : Bool} {L B : Nat}
    (one : D 1) (two : D 2) (hL : 1 ≤ L)
    (r : Nat) (s : State) (lr : L ≤ r) (rb : r ≤ B)
    (fr : Frame p L B s) (sp : Sparse p L B s)
    (hc : s.current = point p r)
    (holes : ∀ t, L ≤ t → t < r → ¬s.used (point p t))
    (top : s.used (point p B)) :
    ∃ t, Reaches D s t ∧ Frame p L B t ∧ Sparse p L B t ∧
      t.current = point p L ∧ t.used (point p B) := by
  induction r using Nat.strongRecOn generalizing s with
  | ind r ih =>
    by_cases done : r = L
    · subst r; exact ⟨s, .refl s, fr, sp, hc, top⟩
    obtain ⟨q, ql, qr, gap, choice⟩ :=
      descent_step one two hL (by omega) rb fr hc holes
    have fr' := frame_visit fr (show q ≤ B by omega)
    have sp' := sparse_descent_visit sp holes ql qr gap
    have holes' : ∀ t, L ≤ t → t < q → ¬(visit s (point p q)).used (point p t) := by
      intro t tl tq ht
      rcases ht with old | same
      · exact holes t tl (by omega) old
      · have eq := (point_injective p t q).mp same
        omega
    obtain ⟨t, path, ft, st, ct, bt⟩ :=
      ih q qr (visit s (point p q)) ql (by omega) fr' sp' rfl holes' (Or.inl top)
    exact ⟨t, .cons choice path, ft, st, ct, bt⟩

theorem active_min_greedy {D : Nat → Prop} {p : Bool} {L B q : Nat} {s : State}
    (fr : Frame p L B s) (qb : q ≤ B)
    (dense : ∀ t, t < q → s.used (point p t))
    (unused : ¬s.used (point p q)) (allowed : Allowed D s.current (point p q)) :
    Greedy D s (point p q) := by
  refine ⟨unused, allowed, ?_⟩
  intro w wu _
  have lower : q ≤ w.natAbs := by
    by_cases h : q ≤ w.natAbs
    · exact h
    · obtain ⟨active, _⟩ := unused_active fr wu (by omega)
      exact False.elim (wu (active ▸ dense w.natAbs (by omega)))
  constructor
  · simpa only [point_abs] using lower
  · intro equal
    rw [point_abs] at equal
    obtain ⟨active, _⟩ := unused_active fr wu (by omega)
    have eq : w = point p q := by simpa only [←equal] using active
    rw [eq]
    exact Int.le_refl _

theorem fill_step {D : Nat → Prop} {p : Bool} {L B r : Nat} {s : State}
    (one : D 1) (two : D 2) (fr : Frame p L B s)
    (hc : s.current = point p r) (room : r+1 < B)
    (dense : ∀ t, t ≤ r → s.used (point p t))
    (sp : Sparse p r B s) (top : s.used (point p B)) :
    ∃ q, r < q ∧ q < B ∧ Greedy D s (point p q) ∧
      (∀ t, t ≤ q → (visit s (point p q)).used (point p t)) ∧
      Sparse p q B (visit s (point p q)) := by
  classical
  have advance (q : Nat) (rq : r < q) (qb : q < B)
      (middle : ∀ t, r < t → t < q → s.used (point p t))
      (un : ¬s.used (point p q)) (ad : Allowed D s.current (point p q)) :
      Greedy D s (point p q) ∧
        (∀ t, t ≤ q → (visit s (point p q)).used (point p t)) ∧
        Sparse p q B (visit s (point p q)) := by
    refine ⟨active_min_greedy fr (by omega) ?_ un ad, ?_, ?_⟩
    · intro t tq
      by_cases tr : t ≤ r
      · exact dense t tr
      · exact middle t (by omega) tq
    · intro t tq
      by_cases eq : t = q
      · exact Or.inr (by rw [eq])
      · apply Or.inl
        by_cases tr : t ≤ r
        · exact dense t tr
        · exact middle t (by omega) (by omega)
    · intro t qt tb ht ht1
      rcases ht with old | same
      · rcases ht1 with old1 | same1
        · exact sp t (by omega) tb old old1
        · have eq := (point_injective p (t+1) q).mp same1
          omega
      · have eq := (point_injective p t q).mp same
        omega
  by_cases skip : s.used (point p (r+1))
  · have missing : ¬s.used (point p (r+2)) := by
      simpa only [Nat.add_assoc] using sp (r+1) (by omega) room skip
    have qb : r+2 < B := by
      by_cases h : r+2 < B
      · exact h
      · have eq : r+2 = B := by omega
        exact False.elim (missing (eq ▸ top))
    refine ⟨r+2, by omega, qb, advance (r+2) (by omega) qb ?_ missing ?_⟩
    · intro t rt tq
      have eq : t = r+1 := by omega
      rw [eq]; exact skip
    · unfold Allowed
      rw [hc, point_add_distance]
      exact ⟨two, by decide⟩
  · refine ⟨r+1, by omega, room, advance (r+1) (by omega) room ?_ skip ?_⟩
    · intro t rt tq; omega
    · unfold Allowed
      rw [hc, point_add_distance]
      exact ⟨one, by decide⟩

def Complete (B : Nat) (s : State) : Prop :=
  ∀ z, s.used z ↔ z.natAbs ≤ B

theorem fill_finish {D : Nat → Prop} {p : Bool} {L B : Nat}
    (one : D 1) (two : D 2) (budget r : Nat) (s : State)
    (rb : r < B) (hb : B-r ≤ budget) (fr : Frame p L B s)
    (hc : s.current = point p r)
    (dense : ∀ t, t ≤ r → s.used (point p t))
    (sp : Sparse p r B s) (top : s.used (point p B)) :
    ∃ t, Reaches D s t ∧ Complete B t ∧ t.current = point p (B-1) := by
  induction budget generalizing r s with
  | zero => omega
  | succ budget ih =>
    by_cases done : r+1 = B
    · refine ⟨s, .refl s, ?_, ?_⟩
      · intro z
        refine ⟨fr.bounded z, ?_⟩
        intro zb
        rcases point_cases p z with active | opposite
        · by_cases eq : z.natAbs = B
          · have zeq : z = point p B := by simpa only [eq] using active
            exact zeq ▸ top
          · exact active ▸ dense z.natAbs (by omega)
        · exact opposite ▸ fr.opposite z.natAbs zb
      · have eq : r = B-1 := by omega
        simpa only [eq] using hc
    · obtain ⟨q, rq, qb, choice, dense', sp'⟩ :=
        fill_step one two fr hc (by omega) dense sp top
      obtain ⟨t, path, complete, current⟩ :=
        ih q (visit s (point p q)) qb (by omega)
          (frame_visit fr (by omega)) rfl dense' sp' (Or.inl top)
      exact ⟨t, .cons choice path, complete, current⟩

def Entrance (p : Bool) (L B : Nat) (s : State) : Prop :=
  s.current = point p B ∧
  ∀ z, s.used z ↔ z.natAbs ≤ B ∧
    ¬∃ t, L ≤ t ∧ t < B ∧ z = point p t

theorem opposite_disjoint (p : Bool) (t u : Nat) (positive : 0 < t) :
    point (!p) u ≠ point p t := by
  cases p <;> simp [point] <;> omega

theorem entrance_frame {p : Bool} {L B : Nat} {s : State}
    (hL : 1 ≤ L) (hLB : L ≤ B) (entry : Entrance p L B s) : Frame p L B s := by
  constructor
  · intro z hz; exact ((entry.2 z).mp hz).1
  · intro t tb
    apply (entry.2 _).mpr
    refine ⟨by simpa only [point_abs] using tb, ?_⟩
    rintro ⟨u, lu, _, eq⟩
    exact opposite_disjoint p u t (by omega) eq
  · intro t tl
    apply (entry.2 _).mpr
    refine ⟨?_, ?_⟩
    · rw [point_abs]; omega
    · rintro ⟨u, lu, _, eq⟩
      have same := (point_injective p t u).mp eq
      omega

theorem one_side_filling (D : Nat → Prop) (p : Bool) (L B : Nat) (s : State)
    (one : D 1) (two : D 2) (hL : 1 ≤ L) (hLB : L < B)
    (entry : Entrance p L B s) :
    ∃ t, Reaches D s t ∧ Complete B t ∧ t.current = point p (B-1) := by
  have holes : ∀ r, L ≤ r → r < B → ¬s.used (point p r) := by
    intro r lr rb used
    exact ((entry.2 _).mp used).2 ⟨r, lr, rb, rfl⟩
  have top : s.used (point p B) := by
    apply (entry.2 _).mpr
    refine ⟨by simp only [point_abs]; omega, ?_⟩
    rintro ⟨u, _, ub, eq⟩
    have same := (point_injective p B u).mp eq
    omega
  have sparse : Sparse p L B s := by
    intro r lr rb used
    exact False.elim (holes r (by omega) rb used)
  obtain ⟨u, path, fr, sp, current, upper⟩ :=
    descent_finish one two hL B s (by omega) (Nat.le_refl _)
      (entrance_frame hL (by omega) entry) sparse entry.1 holes top
  have dense : ∀ r, r ≤ L → u.used (point p r) := by
    intro r rl
    by_cases eq : r = L
    · -- The descent's final point must be used; recover this from its path.
      have used_current : u.used u.current := by
        have reachable_used {x y : State} (h : Reaches D x y)
            (hx : x.used x.current) : y.used y.current := by
          induction h with
          | refl => exact hx
          | @cons x y v _ _ ih => exact ih (Or.inr rfl)
        exact reachable_used path (entry.1 ▸ top)
      rw [eq]
      exact current ▸ used_current
    · exact fr.low r (by omega)
  obtain ⟨t, fill, complete, endpoint⟩ :=
    fill_finish one two (B-L) L u hLB (Nat.le_refl _) fr current dense sp upper
  exact ⟨t, path.trans fill, complete, endpoint⟩

end G01
