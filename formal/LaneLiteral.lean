import LaneFill

set_option autoImplicit false

namespace G08
open G01

def prefixState (s : State) (a : Nat → Int) (q : Nat) : State :=
  ⟨a q, fun z => s.used z ∨ ∃ i, 0<i ∧ i≤q ∧ a i=z⟩

def LocalLiteral (D : Nat → Prop) (s : State) (a : Nat → Int) (n : Nat) : Prop :=
  a 0=s.current ∧ ∀ q, q<n →
    ¬(prefixState s a q).used (a (q+1)) ∧ D (a q-a (q+1)).natAbs ∧
    ∀ w, ¬(prefixState s a q).used w → D (a q-w).natAbs →
      (a (q+1)).natAbs ≤ w.natAbs ∧
      ((a (q+1)).natAbs=w.natAbs → w≤a (q+1))

theorem state_ext {s t : State} (current : s.current=t.current)
    (used : ∀ z, s.used z ↔ t.used z) : s=t := by
  obtain ⟨sc,su⟩ := s
  obtain ⟨tc,tu⟩ := t
  have eq : su=tu := funext (fun z => propext (used z))
  cases current
  cases eq
  rfl

theorem prefix_zero {s : State} {a : Nat → Int} (start : a 0=s.current) :
    prefixState s a 0=s := by
  apply state_ext start
  intro z
  change (s.used z ∨ ∃ i, 0<i ∧ i≤0 ∧ a i=z) ↔ s.used z
  constructor
  · rintro (old | ⟨i,lo,hi,_⟩)
    · exact old
    · omega
  · exact Or.inl

theorem prefix_next (s : State) (a : Nat → Int) (q : Nat) :
    prefixState s a (q+1)=visit (prefixState s a q) (a (q+1)) := by
  apply state_ext (s:=prefixState s a (q+1)) (t:=visit (prefixState s a q) (a (q+1))) rfl
  intro z
  change (s.used z ∨ ∃ i, 0<i ∧ i≤q+1 ∧ a i=z) ↔
    (s.used z ∨ ∃ i, 0<i ∧ i≤q ∧ a i=z) ∨ z=a (q+1)
  constructor
  · rintro (old | ⟨i,lo,hi,eq⟩)
    · exact Or.inl (Or.inl old)
    · by_cases small : i≤q
      · exact Or.inl (Or.inr ⟨i,lo,small,eq⟩)
      · have same : i=q+1 := by omega
        exact Or.inr (by simpa only [same] using eq.symm)
  · rintro ((old | ⟨i,lo,hi,eq⟩) | eq)
    · exact Or.inl old
    · exact Or.inr ⟨i,lo,by omega,eq⟩
    · exact Or.inr ⟨q+1,by omega,Nat.le_refl _,eq.symm⟩

theorem prefix_current_used {s : State} {a : Nat → Int}
    (initial : s.used s.current) (start : a 0=s.current) (q : Nat) :
    (prefixState s a q).used (a q) := by
  by_cases zero : q=0
  · exact Or.inl (by simpa only [zero,start] using initial)
  · exact Or.inr ⟨q,by omega,Nat.le_refl _,rfl⟩

theorem unused_distance_positive {s : State} {v : Int}
    (current_used : s.used s.current) (unused : ¬s.used v) :
    0<(s.current-v).natAbs := by
  have ne : s.current ≠ v := fun eq => unused (eq ▸ current_used)
  have absolute := Int.natAbs_eq (s.current-v)
  omega

theorem literal_iff {D : Nat → Prop} {s : State} {a : Nat → Int} {n : Nat}
    (initial : s.used s.current) :
    LocalLiteral D s a n ↔ a 0=s.current ∧
      ∀ q, q<n → Greedy D (prefixState s a q) (a (q+1)) := by
  constructor
  · rintro ⟨start,steps⟩
    refine ⟨start,?_⟩
    intro q qn
    obtain ⟨unused,distance,minimal⟩ := steps q qn
    refine ⟨unused,⟨distance,?_⟩,?_⟩
    · exact unused_distance_positive (prefix_current_used initial start q) unused
    · intro w wu wd
      exact minimal w wu wd.1
  · rintro ⟨start,steps⟩
    refine ⟨start,?_⟩
    intro q qn
    obtain ⟨unused,distance,minimal⟩ := steps q qn
    refine ⟨unused,distance.1,?_⟩
    intro w wu wd
    exact minimal w wu ⟨wd,unused_distance_positive (prefix_current_used initial start q) wu⟩

theorem interior_current_used {s : State} {p : Bool} {L B n : Nat}
    (bound : L+2*n ≤ B) (interior : Interior p L B n s)
    (current : s.current=point p (L+2*n)) : s.used s.current := by
  classical
  apply Classical.byContradiction
  intro unused
  obtain ⟨i,hi,same⟩ := (interior _ (by rw [current,point_abs]; exact bound)).mp unused
  rw [current] at same
  have eq := (point_injective p (L+2*n) (L+2*i)).mp same
  omega

theorem prefix_run (s : State) (p : Bool) (L n q : Nat) :
    prefixState s (fun i => (laneRun s p L n i).current) q = laneRun s p L n q := by
  induction q with
  | zero => exact prefix_zero rfl
  | succ q ih => rw [prefix_next,ih]; rfl

theorem canonical_literal {D : Nat → Prop} {s : State} {p : Bool} {L B n : Nat}
    (even : OnlyEvenTwo D) (positive : 1≤L) (bound : L+2*n≤B)
    (interior : Interior p L B n s) (current : s.current=point p (L+2*n)) :
    LocalLiteral D s (fun q => (laneRun s p L n q).current) n := by
  apply (literal_iff (interior_current_used bound interior current)).mpr
  refine ⟨rfl,?_⟩
  intro q qn
  rw [prefix_run]
  exact run_greedy even positive bound interior current qn

theorem literal_state_eq {D : Nat → Prop} {s : State} {p : Bool} {L B n : Nat}
    (even : OnlyEvenTwo D) (positive : 1≤L) (bound : L+2*n≤B)
    (interior : Interior p L B n s) (current : s.current=point p (L+2*n))
    {a : Nat → Int} (literal : LocalLiteral D s a n) {q : Nat} (qn : q≤n) :
    prefixState s a q=laneRun s p L n q := by
  have choices := (literal_iff (interior_current_used bound interior current)).mp literal
  induction q with
  | zero => exact prefix_zero literal.1
  | succ q ih =>
    have prev := ih (by omega)
    have choice := choices.2 q (by omega)
    rw [prev] at choice
    have eq := greedy_unique choice (run_greedy even positive bound interior current (by omega))
    rw [prefix_next,prev,eq]
    rfl

def LaneEntrance (p : Bool) (L B : Nat) (s : State) : Prop :=
  s.current=point p B ∧ Interior p L B ((B-L)/2) s

theorem lane_count {L B : Nat} (lb : L≤B) (parity : (B-L)%2=0) :
    B=L+2*((B-L)/2) := by omega

theorem conditional_lane_filling {D : Nat → Prop} {s : State} {p : Bool} {L B : Nat}
    (even : OnlyEvenTwo D) (positive : 1≤L) (lb : L<B) (parity : (B-L)%2=0)
    (entry : LaneEntrance p L B s) :
    ∃ a, LocalLiteral D s a ((B-L)/2) ∧
      (∀ q, q≤(B-L)/2 → a q=point p (B-2*q) ∧
        ∀ z, (prefixState s a q).used z ↔ s.used z ∨
          ∃ i, (B-L)/2-q≤i ∧ i<(B-L)/2 ∧ z=point p (L+2*i)) ∧
      (∀ b, LocalLiteral D s b ((B-L)/2) → ∀ q, q≤(B-L)/2 → b q=a q) ∧
      a ((B-L)/2)=point p L ∧
      (∀ q, q≤(B-L)/2 →
        ((∀ z, z.natAbs≤B → (prefixState s a q).used z) ↔ q=(B-L)/2)) := by
  have count := lane_count (show L≤B by omega) parity
  have bound : L+2*((B-L)/2)≤B := by omega
  have current : s.current=point p (L+2*((B-L)/2)) := by rw [←count]; exact entry.1
  let a := fun q => (laneRun s p L ((B-L)/2) q).current
  refine ⟨a,canonical_literal even positive bound entry.2 current,?_,?_,?_,?_⟩
  · intro q qn
    constructor
    · have radius : L+2*((B-L)/2-q)=B-2*q := by omega
      exact (run_current current q).trans (congrArg (point p) radius)
    · intro z
      change (prefixState s (fun q => (laneRun s p L ((B-L)/2) q).current) q).used z ↔ _
      rw [prefix_run]
      exact run_used qn z
  · intro b literal q qn
    exact congrArg State.current (literal_state_eq even positive bound entry.2 current literal qn)
  · have h := run_current current ((B-L)/2)
    simpa only [Nat.sub_self,Nat.mul_zero,Nat.add_zero] using h
  · intro q qn
    change (∀ z, z.natAbs≤B →
      (prefixState s (fun q => (laneRun s p L ((B-L)/2) q).current) q).used z) ↔ _
    rw [prefix_run]
    exact run_complete_iff bound entry.2 qn

theorem finite_literal_prefix {D : Nat → Prop} {s : State} {p : Bool} {L B : Nat}
    (even : OnlyEvenTwo D) (positive : 1≤L) (lb : L<B) (parity : (B-L)%2=0)
    (entry : LaneEntrance p L B s) (finite : FiniteUsed s) {a : Nat → Int}
    (literal : LocalLiteral D s a ((B-L)/2)) {q : Nat} (qn : q≤(B-L)/2) :
    FiniteUsed (prefixState s a q) := by
  have count := lane_count (show L≤B by omega) parity
  have bound : L+2*((B-L)/2)≤B := by omega
  have current : s.current=point p (L+2*((B-L)/2)) := by rw [←count]; exact entry.1
  rw [literal_state_eq even positive bound entry.2 current literal qn]
  exact run_finite finite q

def LiteralWalk (D : Nat → Prop) (a : Nat → Int) : Prop :=
  a 0=0 ∧ ∀ n,
    (¬∃ i, i≤n ∧ a i=a (n+1)) ∧ D (a n-a (n+1)).natAbs ∧
    ∀ w, (¬∃ i, i≤n ∧ a i=w) → D (a n-w).natAbs →
      (a (n+1)).natAbs≤w.natAbs ∧ ((a (n+1)).natAbs=w.natAbs → w≤a (n+1))

theorem history_segment (a : Nat → Int) (N q : Nat) :
    prefixState (history a N) (fun i => a (N+i)) q = history a (N+q) := by
  apply state_ext (s:=prefixState (history a N) (fun i => a (N+i)) q)
    (t:=history a (N+q)) rfl
  intro z
  change ((∃ i,i≤N ∧ a i=z) ∨ ∃ i,0<i ∧ i≤q ∧ a (N+i)=z) ↔
    ∃ i,i≤N+q ∧ a i=z
  constructor
  · rintro (⟨i,hi,eq⟩ | ⟨i,lo,hi,eq⟩)
    · exact ⟨i,by omega,eq⟩
    · exact ⟨N+i,by omega,eq⟩
  · rintro ⟨i,hi,eq⟩
    by_cases small : i≤N
    · exact Or.inl ⟨i,small,eq⟩
    · refine Or.inr ⟨i-N,by omega,by omega,?_⟩
      have same : N+(i-N)=i := by omega
      simpa only [same] using eq

theorem walk_segment_literal {D : Nat → Prop} {a : Nat → Int}
    (rule : LiteralWalk D a) (N n : Nat) :
    LocalLiteral D (history a N) (fun q => a (N+q)) n := by
  constructor
  · simp [history]
  · intro q _qn
    have step := rule.2 (N+q)
    change ¬(prefixState (history a N) (fun q => a (N+q)) q).used (a (N+(q+1))) ∧ _
    rw [history_segment]
    simpa only [history,Nat.add_assoc] using step

theorem literal_walk_lane {D : Nat → Prop} {a : Nat → Int} {N L B : Nat} {p : Bool}
    (rule : LiteralWalk D a) (even : OnlyEvenTwo D) (positive : 1≤L)
    (lb : L<B) (parity : (B-L)%2=0) (entry : LaneEntrance p L B (history a N)) :
    ∀ q, q≤(B-L)/2 → a (N+q)=point p (B-2*q) ∧
      ∀ z, (∃ i,i≤N+q ∧ a i=z) ↔ (∃ i,i≤N ∧ a i=z) ∨
        ∃ i,(B-L)/2-q≤i ∧ i<(B-L)/2 ∧ z=point p (L+2*i) := by
  obtain ⟨b,_,prefixes,unique,_,_⟩ := conditional_lane_filling even positive lb parity entry
  have literal := walk_segment_literal rule N ((B-L)/2)
  intro q qn
  have eq := unique (fun q => a (N+q)) literal q qn
  refine ⟨eq.trans (prefixes q qn).1,?_⟩
  have count := lane_count (show L≤B by omega) parity
  have bound : L+2*((B-L)/2)≤B := by omega
  have current : (history a N).current=point p (L+2*((B-L)/2)) := by
    rw [←count]; exact entry.1
  intro z
  have state := literal_state_eq even positive bound entry.2 current literal qn
  rw [history_segment] at state
  change (history a (N+q)).used z ↔ _
  rw [state]
  exact run_used qn z

end G08
