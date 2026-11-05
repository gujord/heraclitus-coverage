import LaneLiteral

set_option autoImplicit false

namespace G08E
open G01

def shortD (d : Nat) : Prop := d=2 ∨ d=3

def distances (k d : Nat) : Prop := d=2 ∨ d=3 ∨ ∃ t, d=10*k+3+2*t

def after (s : State) : List Int → State
  | [] => s
  | v::vs => after (visit s v) vs

def Valid (D : Nat → Prop) (s : State) : List Int → Prop
  | [] => True
  | v::vs => Greedy D s v ∧ Valid D (visit s v) vs

theorem history_next (a : Nat → Int) (n : Nat) :
    history a (n+1)=visit (history a n) (a (n+1)) := by
  have h := G08.prefix_next (history a n) (fun i => a (n+i)) 0
  rw [G08.history_segment,G08.history_segment] at h
  simpa only [Nat.add_zero,Nat.zero_add] using h

theorem walk_greedy {D : Nat → Prop} {a : Nat → Int} (rule : G08.LiteralWalk D a) (n : Nat) :
    Greedy D (history a n) (a (n+1)) := by
  have segment := G08.walk_segment_literal rule n 1
  have initial : (history a n).used (history a n).current := ⟨n,Nat.le_refl _,rfl⟩
  have choice := ((G08.literal_iff initial).mp segment).2 0 (by decide)
  rw [G08.history_segment] at choice
  simpa only [Nat.add_zero,Nat.zero_add] using choice

theorem follow_trace {D : Nat → Prop} {a : Nat → Int} (rule : G08.LiteralWalk D a)
    {n : Nat} {s : State} {xs : List Int} (entry : history a n=s) (valid : Valid D s xs) :
    history a (n+xs.length)=after s xs := by
  induction xs generalizing n s with
  | nil => simpa only [List.length_nil,Nat.add_zero,after] using entry
  | cons v xs ih =>
    have choice := walk_greedy rule n
    rw [entry] at choice
    have eq := greedy_unique choice valid.1
    have next : history a (n+1)=visit s v := by rw [history_next,entry,eq]
    have result := ih next valid.2
    simpa only [List.length_cons,after,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using result

theorem abs_distance_bound (c v : Int) : (c-v).natAbs ≤ c.natAbs+v.natAbs := by
  have hc := Int.natAbs_eq c
  have hv := Int.natAbs_eq v
  have hd := Int.natAbs_eq (c-v)
  omega

theorem short_lift {k : Nat} {s : State} {v : Int}
    (short : Greedy shortD s v) (shield : s.current.natAbs+v.natAbs < 10*k+3) :
    Greedy (distances k) s v := by
  refine ⟨short.1,⟨?_,short.2.1.2⟩,?_⟩
  · rcases short.2.1.1 with two | three
    · exact Or.inl two
    · exact Or.inr (Or.inl three)
  · intro w wu wd
    rcases wd.1 with two | three | ⟨t,tail⟩
    · exact short.2.2 w wu ⟨Or.inl two,wd.2⟩
    · exact short.2.2 w wu ⟨Or.inr three,wd.2⟩
    · have bound := abs_distance_bound s.current w
      have strict : v.natAbs<w.natAbs := by omega
      exact ⟨by omega,by intro eq; omega⟩

theorem short_greedy {s : State} {v : Int}
    (unused : ¬s.used v) (jump : (s.current-v).natAbs=2 ∨ (s.current-v).natAbs=3)
    (choices : ∀ w, (w=s.current-2 ∨ w=s.current+2 ∨ w=s.current-3 ∨ w=s.current+3) →
      ¬s.used w → Preferred v w) : Greedy shortD s v := by
  refine ⟨unused,⟨jump,by omega⟩,?_⟩
  intro w wu wd
  have absolute := Int.natAbs_eq (s.current-w)
  apply choices w _ wu
  rcases wd.1 with h | h <;> omega

theorem negative_preferred {v w : Int} (nonpos : v≤0) (le : w≤v) : Preferred v w := by
  have av := Int.natAbs_eq v
  have aw := Int.natAbs_eq w
  exact ⟨by omega,by intro _; exact le⟩

theorem positive_preferred {r : Nat} {w : Int} (bound : r≤w.natAbs) : Preferred (r : Int) w := by
  have aw := Int.natAbs_eq w
  simp only [Preferred,Int.natAbs_natCast]
  exact ⟨bound,by intro equal; omega⟩

theorem negative_shield {k : Nat} {c v : Int} (hc : c≤0) (hv : v≤0)
    (bound : -c-v < (10*k+3 : Nat)) : c.natAbs+v.natAbs<10*k+3 := by
  have ac := Int.natAbs_eq c
  have av := Int.natAbs_eq v
  omega

theorem short_signed {s : State} {v : Int} (unused : ¬s.used v)
    (jump : s.current-v=2 ∨ s.current-v=(-2) ∨ s.current-v=3 ∨ s.current-v=(-3))
    (choices : ∀ w, (w=s.current-2 ∨ w=s.current+2 ∨ w=s.current-3 ∨ w=s.current+3) →
      ¬s.used w → Preferred v w) : Greedy shortD s v := by
  apply short_greedy unused _ choices
  have absolute := Int.natAbs_eq (s.current-v)
  omega

theorem lift_trace {k R : Nat} {s : State} {xs : List Int}
    (valid : Valid shortD s xs) (current : s.current.natAbs≤R)
    (points : ∀ v, v∈xs → v.natAbs≤R) (shield : 2*R<10*k+3) : Valid (distances k) s xs := by
  induction xs generalizing s with
  | nil => trivial
  | cons v xs ih =>
    have vb := points v (by simp)
    refine ⟨short_lift valid.1 (by omega),?_⟩
    apply ih valid.2 vb
    intro w hw
    exact points w (by simp [hw])

end G08E
