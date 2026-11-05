import LaneLiteral

set_option autoImplicit false

namespace G08
open G01

def sampleUsed (p : Bool) : List Int :=
  if p then [-5,-4,-3,-2,-1,0,2,4,5,12,-17] else [-5,-4,-2,0,1,2,3,4,5,12,-17]

def sampleState (p : Bool) : State := ⟨point p 5, fun z => z ∈ sampleUsed p⟩

def allOddsAndTwo (d : Nat) : Prop := d=2 ∨ d%2=1

theorem sample_distances : OnlyEvenTwo allOddsAndTwo := by
  constructor
  · exact Or.inl rfl
  · intro d hd _ even
    rcases hd with eq | odd
    · exact eq
    · omega

theorem two_holes (p : Bool) (z : Int) :
    Hole p 1 2 z ↔ z=point p 1 ∨ z=point p 3 := by
  constructor
  · rintro ⟨i,hi,eq⟩
    have cases : i=0 ∨ i=1 := by omega
    rcases cases with zero | one
    · exact Or.inl (by simpa only [zero] using eq)
    · exact Or.inr (by simpa only [one] using eq)
  · rintro (eq | eq)
    · exact ⟨0,by decide,eq⟩
    · exact ⟨1,by decide,eq⟩

theorem sample_entry (p : Bool) : LaneEntrance p 1 5 (sampleState p) := by
  refine ⟨rfl,?_⟩
  intro z zb
  change ¬(sampleState p).used z ↔ Hole p 1 2 z
  rw [two_holes]
  have absolute := Int.natAbs_eq z
  cases p <;> simp [sampleState,sampleUsed,point] <;> omega

theorem sample_finite (p : Bool) : FiniteUsed (sampleState p) :=
  ⟨sampleUsed p,fun _ => Iff.rfl⟩

theorem sample_exterior (p : Bool) :
    (sampleState p).used 12 ∧ (sampleState p).used (-17) := by
  cases p <;> simp [sampleState,sampleUsed]

theorem sample_filling (p : Bool) :
    ∃ a, LocalLiteral allOddsAndTwo (sampleState p) a 2 ∧
      a 1=point p 3 ∧ a 2=point p 1 ∧
      FiniteUsed (prefixState (sampleState p) a 2) ∧
      (prefixState (sampleState p) a 2).used 12 ∧
      (prefixState (sampleState p) a 2).used (-17) := by
  obtain ⟨a,literal,prefixes,_,last,_⟩ := conditional_lane_filling
    sample_distances (by decide : 1≤1) (by decide : 1<5) (by decide) (sample_entry p)
  refine ⟨a,literal,?_,last,?_,?_,?_⟩
  · exact (prefixes 1 (by decide)).1
  · exact finite_literal_prefix sample_distances (by decide) (by decide) (by decide)
      (sample_entry p) (sample_finite p) literal (by decide)
  · exact Or.inl (sample_exterior p).1
  · exact Or.inl (sample_exterior p).2

theorem positive_exterior_filling :
    ∃ a, LocalLiteral allOddsAndTwo (sampleState true) a 2 ∧ a 1=3 ∧ a 2=1 := by
  obtain ⟨a,rule,first,last,_⟩ := sample_filling true
  exact ⟨a,rule,first,last⟩

theorem negative_exterior_filling :
    ∃ a, LocalLiteral allOddsAndTwo (sampleState false) a 2 ∧ a 1=(-3) ∧ a 2=(-1) := by
  obtain ⟨a,rule,first,last,_⟩ := sample_filling false
  exact ⟨a,rule,first,last⟩

def extraEven (d : Nat) : Prop := d=2 ∨ d=4

def noTwo (d : Nat) : Prop := d=3

def twoAndFive (d : Nat) : Prop := d=2 ∨ d=5

def onlyTwo (d : Nat) : Prop := d=2

def extraHole : State := ⟨5,fun z => (sampleState true).used z ∧ z≠0⟩

def wrongEntrance : State := ⟨-5,(sampleState true).used⟩

theorem extra_even_counterexample : ¬Greedy extraEven (sampleState true) 3 := by
  intro choice
  have pref := choice.2.2 1 (by simp [sampleState,sampleUsed])
    (by simp [Allowed,extraEven,sampleState,point])
  exact (by unfold Preferred; decide : ¬Preferred 3 1) pref

theorem absent_two_counterexample : ¬Greedy noTwo (sampleState true) 3 := by
  intro choice
  exact (by simp [Allowed,noTwo,sampleState,point] :
    ¬Allowed noTwo (sampleState true).current 3) choice.2.1

theorem extra_hole_counterexample : ¬Greedy twoAndFive extraHole 3 := by
  intro choice
  have pref := choice.2.2 0 (by simp [extraHole])
    (by simp [Allowed,twoAndFive,extraHole])
  exact (by unfold Preferred; decide : ¬Preferred 3 0) pref

theorem wrong_entrance_counterexample : ¬Greedy onlyTwo wrongEntrance 3 := by
  intro choice
  exact (by simp [Allowed,onlyTwo,wrongEntrance] :
    ¬Allowed onlyTwo wrongEntrance.current 3) choice.2.1

theorem third_inward_move_counterexample :
    ¬Greedy onlyTwo (visit (visit (sampleState true) 3) 1) (-1) := by
  intro choice
  exact choice.1 (Or.inl (Or.inl (by simp [sampleState,sampleUsed])))

end G08
