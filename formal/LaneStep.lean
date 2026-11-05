import Semantics

set_option autoImplicit false

namespace G08
open G01

def OnlyEvenTwo (D : Nat → Prop) : Prop :=
  D 2 ∧ ∀ d, D d → 0 < d → d % 2 = 0 → d = 2

def Hole (p : Bool) (L n : Nat) (z : Int) : Prop :=
  ∃ i, i < n ∧ z = point p (L+2*i)

def Interior (p : Bool) (L B n : Nat) (s : State) : Prop :=
  ∀ z, z.natAbs ≤ B → (¬s.used z ↔ Hole p L n z)

theorem point_distance {p : Bool} {a b : Nat} (le : b ≤ a) :
    (point p a - point p b).natAbs = a-b := by
  have sub : a-(a-b)=b := by omega
  have h := point_sub_distance p a (a-b) (by omega)
  simpa only [sub] using h

theorem inward_greedy {D : Nat → Prop} {p : Bool} {L B n : Nat} {s : State}
    (even : OnlyEvenTwo D) (_positive : 1 ≤ L) (bound : L+2*(n+1) ≤ B)
    (interior : Interior p L B (n+1) s)
    (current : s.current = point p (L+2*(n+1))) :
    Greedy D s (point p (L+2*n)) := by
  have wb : (point p (L+2*n)).natAbs ≤ B := by rw [point_abs]; omega
  have unused := (interior _ wb).mpr ⟨n,by omega,rfl⟩
  have allowed : Allowed D s.current (point p (L+2*n)) := by
    unfold Allowed
    rw [current, point_distance (by omega)]
    have diff : L+2*(n+1)-(L+2*n)=2 := by omega
    rw [diff]
    exact ⟨even.1,by decide⟩
  refine ⟨unused,allowed,?_⟩
  intro w wu wa
  by_cases inside : w.natAbs ≤ B
  · obtain ⟨i,hi,eq⟩ := (interior w inside).mp wu
    have dist : (s.current-w).natAbs = L+2*(n+1)-(L+2*i) := by
      rw [current,eq,point_distance (by omega)]
    have step : L+2*(n+1)-(L+2*i)=2 := by
      apply even.2 _
      · simpa only [dist] using wa.1
      · simpa only [dist] using wa.2
      · omega
    have same : i=n := by omega
    rw [eq,same]
    exact ⟨Nat.le_refl _,fun _ => Int.le_refl _⟩
  · constructor
    · rw [point_abs]; omega
    · intro equal
      rw [point_abs] at equal
      omega

theorem interior_visit {p : Bool} {L B n : Nat} {s : State}
    (_bound : L+2*(n+1) ≤ B) (interior : Interior p L B (n+1) s) :
    Interior p L B n (visit s (point p (L+2*n))) := by
  intro z zb
  constructor
  · intro unused
    have old : ¬s.used z := fun h => unused (Or.inl h)
    obtain ⟨i,hi,eq⟩ := (interior z zb).mp old
    refine ⟨i,?_,eq⟩
    have ne : i ≠ n := by
      intro same
      exact unused (Or.inr (by simpa only [same] using eq))
    omega
  · rintro ⟨i,hi,eq⟩ used
    rcases used with old | same
    · exact (interior z zb).mpr ⟨i,by omega,eq⟩ old
    · have radii := (point_injective p (L+2*i) (L+2*n)).mp (eq.symm.trans same)
      omega

end G08
