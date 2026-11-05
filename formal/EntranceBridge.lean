import CofiniteResults
import EntranceGlobal

set_option autoImplicit false

namespace G08E
open G01

theorem difference_symmetric (x y : Int) : (x-y).natAbs=(y-x).natAbs := by
  have first := Int.natAbs_eq (x-y)
  have second := Int.natAbs_eq (y-x)
  omega

theorem literal_rule_iff (D : Nat → Prop) (a : Nat → Int) :
    G06.LiteralRule D a ↔ G08.LiteralWalk D a := by
  constructor
  · rintro ⟨start,steps⟩
    refine ⟨start,?_⟩
    intro n
    obtain ⟨unused,distance,minimal⟩ := steps n
    refine ⟨unused,?_,?_⟩
    · rw [difference_symmetric (a n) (a (n+1))]
      exact distance
    · intro w wu wd
      apply minimal w wu
      rw [difference_symmetric w (a n)]
      exact wd
  · rintro ⟨start,steps⟩
    refine ⟨start,?_⟩
    intro n
    obtain ⟨unused,distance,minimal⟩ := steps n
    refine ⟨unused,?_,?_⟩
    · rw [difference_symmetric (a (n+1)) (a n)]
      exact distance
    · intro w wu wd
      apply minimal w wu
      rw [difference_symmetric (a n) w]
      exact wd

theorem literal_exists (k : Nat) : ∃ a, G08.LiteralWalk (distances k) a := by
  obtain ⟨a,rule,_,_⟩ := G10.g08_exists k
  exact ⟨a,(literal_rule_iff (distances k) a).mp rule⟩

theorem box_deadline {k : Nat} {a : Nat → Int} (rule : G08.LiteralWalk (distances k) a)
    (z : Int) (inside : z.natAbs≤5*k+2) : ∃ n, n≤70*k+33 ∧ a n=z := by
  have literal := (literal_rule_iff (distances k) a).mpr rule
  exact G10.g08_box_deadline literal z inside

theorem omitted_entrance_deadline {k : Nat} {a : Nat → Int}
    (rule : G08.LiteralWalk (distances k) a) {z : Int}
    (missing : ¬∃ i,i≤5*k+5 ∧ a i=z) (inside : z.natAbs≤5*k+2) :
    ∃ n, 5*k+5<n ∧ n≤70*k+33 ∧ n-(5*k+5)≤65*k+28 ∧ a n=z := by
  obtain ⟨n,upper,eq⟩ := box_deadline rule z inside
  have lower : 5*k+5<n := by
    by_cases earlier : n≤5*k+5
    · exact False.elim (missing ⟨n,earlier,eq⟩)
    · omega
  exact ⟨n,lower,upper,by omega,eq⟩

end G08E
