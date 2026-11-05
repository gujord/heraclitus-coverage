import CofiniteGlobal

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G10
open G01

theorem literal_unique {D : Nat → Prop} {a b : Nat → Int}
    (ra : G06.LiteralRule D a) (rb : G06.LiteralRule D b) : ∀ n, a n=b n := by
  have wa := (G06.literal_iff D a).mp ra
  have wb := (G06.literal_iff D b).mp rb
  have initialEqual : ∀ n, ∀ i, i ≤ n → a i=b i := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have iz : i=0 := by omega
      rw [iz,ra.1,rb.1]
    | succ n ih =>
      have states : history a n=history b n := by
        apply state_ext (ih n (Nat.le_refl n))
        intro z
        change (∃ i,i≤n ∧ a i=z) ↔ (∃ i,i≤n ∧ b i=z)
        constructor
        · rintro ⟨i,hi,eq⟩
          exact ⟨i,hi,(ih i hi).symm.trans eq⟩
        · rintro ⟨i,hi,eq⟩
          exact ⟨i,hi,(ih i hi).trans eq⟩
      have step : a (n+1)=b (n+1) := by
        have first := wa.2 n
        rw [states] at first
        exact greedy_unique first (wb.2 n)
      intro i hi
      by_cases small : i≤n
      · exact ih i small
      · have eq : i=n+1 := by omega
        simpa only [eq] using step
  intro n
  exact initialEqual n n (Nat.le_refl n)

theorem literal_first_visit_unique {D : Nat → Prop} {M : Nat} {a : Nat → Int}
    (tail : OddTail D M) (rule : G06.LiteralRule D a) (z : Int) :
    ∃ n, n ≤ 4*M+6*z.natAbs+9 ∧ a n=z ∧ ∀ j, a j=z → j=n := by
  obtain ⟨n,bound,eq⟩ := literal_first_visit tail rule z
  refine ⟨n,bound,eq,?_⟩
  intro j same
  exact walk_injective ((G06.literal_iff D a).mp rule).2 j n (same.trans eq.symm)

def g08Distances (k d : Nat) : Prop := d=2 ∨ d=3 ∨ ∃ t, d=10*k+3+2*t

theorem g08_odd_tail (k : Nat) : OddTail (g08Distances k) (10*k+3) := by
  intro d large odd
  refine Or.inr (Or.inr ⟨(d-(10*k+3))/2,?_⟩)
  omega

theorem g08_box_deadline {k : Nat} {a : Nat → Int}
    (rule : G06.LiteralRule (g08Distances k) a) (z : Int)
    (inside : z.natAbs ≤ 5*k+2) : ∃ n, n ≤ 70*k+33 ∧ a n=z := by
  obtain ⟨n,bound,eq⟩ := literal_first_visit (g08_odd_tail k) rule z
  exact ⟨n,by omega,eq⟩

theorem g08_exists (k : Nat) :
    ∃ a, G06.LiteralRule (g08Distances k) a ∧ Coverage a ∧
      ∀ z : Int, z.natAbs ≤ 5*k+2 → ∃ n, n ≤ 70*k+33 ∧ a n=z := by
  obtain ⟨a,rule,covers,_⟩ := literal_exists (g08Distances k) (10*k+3) (g08_odd_tail k)
  exact ⟨a,rule,covers,g08_box_deadline rule⟩

end G10
