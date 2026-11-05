import ResidueCoverage

set_option autoImplicit false

namespace G18
open G01

theorem progression_exists (D : Nat → Prop) (q r M : Nat)
    (hq : 0<q) (hr : r<q) (coprime : Nat.gcd q r=1)
    (tail : ∀ d, 0<d → M≤d → d%q=r → D d) :
    ∃ a, G06.LiteralRule D a ∧ Coverage a ∧
      ∀ b, G06.LiteralRule D b → ∀ n, a n=b n := by
  apply literal_exists D q M [r] hq (by simp)
  · intro s hs
    have eq : s=r := by simpa using hs
    simpa only [eq] using hr
  · exact coprime
  · intro d positive large member
    exact tail d positive large (by simpa using member)

theorem odd_tail_coverage {D : Nat → Prop} {a : Nat → Int} {M : Nat}
    (tail : G10.OddTail D M) (rule : G06.LiteralRule D a) : Coverage a := by
  apply literal_coverage (q:=2) (M:=M) (S:=[1]) (by decide) (by decide)
  · intro s hs
    have eq : s=1 := by simpa using hs
    omega
  · decide
  · intro d _ large member
    exact tail d large (by simpa using member)
  · exact rule

def progressionFive (d : Nat) : Prop := 5≤d ∧ d%3=2

theorem progression_five_no_short :
    ¬progressionFive 1 ∧ ¬progressionFive 2 ∧ ¬progressionFive 3 := by
  unfold progressionFive
  decide

theorem progression_five_exists :
    ∃ a, G06.LiteralRule progressionFive a ∧ Coverage a ∧
      ∀ b, G06.LiteralRule progressionFive b → ∀ n, a n=b n := by
  apply progression_exists progressionFive 3 2 5 (by decide) (by decide) (by decide)
  intro d _ large rem
  exact ⟨large,rem⟩

def mixedSix (d : Nat) : Prop := 8≤d ∧ (d%6=2 ∨ d%6=3)

theorem mixed_six_residues :
    Nat.gcd 6 2=2 ∧ Nat.gcd 6 3=3 ∧ ([2,3] : List Nat).foldl Nat.gcd 6=1 := by
  decide

theorem mixed_six_exists :
    ∃ a, G06.LiteralRule mixedSix a ∧ Coverage a ∧
      ∀ b, G06.LiteralRule mixedSix b → ∀ n, a n=b n := by
  apply literal_exists mixedSix 6 8 [2,3] (by decide) (by decide)
  · intro s hs
    have cases : s=2 ∨ s=3 := by simpa using hs
    omega
  · decide
  · intro d _ large member
    exact ⟨large,by simpa using member⟩

theorem modulus_one_exists (M : Nat) :
    ∃ a, G06.LiteralRule (fun d => 0<d ∧ M≤d) a ∧ Coverage a ∧
      ∀ b, G06.LiteralRule (fun d => 0<d ∧ M≤d) b → ∀ n, a n=b n := by
  apply literal_exists (fun d => 0<d ∧ M≤d) 1 M [0] (by decide) (by decide)
  · intro s hs
    have eq : s=0 := by simpa using hs
    omega
  · decide
  · exact fun _ positive large _ => ⟨positive,large⟩

theorem duplicate_residues_exists :
    ∃ a, G06.LiteralRule progressionFive a ∧ Coverage a ∧
      ∀ b, G06.LiteralRule progressionFive b → ∀ n, a n=b n := by
  apply literal_exists progressionFive 3 5 [2,2] (by decide) (by decide)
  · intro s hs
    have eq : s=2 := by simpa using hs
    omega
  · decide
  · intro d _ large member
    exact ⟨large,by simpa using member⟩

end G18
