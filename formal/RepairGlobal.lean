import RepairEntrance

set_option autoImplicit false

namespace G09
open G01 G02

def Checkpoints (a : Nat → Int) : Prop :=
  ∀ j, Frontier (36+2*j) (history a (72+4*j))

def Repairs (a : Nat → Int) : Prop :=
  ∀ j, a (73+4*j)=((36+2*j : Nat) : Int)

theorem tail_hypotheses (j : Nat) :
    distances 1 ∧ distances 3 ∧ distances (2*(36+2*j)) ∧
    distances (2*(36+2*j)+4) ∧ ¬distances 2 ∧
    ¬distances (2*(36+2*j)+1) ∧ ¬distances (2*(36+2*j)+2) ∧
    ¬distances (2*(36+2*j)+3) := by
  unfold distances
  omega

theorem checkpoints {a : Nat → Int} (rule : Rule distances a) : Checkpoints a := by
  intro j
  induction j with
  | zero => exact entrance_frontier rule
  | succ j ih =>
    obtain ⟨one, three, jump, next, no2, no1, noCross2, no3⟩ := tail_hypotheses j
    have cert := repair_certificate (history a (72+4*j)) one three jump next no2 no1 noCross2 no3 (by omega) ih
    have hstate := certificate_history rule (repairBlock (36+2*j)) (72+4*j) (history a (72+4*j)) rfl cert
    have result := repair_finish ih
    have index : 72+4*j+(repairBlock (36+2*j)).length=72+4*(j+1) := by
      simp only [repairBlock, List.length_cons, List.length_nil]; omega
    have radius : 36+2*j+2=36+2*(j+1) := by omega
    rw [index] at hstate
    simpa only [←hstate, radius] using result

theorem immediate_repairs {a : Nat → Int} (rule : Rule distances a) : Repairs a := by
  intro j
  have state := checkpoints rule j
  have jump := (tail_hypotheses j).2.2.1
  have choice := first_repair jump (by omega) state
  have eq := greedy_unique (rule.2 (72+4*j)) choice
  have index : 72+4*j+1=73+4*j := by omega
  simpa only [index] using eq

def RepairBound (a : Nat → Int) : Prop :=
  ∀ n, 64≤n → n%4=0 → ∀ z, z.natAbs≤n/2 → ¬(history a n).used z →
    ∃ k, 1≤k ∧ k≤3 ∧ a (n+k)=z

theorem repairs_within_three {a : Nat → Int} (rule : Rule distances a) : RepairBound a := by
  intro n hn hn4 z hz missing
  have az := Int.natAbs_eq z
  by_cases first : n=64
  · subst n
    have out : ¬((-32≤z ∧ z≤32 ∧ z≠ -31) ∨ z=35) :=
      fun h => missing ((first_checkpoint_frame rule z).mpr h)
    have eq : z= -31 := by omega
    exact ⟨3, by decide, by decide, by simpa only [eq] using (original_hole rule).2.2.2⟩
  by_cases second : n=68
  · subst n
    have out : ¬((-34≤z ∧ z<34) ∨ z=35) :=
      fun h => missing ((second_checkpoint_frame rule z).mpr h)
    have eq : z=34 := by omega
    exact ⟨1, by decide, by decide, by simpa only [eq] using (second_hole rule).2⟩
  · have hn72 : 72≤n := by omega
    let j := (n-72)/4
    have index : n=72+4*j := by dsimp only [j]; omega
    rw [index] at hz missing ⊢
    have state := (checkpoints rule j).2
    have out : ¬((-((36+2*j : Nat) : Int)≤z ∧ z<((36+2*j : Nat) : Int)) ∨ z=((36+2*j : Nat) : Int)+1) :=
      fun h => missing ((state z).mpr h)
    have eq : z=((36+2*j : Nat) : Int) := by omega
    refine ⟨1, by decide, by decide, ?_⟩
    have next : 72+4*j+1=73+4*j := by omega
    simpa only [next, eq] using immediate_repairs rule j

theorem coverage {a : Nat → Int} (rule : Rule distances a) : Coverage a := by
  intro z
  have hz := Int.natAbs_eq z
  have used := ((checkpoints rule z.natAbs).2 z).mpr (Or.inl ⟨by omega, by omega⟩)
  obtain ⟨i, _, eq⟩ := used
  exact ⟨i, eq, fun j same => walk_injective rule.2 j i (same.trans eq.symm)⟩

theorem distances_unbounded : Unbounded distances := by
  intro N
  refine ⟨64+4*N, by omega, ?_⟩
  unfold distances; omega

theorem literal_checkpoints {a : Nat → Int} (rule : G06.LiteralRule distances a) : Checkpoints a :=
  checkpoints ((G06.literal_iff distances a).mp rule)

theorem literal_repairs {a : Nat → Int} (rule : G06.LiteralRule distances a) : Repairs a :=
  immediate_repairs ((G06.literal_iff distances a).mp rule)

theorem literal_coverage {a : Nat → Int} (rule : G06.LiteralRule distances a) : Coverage a :=
  coverage ((G06.literal_iff distances a).mp rule)

theorem literal_repair_bound {a : Nat → Int} (rule : G06.LiteralRule distances a) : RepairBound a :=
  repairs_within_three ((G06.literal_iff distances a).mp rule)

theorem literal_exists : ∃ a, G06.LiteralRule distances a ∧ Checkpoints a ∧ Repairs a ∧ RepairBound a ∧ Coverage a := by
  obtain ⟨a, rule⟩ := G02.unbounded_exists distances distances_unbounded
  exact ⟨a, (G06.literal_iff distances a).mpr rule, checkpoints rule, immediate_repairs rule, repairs_within_three rule, coverage rule⟩

end G09
