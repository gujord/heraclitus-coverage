import ResidueOmission

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G18
open G01

theorem omitted_add {D : Nat → Prop} {a : Nat → Int}
    {q M s : Nat} {S : List Nat} (hq : 0<q) (hs : s<q) (member : s∈S)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a)
    {r : Int} (omitted : OmittedClass a q r) : OmittedClass a q (r+(s : Int)) := by
  obtain ⟨h,missing,rem⟩ := omitted
  obtain ⟨B,bound⟩ := upper_class hq hs member tail rule missing
  obtain ⟨x,large,eq⟩ := class_above q hq (h+(s : Int)) B
  refine ⟨x, ?_, ?_⟩
  · intro n hit
    have b := bound n (by rwa [hit])
    omega
  · rw [eq, Int.add_emod, rem, ← Int.add_emod]

theorem omitted_sub {D : Nat → Prop} {a : Nat → Int}
    {q M s : Nat} {S : List Nat} (hq : 0<q) (hs : s<q) (member : s∈S)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a)
    {r : Int} (omitted : OmittedClass a q r) : OmittedClass a q (r-(s : Int)) := by
  obtain ⟨h,missing,rem⟩ := omitted
  obtain ⟨B,bound⟩ := lower_class hq hs member tail rule missing
  obtain ⟨x,small,eq⟩ := class_below q hq (h-(s : Int)) B
  refine ⟨x, ?_, ?_⟩
  · intro n hit
    have b := bound n (by rwa [hit])
    omega
  · rw [eq, Int.sub_emod, rem, ← Int.sub_emod]

theorem omitted_shift {D : Nat → Prop} {a : Nat → Int}
    {q M s : Nat} {S : List Nat} (hq : 0<q) (hs : s<q) (member : s∈S)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a) :
    Shift (OmittedClass a q) (s : Int) := by
  intro r
  constructor
  · intro h
    have k := omitted_sub hq hs member tail rule h
    have e : r+(s : Int)-(s : Int)=r := by omega
    rwa [e] at k
  · exact omitted_add hq hs member tail rule

theorem omitted_period (a : Nat → Int) (q : Nat) :
    Shift (OmittedClass a q) (q : Int) := by
  intro r
  simp only [OmittedClass, Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

theorem all_omitted_classes {D : Nat → Prop} {a : Nat → Int}
    {q M : Nat} {S : List Nat} (hq : 0<q) (bounded : ∀ s∈S, s<q)
    (connected : S.foldl Nat.gcd q=1)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a)
    {h : Int} (missing : Missing a h) : ∀ r, OmittedClass a q r := by
  have one := shift_fold_gcd S q (omitted_period a q)
    (fun s hs => omitted_shift hq (bounded s hs) hs tail rule)
  rw [connected] at one
  exact shift_one_all one ⟨h,missing,rfl⟩

theorem visited_class_bounded {D : Nat → Prop} {a : Nat → Int}
    {q M s : Nat} {S : List Nat} (hq : 0<q) (hs : s<q) (member : s∈S)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a)
    (all : ∀ r, OmittedClass a q r) (r : Int) :
    ∃ B : Nat, ∀ n, a n%(q : Int)=r%(q : Int) → (a n).natAbs≤B := by
  obtain ⟨h,missing,rem⟩ := all (r-(s : Int))
  obtain ⟨U,upper⟩ := upper_class hq hs member tail rule missing
  obtain ⟨k,missingk,remk⟩ := all (r+(s : Int))
  obtain ⟨L,lower⟩ := lower_class hq hs member tail rule missingk
  have eu : (h+(s : Int))%(q : Int)=r%(q : Int) := by
    rw [Int.add_emod, rem, ← Int.add_emod]
    have e : r-(s : Int)+(s : Int)=r := by omega
    rw [e]
  have el : (k-(s : Int))%(q : Int)=r%(q : Int) := by
    rw [Int.sub_emod, remk, ← Int.sub_emod]
    have e : r+(s : Int)-(s : Int)=r := by omega
    rw [e]
  refine ⟨U.natAbs+L.natAbs, ?_⟩
  intro n eq
  have up := upper n (eq.trans eu.symm)
  have lo := lower n (eq.trans el.symm)
  have un := Int.natAbs_eq U
  have ln := Int.natAbs_eq L
  have an := Int.natAbs_eq (a n)
  omega

theorem finite_class_bound {a : Nat → Int} {q : Nat} (hq : 0<q)
    (bounds : ∀ r : Int, ∃ B : Nat, ∀ n,
      a n%(q : Int)=r%(q : Int) → (a n).natAbs≤B) :
    ∃ B : Nat, ∀ n, (a n).natAbs≤B := by
  obtain ⟨B,hb⟩ := finite_eventually
    (fun r K => ∀ n, a n%(q : Int)=(r : Int)%(q : Int) → (a n).natAbs≤K) q
    (by
      intro r _
      obtain ⟨K,hk⟩ := bounds (r : Int)
      exact ⟨K,fun L hl n eq => Nat.le_trans (hk n eq) hl⟩)
  refine ⟨B, ?_⟩
  intro n
  have nonneg := Int.emod_nonneg (a n) (by omega : (q : Int)≠0)
  have less := Int.emod_lt_of_pos (a n) (by omega : (0 : Int)<q)
  let r := (a n%(q : Int)).toNat
  have ri : (r : Int)=a n%(q : Int) := by dsimp [r]; omega
  have rq : r<q := by omega
  apply hb r rq B (Nat.le_refl B) n
  rw [ri, Int.emod_emod]

theorem literal_coverage {D : Nat → Prop} {a : Nat → Int}
    {q M : Nat} {S : List Nat} (hq : 0<q) (nonempty : S≠[])
    (bounded : ∀ s∈S, s<q) (connected : S.foldl Nat.gcd q=1)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a) : Coverage a := by
  have inj := walk_injective ((G06.literal_iff D a).mp rule).2
  intro z
  have visited : ∃ n, a n=z := by
    apply Classical.byContradiction
    intro absent
    have missing : Missing a z := fun n eq => absent ⟨n,eq⟩
    have all := all_omitted_classes hq bounded connected tail rule missing
    have member : ∃ s, s∈S := by
      cases S with
      | nil => exact False.elim (nonempty rfl)
      | cons s xs => exact ⟨s,by simp⟩
    obtain ⟨s,hs⟩ := member
    obtain ⟨B,hb⟩ := finite_class_bound hq
      (visited_class_bounded hq (bounded s hs) hs tail rule all)
    obtain ⟨N,hn⟩ := eventually_outside inj B
    have lo := hn N (Nat.le_refl N)
    have hi := hb N
    omega
  obtain ⟨n,hn⟩ := visited
  exact ⟨n,hn,fun j hj => inj j n (hj.trans hn.symm)⟩

theorem tail_unbounded {D : Nat → Prop} {q M : Nat} {S : List Nat}
    (hq : 0<q) (nonempty : S≠[]) (bounded : ∀ s∈S, s<q)
    (tail : ResidueTail D q M S) : G02.Unbounded D := by
  have member : ∃ s, s∈S := by
    cases S with
    | nil => exact False.elim (nonempty rfl)
    | cons s xs => exact ⟨s,by simp⟩
  obtain ⟨s,hs⟩ := member
  intro N
  let d := s+q*(N+M+1)
  have mul := Nat.mul_le_mul_right (N+M+1) (by omega : 1≤q)
  have large : N<d ∧ M≤d ∧ 0<d := by dsimp [d]; omega
  refine ⟨d,large.1,tail d large.2.2 large.2.1 ?_⟩
  have eq : d%q=s := by dsimp [d]; simp [Nat.add_mod, Nat.mod_eq_of_lt (bounded s hs)]
  rwa [eq]

theorem literal_exists (D : Nat → Prop) (q M : Nat) (S : List Nat)
    (hq : 0<q) (nonempty : S≠[]) (bounded : ∀ s∈S, s<q)
    (connected : S.foldl Nat.gcd q=1) (tail : ResidueTail D q M S) :
    ∃ a, G06.LiteralRule D a ∧ Coverage a ∧
      ∀ b, G06.LiteralRule D b → ∀ n, a n=b n := by
  obtain ⟨a,rule⟩ := G02.unbounded_exists D (tail_unbounded hq nonempty bounded tail)
  have literal := (G06.literal_iff D a).mpr rule
  exact ⟨a,literal,literal_coverage hq nonempty bounded connected tail literal,
    fun b rb => G10.literal_unique literal rb⟩

end G18
