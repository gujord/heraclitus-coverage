import CofiniteResults
import ResidueAlgebra

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G18
open G01

def ResidueTail (D : Nat → Prop) (q M : Nat) (S : List Nat) : Prop :=
  ∀ d, 0 < d → M ≤ d → d%q ∈ S → D d

def Missing (a : Nat → Int) (h : Int) : Prop := ∀ n, a n ≠ h

def OmittedClass (a : Nat → Int) (q : Nat) (r : Int) : Prop :=
  ∃ h, Missing a h ∧ h % (q : Int) = r % (q : Int)

theorem eventually_ne {a : Nat → Int}
    (inj : ∀ i j, a i=a j → i=j) (x : Int) :
    ∃ N, ∀ n, N ≤ n → a n ≠ x := by
  by_cases hit : ∃ i, a i=x
  · obtain ⟨i,hi⟩ := hit
    refine ⟨i+1, ?_⟩
    intro n hn eq
    have k := inj n i (eq.trans hi.symm)
    omega
  · exact ⟨0, fun n _ eq => hit ⟨n,eq⟩⟩

theorem finite_eventually (P : Nat → Nat → Prop) (q : Nat)
    (h : ∀ r, r<q → ∃ N, ∀ n, N≤n → P r n) :
    ∃ N, ∀ r, r<q → ∀ n, N≤n → P r n := by
  induction q with
  | zero => exact ⟨0, by omega⟩
  | succ q ih =>
    obtain ⟨N,hn⟩ := ih (fun r hr => h r (by omega))
    obtain ⟨K,hk⟩ := h q (by omega)
    refine ⟨N+K, ?_⟩
    intro r hr n hi
    by_cases less : r<q
    · exact hn r less n (by omega)
    · have eq : r=q := by omega
      subst r
      exact hk n (by omega)

theorem eventually_outside {a : Nat → Int}
    (inj : ∀ i j, a i=a j → i=j) (B : Nat) :
    ∃ N, ∀ n, N≤n → B < (a n).natAbs := by
  obtain ⟨N,hn⟩ := finite_eventually
    (fun r n => a n ≠ (r : Int)-(B : Int)) (2*B+1)
    (fun r _ => eventually_ne inj ((r : Int)-(B : Int)))
  refine ⟨N, ?_⟩
  intro n hi
  apply Classical.byContradiction
  intro small
  have ab := Int.natAbs_eq (a n)
  have code : (a n+(B : Int)).toNat < 2*B+1 := by omega
  have eq : a n = ((a n+(B : Int)).toNat : Int)-(B : Int) := by omega
  exact hn _ code n hi eq

theorem prefix_bound (a : Nat → Int) (N : Nat) :
    ∃ B : Nat, ∀ n, n<N → (a n).natAbs ≤ B := by
  induction N with
  | zero => exact ⟨0, by omega⟩
  | succ N ih =>
    obtain ⟨B,hb⟩ := ih
    refine ⟨B+(a N).natAbs, ?_⟩
    intro n hn
    by_cases less : n<N
    · have k := hb n less
      omega
    · have eq : n=N := by omega
      subst n
      omega

theorem missing_avoids {D : Nat → Prop} {a : Nat → Int} {h : Int}
    (rule : G06.LiteralRule D a) (missing : Missing a h) :
    ∃ N, ∀ n, N≤n → ¬ D (h-a n).natAbs := by
  have inj := walk_injective ((G06.literal_iff D a).mp rule).2
  obtain ⟨N,hn⟩ := eventually_outside inj h.natAbs
  refine ⟨N, ?_⟩
  intro n hi hd
  have unused : ¬∃ i, i≤n ∧ a i=h := by
    rintro ⟨i,_,eq⟩
    exact missing i eq
  have small := ((rule.2 n).2.2 h unused hd).1
  have large := hn (n+1) (by omega)
  omega

theorem class_difference {q s : Nat} (_hq : 0<q) (hs : s<q)
    {x h : Int} (eq : x % (q : Int) = (h+(s : Int)) % (q : Int)) :
    (x-h) % (q : Int) = (s : Int) := by
  calc
    (x-h) % (q : Int) = (x%(q : Int)-h%(q : Int))%(q : Int) := Int.sub_emod ..
    _ = ((h+(s : Int))%(q : Int)-h%(q : Int))%(q : Int) := by rw [eq]
    _ = ((h+(s : Int))-h)%(q : Int) := (Int.sub_emod ..).symm
    _ = (s : Int) := by
      have e : h+(s : Int)-h = (s : Int) := by omega
      rw [e]
      exact Int.emod_eq_of_lt (by omega) (by omega)

theorem positive_distance_mod {x : Int} {q s : Nat}
    (pos : 0≤x) (mod : x%(q : Int)=(s : Int)) : x.natAbs%q=s := by
  have ab := Int.natAbs_eq x
  have eq : (x.natAbs : Int)=x := by omega
  have cast : ((x.natAbs%q : Nat) : Int)=(s : Int) := by
    rw [Int.natCast_emod, eq, mod]
  omega

theorem upper_class {D : Nat → Prop} {a : Nat → Int} {h : Int}
    {q M s : Nat} {S : List Nat} (hq : 0<q) (hs : s<q) (member : s∈S)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a)
    (missing : Missing a h) :
    ∃ B : Int, ∀ n, a n % (q : Int)=(h+(s : Int))%(q : Int) → a n≤B := by
  obtain ⟨N,avoid⟩ := missing_avoids rule missing
  obtain ⟨B,bound⟩ := prefix_bound a N
  refine ⟨(B : Int)+(h.natAbs : Int)+(M : Int)+1, ?_⟩
  intro n eq
  have ah := Int.natAbs_eq h
  have an := Int.natAbs_eq (a n)
  by_cases early : n<N
  · have k := bound n early
    omega
  · apply Classical.byContradiction
    intro large
    have dif := Int.natAbs_eq (a n-h)
    have pos : 0<a n-h := by omega
    have rem := positive_distance_mod (by omega : 0≤a n-h) (class_difference hq hs eq)
    have hd : D (a n-h).natAbs := tail _ (by omega) (by omega) (by rwa [rem])
    have hd' : D (h-a n).natAbs := by simpa only [difference_symm] using hd
    exact avoid n (by omega) hd'

theorem lower_class {D : Nat → Prop} {a : Nat → Int} {h : Int}
    {q M s : Nat} {S : List Nat} (hq : 0<q) (hs : s<q) (member : s∈S)
    (tail : ResidueTail D q M S) (rule : G06.LiteralRule D a)
    (missing : Missing a h) :
    ∃ B : Int, ∀ n, a n % (q : Int)=(h-(s : Int))%(q : Int) → B≤a n := by
  obtain ⟨N,avoid⟩ := missing_avoids rule missing
  obtain ⟨B,bound⟩ := prefix_bound a N
  refine ⟨-((B : Int)+(h.natAbs : Int)+(M : Int)+1), ?_⟩
  intro n eq
  have ah := Int.natAbs_eq h
  have an := Int.natAbs_eq (a n)
  by_cases early : n<N
  · have k := bound n early
    omega
  · apply Classical.byContradiction
    intro small
    have dif := Int.natAbs_eq (h-a n)
    have pos : 0<h-a n := by omega
    have eq' : h%(q : Int)=(a n+(s : Int))%(q : Int) := by
      rw [Int.add_emod, eq, ← Int.add_emod]
      have e : h-(s : Int)+(s : Int)=h := by omega
      rw [e]
    have rem := positive_distance_mod (by omega : 0≤h-a n) (class_difference hq hs eq')
    exact avoid n (by omega) (tail _ (by omega) (by omega) (by rwa [rem]))

theorem class_above (q : Nat) (hq : 0<q) (r B : Int) :
    ∃ x : Int, B<x ∧ x%(q : Int)=r%(q : Int) := by
  let k : Int := (B.natAbs : Int)+(r.natAbs : Int)+1
  have kp : 0≤k := by dsimp [k]; omega
  have mul := Int.mul_le_mul_of_nonneg_right (by omega : (1 : Int)≤(q : Int)) kp
  have bb := Int.natAbs_eq B
  have rr := Int.natAbs_eq r
  refine ⟨r+(q : Int)*k, ?_, ?_⟩
  · dsimp [k] at *
    omega
  · simp [Int.add_emod]

theorem class_below (q : Nat) (hq : 0<q) (r B : Int) :
    ∃ x : Int, x<B ∧ x%(q : Int)=r%(q : Int) := by
  obtain ⟨x,hx,rem⟩ := class_above q hq (-r) (-B)
  refine ⟨-x, by omega, ?_⟩
  have e : (0-x)%(q : Int)=(0-(-r))%(q : Int) := by
    calc
      (0-x)%(q : Int) = (0%(q : Int)-x%(q : Int))%(q : Int) := Int.sub_emod ..
      _ = (0%(q : Int)-(-r)%(q : Int))%(q : Int) := by rw [rem]
      _ = (0-(-r))%(q : Int) := (Int.sub_emod ..).symm
  simpa using e

end G18
