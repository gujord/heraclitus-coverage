import Std

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace G18


def Shift (P : Int → Prop) (d : Int) : Prop := ∀ x, P (x+d) ↔ P x

theorem shift_zero (P : Int → Prop) : Shift P 0 := by
  intro x
  simp

theorem shift_neg {P : Int → Prop} {d : Int} (h : Shift P d) : Shift P (-d) := by
  intro x
  have e : (x + -d) + d = x := by omega
  have k := h (x + -d)
  rw [e] at k
  exact k.symm

theorem shift_add {P : Int → Prop} {c d : Int}
    (hc : Shift P c) (hd : Shift P d) : Shift P (c+d) := by
  intro x
  rw [← Int.add_assoc]
  exact (hd (x+c)).trans (hc x)

theorem shift_nat_mul {P : Int → Prop} {d : Int} (h : Shift P d) (k : Nat) :
    Shift P (d*(k : Int)) := by
  induction k with
  | zero => simpa using shift_zero P
  | succ k ih =>
    simpa [Int.natCast_add, Int.mul_add] using shift_add ih h

theorem shift_int_mul {P : Int → Prop} {d : Int} (h : Shift P d) (k : Int) :
    Shift P (d*k) := by
  cases k with
  | ofNat n => exact shift_nat_mul h n
  | negSucc n =>
    change Shift P (d * -((n+1 : Nat) : Int))
    simpa only [Int.mul_neg] using shift_neg (shift_nat_mul h (n+1))

theorem shift_mod {P : Int → Prop} {a b : Nat}
    (ha : Shift P (a : Int)) (hb : Shift P (b : Int)) :
    Shift P ((a % b : Nat) : Int) := by
  have e : ((a % b : Nat) : Int) = (a : Int) + -((b : Int)*(a/b : Nat)) := by
    have k := Nat.mod_add_div a b
    have kk := congrArg (fun n : Nat => (n : Int)) k
    simp only [Int.natCast_add, Int.natCast_mul] at kk
    omega
  rw [e]
  exact shift_add ha (shift_neg (shift_nat_mul hb (a/b)))

theorem shift_gcd {P : Int → Prop} (a b : Nat)
    (ha : Shift P (a : Int)) (hb : Shift P (b : Int)) :
    Shift P ((Nat.gcd a b : Nat) : Int) := by
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases az : a=0
    · subst a
      simpa using hb
    · rw [Nat.gcd_rec]
      exact ih (b%a) (Nat.mod_lt b (by omega)) a (shift_mod hb ha) ha

theorem shift_fold_gcd {P : Int → Prop} (xs : List Nat) (q : Nat)
    (hq : Shift P (q : Int))
    (hs : ∀ s ∈ xs, Shift P (s : Int)) :
    Shift P ((xs.foldl Nat.gcd q : Nat) : Int) := by
  induction xs generalizing q with
  | nil => exact hq
  | cons s xs ih =>
    exact ih (Nat.gcd q s) (shift_gcd q s hq (hs s (by simp)))
      (fun t ht => hs t (by simp [ht]))

theorem shift_one_all {P : Int → Prop} (h : Shift P 1) {x : Int}
    (hx : P x) (y : Int) : P y := by
  have k := shift_int_mul h (y-x)
  have e : x + 1*(y-x) = y := by omega
  have r := (k x).mpr hx
  rwa [e] at r

end G18
