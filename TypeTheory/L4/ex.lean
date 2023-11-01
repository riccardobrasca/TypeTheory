import Mathlib.Tactic
import Mathlib.Util.PiNotation
open scoped PiNotation
universe u

/-- Our copy of the natural numbers called `N` -/
inductive N : Type where
| zero : N
| succ : N → N

namespace N

section constructor

#check zero

#check succ

variable (n : N)

#check succ n

end constructor

section notations

/-- This activate the notation `(0 : N)`. -/
instance : Zero N := ⟨zero⟩

theorem zero_def : zero = 0 := rfl

/-- Let's define `one` as `succ 0`. -/
def one : N := succ 0

/-- This activate the notation `(1 : N)`. -/
instance : One N := ⟨one⟩

theorem one_def : one = 1 := rfl

theorem one_eq_succ_zero : (1 : N) = succ 0 := rfl

def two : N := succ 1

theorem two_eq_succ_one : two = succ 1 := rfl

def three : N := succ two

theorem three_eq_succ_two : three = succ two := rfl

def four : N := succ three

theorem four_eq_succ_three : four = succ three := rfl

end notations

section eliminator

variable (M : N → Sort u)

variable (z : M 0) (s : Π (n : N), M n → M (succ n))
--Note that the notation `Π` works

#check (rec z s : Π (n : N), M n)
--here Lean is not smart enough to guess

#check (rec (motive := M) z s)
--one can help Lean writing `(motive := M)`

variable (n : N)

#check (rec (motive := M) z s n)

--ignore the `@`, it means that we want all the variables explicit
#check (@rec : Π (M : N → Sort u), M 0 → (Π (n : N), (M n → M (succ n))) → Π (n : N), M n)

end eliminator

section computation_rules

variable (M : N → Sort u) (z : M 0)
  (s : Π (n : N), M n → M (succ n))

example : rec (motive := M) z s 0 = z := rfl

example (n : N) : rec (motive := M) z s (succ n) = s n (rec z s n) := rfl

end computation_rules

section eliminator_type

variable (A : Type u)

variable (z : A) (s : N → A → A)

#check (rec (motive := fun _ ↦ A) z s)
--we say that the motive is the constant function `A`

#check (rec z s : N → A)
--or we can help Lean like this

example : rec z s 0 = z := rfl

example (n : N) : rec z s (succ n) = s n (rec z s n) := rfl

end eliminator_type

section pattern_matching

variable (M : N → Sort u) (z : M 0)
  (s : Π (n : N), M n → M (succ n))

noncomputable --ignore this
def f : Π (n : N), M n := rec z s

example (n : N) : f M z s (succ n) = s n (rec z s n) := rfl

def f1 : Π (n : N), M n
| 0 => z
| succ n => s n (f1 n)

example (n : N) : f1 M z s (succ n) = s n (f1 M z s n) := rfl

end pattern_matching

section double

def s : N → N → N := fun a b ↦ succ (succ b)

noncomputable
def double : N → N := rec 0 s

theorem double_zero : double 0 = 0 := rfl

theorem double_succ (n : N) : double (succ n) = succ (succ (double n)) := rfl

theorem double_one : double 1 = two := by
  rw [one_eq_succ_zero]
  rw [double_succ 0]
  rw [double_zero]
  rfl

theorem double_two : double two = four := by
  rw [two_eq_succ_one]
  rw [double_succ 1]
  rw [double_one]
  rw [two_eq_succ_one]
  rw [one_eq_succ_zero]
  rfl

example : double two = four := rfl

def double' : N → N
| 0 => 0
| succ n => succ (succ (double' n))

theorem double'_zero : double' 0 = 0 := rfl

theorem double'_succ (n : N) : double' (succ n) = succ (succ (double' n)) := rfl

theorem double'_one : double' 1 = two := rfl

theorem double'_two : double' two = four := rfl

end double

section addition

def add' : N → N → N
| 0 => id
| succ n => fun a ↦ succ (add' n a)

/- Pattern matching is smart enough to use several variables. -/
def add : N → N → N
| 0, a => a
| succ n, a => succ (add n a)

/- This activates the notation `a + b` for `add a b`. -/
instance : Add N := ⟨add⟩

/-The computation rules give us the following results for free.-/

theorem zero_add (a : N) : 0 + a = a := rfl

theorem succ_add (a b : N) : succ a + b = succ (a + b) := rfl

/- These are also definitional equalities. -/

theorem one_add_one_eq_two : 1 + 1 = two := rfl

theorem two_add_two_eq_four : two + two = four := rfl

/- The following equality is not definitional! -/
theorem add_zero : ∀ (a : N), a + 0 = a := by
  apply rec
  · exact zero_add 0
  · intro a ha
    rw [succ_add, ha]
    --We will see how `rw` works, it is related to the definition of `=`.

example : ∀ (a : N), a + 0 = a := by
  intro a
  induction a with
  | zero => rfl
  | succ d hd => --here one can replace `succ` by `_`,
                --no need to know the name of the consuctor
    rw [succ_add, hd]

theorem add_succ (a b : N) : a + (succ b) = succ (a + b) := by
  induction a with
  | zero => rfl
  | _ d hd =>
    rw [succ_add, hd]
    rfl

theorem succ_eq_add_one (a : N) : succ a = a + 1 := by
  rw [one_eq_succ_zero, add_succ, add_zero]

theorem add_comm (a b : N) : a + b = b + a := by
  induction a with
  | zero => rw [zero_def, zero_add, add_zero]
  | _ d hd =>
    rw [succ_add, hd, add_succ]

theorem one_add_eq_succ (a : N) : 1 + a = succ a := by
  rw [add_comm, succ_eq_add_one]

theorem add_assoc (a b c : N) : a + b + c = a + (b + c) := by
  induction a with
  | zero => rw [zero_def, zero_add, zero_add]
  | _ d hd => rw [succ_add, succ_add, hd, succ_add]

theorem double_eq_add_self (a : N) : double a = a + a := by
  induction a with
  | zero =>
    rw [zero_def, double_zero, add_zero]
  | _ d hd =>
    rw [add_succ, succ_add, double_succ, hd]

end addition

section inj

def pred : N → N
| 0 => 0
| succ n => n

theorem pred_succ (n : N) : pred (succ n) = n := rfl

theorem pred_zero : pred 0 = 0 := rfl

theorem succ_inj (a b : N) (h : succ a = succ b) : a = b := by
  have H : pred (succ a) = pred (succ b) := by
    rw [h]
  rw [pred_succ, pred_succ] at H
  exact H

end inj

section ne

theorem true_ne_false : True ≠ False := by
  intro h
  rw [← h]
  trivial

theorem zero_ne_one : (0 : N) ≠ 1 := by
  intro h
  let f : N → Prop :=
    N.rec False (fun a b => True)
  have hzero : f 0 = False := rfl
  have hone : f 1 = True := rfl
  rw [h, hone] at hzero
  exact true_ne_false hzero

theorem succ_ne_zero (n : N) : succ n ≠ 0 := by
  intro h
  let f : N → Prop :=
    N.rec False (fun a b => True)
  have hzero : f 0 = False := rfl
  have hn : f (succ n) = True := rfl
  rw [← h, hn] at hzero
  exact true_ne_false hzero

example : ¬(∃ (n : N), succ n = 0) := by
  rintro ⟨n, hn⟩
  --this is the same as `intro n` followed by `obtain ⟨n, hn⟩ := h`
  exact succ_ne_zero n hn

end ne

end N
