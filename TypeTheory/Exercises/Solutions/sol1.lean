import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Real

open Real

section basics

/-Check the type of the natural number `10` and of the integers `-5` and `12`.-/

#check 10

#check -5

#check (12 : ℤ)

/-Check the type of `ℕ` and of `ℝ`. (You can type the symbol `ℕ` writing `\N`.
In general, if you move your cursor over a symbol, VS Code will tell you how to type it.
Very often, if you how to write the symbol in LaTeX, the same command will work.)-/

#check ℕ

#check ℝ

/- Find a term of type `Type 12`. -/

#check (Type 11)

/- Show that any term, of any type, is definitionally equal to itself. -/

example (A : Sort u) (a : A) : a = a := rfl

/- Show that, if `(n : ℕ)`, then `n + 0` is definitionally equal to `n`, but `0 + n` is not.
(Of course `0 + n` is equal to `n`, but the equality is not a definitional equality.) -/

example (n : ℕ) : n + 0 = n := rfl

example (n : ℕ) : 0 + n = n := rfl --gives an error, so the two terms are not definitionally equal

/- Is `(fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (a + 0)` definitionally equal to `a ^ 2 + a`, where `(a : ℕ)`?
Try to answer without using Lean and then check it with Lean.
Do the same for `(fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (0 + a) = a ^ 2 + a` and
`(fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (0 + 4) = 20` -/

--ALL THE FOLLOWING WITH THE `^` SYMBOL GAVE AN ERROR IN THE FIRST VERSION OF THE EXERCISES SHEET
-- BECAUSE OF THE NOTATION INTRODUCED AT THE  BEGINNING OF THE FILE, I DIDN'T REALIZE IT, SORRY.
-- THIS IS NOW FIXED.

example (a : ℕ) : (fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (a + 0) = a ^ 2 + a := rfl

example (a : ℕ) : (fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (0 + a) = a ^ 2 + a := rfl --gives an error, so the two terms are not definitionally equal

example : (fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (0 + 4) = 20 := rfl

/- Check that `π + 0` is not definitionally equal to `π`. -/

example : π + 0 = π := rfl --error

/- Are the functions `(fun (n : ℕ) ↦ (n + 0)^3 + n^2)` and `(fun (m : ℕ) ↦ m^3 + m^2 + 0)`
definitionally equal? (Try yo answer without Lean first, but to really check it write the parentheses,
otherwise Lean will be confused.) Same question for `(fun (x : ℝ) ↦ (x + 0)^3 + x^2)` and
`(fun (y : ℝ) ↦ y^3 + y^2 + 0)` -/

example : (fun (n : ℕ) ↦ (n + 0)^3 + n^2) = (fun (m : ℕ) ↦ m^3 + m^2 + 0) := rfl

example : (fun (x : ℝ) ↦ (x + 0)^3 + x^2) = (fun (y : ℝ) ↦ y^3 + y^2 + 0) := rfl --error

/- What happens if you try to prove that `sin = fun (n : ℕ) ↦ n ^ 2`? Can you explain? -/

example : sin = fun (n : ℕ) ↦ n ^ 2 := rfl --the two terms have different type, so this is not a
-- well formed statement, it doesn't make any sense

end basics

/- Check that the type given by functions between two types of `Type 3` is of `Type 3`. -/

variable (T₁ T₂ : Type 3)

#check (T₁ → T₂)

/- Define the constant function `f`, from `ℝ` to `ℕ`, that sends everything to `3`. -/

def f : ℝ → ℕ := fun x ↦ 3

/- Is `f π` definitionally equal to `3 + 0`? -/

example : f π = 3 + 0 := rfl

/- In the following example you prove that if two functions are equal than their value is the same
at any given point. You need to use the `rw` tactic. The other implication is called functional
extensionality, and it needs an additional axiom to be proven.  -/

example (A B : Type) (f g : A → B) (h : f = g) (a : A) : f a = g a := by
  rw [h]

/- Define the function that takes a natural number `n` and sends it to the constant function,
from `ℝ` to `ℕ`, that sends everything to `n`. -/

example : ℕ → ℝ → ℕ := fun n x ↦ n

/- Define by hand the function `currying` that takes a function `A × B → C` and sends it to the
corresponding function `A → B → C`. Define also a function `uncurrying` in the other direction.
Check that `rfl` proves the two `example` below. Can you explain why we don't need functional
extensionality to prove them? -/

def currying {A B C : Type} (f : A × B → C) : A → B → C := fun a b ↦ f ⟨a, b⟩

def uncurrying {A B C : Type} (f : A → B → C) : A × B → C := fun x ↦ f x.1 x.2

example (A B C : Type) (f : A × B → C) : uncurrying (currying f) = f := rfl

example (A B C : Type) (f : A → B → C) : currying (uncurrying f) = f := rfl

--We don't need functional extensionality because all the equalities are definitional

section functions_type

end functions_type

section dependent_functions

notation R "^" n => (Fin n → R) -- notation to use ℝ^n as a type

/- If `(n : ℕ)`, then `ℝ^n` is the type of real vectors with `n` components. Check that the type
of dependent functions that take a natural number `n` and give a function `(ℝ^n) → (ℝ^n)` is `Type`.
(the parentheses are needed to help Lean.) -/

#check (n : ℕ) → (ℝ^n) → (ℝ^n)

/- Define the function `dep_sum` that takes a natural number `n` and gives the function that takes two
vectors in `ℝ^n` and gives their sum. -/

def dep_sum := fun (n : ℕ) (x : ℝ^n) (y : ℝ^n) ↦ x + y

/- If `(A : Type)` is any type, then `(List A : Type)` is the type of lists of elements of type `A`.
What is the type of `List`? -/

#check (List : (T : Type) → Type)

/- If `(A : Type)` and `(a b : A)` are two terms of type `A`, then `(@Eq A a b : Prop)` is the
proposition `a = b` (we don't care about its definition at the moment, also ignore the `@`).
What is the type of `@Eq`? The Type of `@Eq A`? The type of `@Eq ℕ 3`? -/

variable (A : Type)

#check (@Eq : (A : Type) → (A → A → Prop))

#check (@Eq A : A → A → Prop)

#check (@Eq ℕ 3)

end dependent_functions

section cartesian_product

/- Define the function from `ℕ × ℝ` that sends a pair `(n, x)` to `x^n`. -/

example : ℕ × ℝ → ℝ := fun t ↦ t.2^t.1

/- Using the functions `x ↦ x.1` and `x ↦ x.2` define by hand the eliminator of the Cartesian
product `(eliminator : (A → B → C) → (A × B → C))`. Check that `rfl` prove the example below.
-/

def eliminator (A B C : Type) : (A → B → C) → (A × B → C) := fun f x ↦ f x.1 x.2

example {A B C : Type} (f : A → B → C) (a : A) (b : B) :
  eliminator A B C f ⟨a, b⟩ = f a b := rfl

/- Do the same for the dependent version of the eliminator. -/

def eliminator_dep (A B : Type) (C : A × B → Type) :
  ((a : A) → (b : B) → C ⟨a, b⟩) → ((x : A × B) → C x) := fun f x ↦ f x.1 x.2

example {A B : Type} (C : A × B → Type) (f : (a : A) → (b : B) → C ⟨a, b⟩) (a : A) (b : B) :
  eliminator_dep A B C f ⟨a, b⟩ = f a b := rfl

end cartesian_product

section dependent_pairs

/- What is the type of dependent pairs where the first component is a `Type` and the second
component is a list of element whose type is the first component? Check it in Lean. -/

#check (T : Type) × List T

/- The empty list is denoted `[]`. Define a function, from the type of dependent pairs whose first
component is a type `A` and the second component is a list of elements of type `A`, that sends
a pair `(A, L)` to the proposition saying that `L` is empty. -/

example : (T : Type) × List T → Prop := fun X ↦ X.2 = []

/- Do the last two questions in the Cartesian_product section for the dependent pairs type. -/

def eliminator' (A : Type) (B : A → Type) (C : Type) : ((a : A) → B a → C) → ((a : A) × B a → C) :=
  fun f x ↦ f x.1 x.2

example {A C : Type} (B : A → Type) (f : (a : A) → B a → C) (a : A) (b : B a) :
  eliminator' A B C f ⟨a, b⟩ = f a b := rfl

def eliminator_dep' (A : Type) (B : A → Type) (C : (a : A) × B a → Type) :
  ((a : A) → (b : B a) → C ⟨a, b⟩) → ((x : (a : A) × B a) → C x) := fun f x ↦ f x.1 x.2

example {A : Type} {B : A → Type} (C : (a : A) × B a → Type) (f : (a : A) → (b : B a) → C ⟨a, b⟩)
  (a : A) (b : B a) : eliminator_dep' A B C f ⟨a, b⟩ = f a b := rfl

/- If `(n : ℕ)`, then `(0 : ℝ^n)` is the zero vector with `n` components. Define the function, from
`ℕ` to `(n : ℕ) × ℝ^n`, that sends `n` to the pair `(n, 0)`, where the `0` in the second component
is the zero vectors with `2*n` component. -/

example : ℕ → (n : ℕ) × ℝ^n := fun n ↦ ⟨n, (0 : ℝ^n)⟩

end dependent_pairs

section disjoint_union

/- If `(A B : Type)`, then `A ⊕ B` is the disjoint union of `A` and `B`. -/

variable (A B : Type)

#check A ⊕ B

/- It is again a special case of an inductive type. Write down the formation rule for the disjoint
union. How may constructor do we have in this case? How does the eliminator work in this case?
How many computation rules do we want? Write them (with pen and paper).

--There are two constructors, corresponding to the two inclusions.

The eliminator is called in Lean `Sum.elim`, you can check its type and see if you guessed correctly. -/

#check Sum.elim

/- If `(A B C D : Type)` and  `(f : A → C)`, `(g : B → D)` define, with pen and paper using the
constructors and the eliminator, a function `A ⊕ B → C ⊕ D`. -/

/- Do the same in Lean, where the constructors are called `Sum.inl` and `Sum.inr` (you can check
their type). Doing it in tactic mode can be a little easier, and you may need the `apply` tactic.
This question requires basic familiarity with Lean (nothing more than the natural number game). -/

def mapsum (A B C D : Type) (f : A → C) (g : B → D) : A ⊕ B → C ⊕ D :=
  Sum.elim (fun a ↦ Sum.inl (f a)) (fun b ↦ Sum.inr (g b))

/- Write the computations rules in Lean. -/

example (C : Type) (f : A → C) (g : B → C) (a : A) : Sum.elim f g (Sum.inl a) = f a := rfl

example (C : Type) (f : A → C) (g : B → C) (b : B) : Sum.elim f g (Sum.inr b) = g b := rfl

end disjoint_union

section proposition

/- `Nat.add_zero` is the theorem that for all `(n : ℕ)` we have `n + 0 = n`. What is the type of
`Nat.add_zero 4`? Check it in Lean. -/

#check Nat.add_zero 4

/- Define a dependent function `(n : ℕ) → n + 0 = n` -/

example : (n : ℕ) → n + 0 = n := fun n ↦ Nat.add_zero n

/- Check that the type of dependent functions from `ℕ` to `P n`, where `P n` is a statement about
`n`, is `Prop`. -/

variable (P : ℕ → Prop)

#check ((n : ℕ) → P n)

end proposition

section unit_empty

open PUnit --ignore this

/- Following the same definition as for `True` and `False`, one can define the `Unit` type, with
only one constructor and the `Empty` type.

The constructor for `Unit` allows us to construct a term of type `Unit`, denoted `Unit.unit` or
simply `()`. -/

#check Unit

#check Empty

#check Unit.unit

#check ()

/- Think about the non-dependent eliminator for `Unit`. Is it useful? We now move on to the
non-dependent eliminator. What is is form? Given a function `(f : Unit → Sort u)`, where `u` is a
universe, and a term `T : f unit`, it allows to build a dependent function
`(rec f : (u : Unit) → f u)`. Be sure to understand that this is the form of the dependent eliminator. -/

universe u

variable (f : Unit → Sort u) (T : f ())

#check (rec T : (u : Unit) → f u)

/- The computation rule simply says that `rec T unit = T` definitionally. -/

example : (rec T : (u : Unit) → f u) Unit.unit = T := rfl

/- We can now prove that the only term of type `Unit` is `Unit.unit`, meaning that any `(x : Unit)`
satisfies `x = Unit.unit`. You don't need the precise definition of `a = b`, the only thing you need
is that `@rfl A a : a = a` for all `(a : A)`.

The strategy is the following: to prove that for all `(x : Unit)` we have `x = Unit.unit` we need to
define a (dependent!) function that sends any `(x : Unit)` to a proof that `x = Unit.unit`. But to
define a dependent function from `Unit` we can use the recursor! So first of all we define a function
`f1 : Unit → Prop` that sends `x` to the proposition `x = Unit.unit` (this function will give the
codomain of the dependent function we are looking for). Now, the recursor says that to build a
function `(x : Unit) → f1 x` it is enough to specify a term of type `f1 Unit.unit`. But by definition
of `f1`, `f1 Unit.unit` is the proposition `Unit.unit = Unit.unit`, so `@rfl Unit Unit.unit ` has
the type we want. Implement this in Lean. -/


def f1 : Unit → Prop := fun x ↦ x = ()

example : ∀ (x : Unit), x = Unit.unit := rec (@rfl Unit Unit.unit)

--Lean is even smarter, the following works

example : ∀ (x : Unit), x = Unit.unit := rec rfl

/- Think about the recursor for the `Empty` type and, using the `cases` tactic, construct a function
`Empty → A`, for any given type `A`. -/

example (A : Type) : Empty → A := by
  intro p
  cases p

end unit_empty

section logic

/- Prove (some of) the following theorems in propositional logic.
Remember the basic tactics `intro`, `apply` and `exact`.
You will also need `constructor`, `rcases`, `left` and `right`. -/

example (P : Prop) : P → P := by
  intro p
  exact p

example (P Q R : Prop) : (P → Q → R) → (P → Q) → (P → R) := by
  intro h h1 p
  apply h --here `apply` is smart enough to produce the two goals
  · exact p
  · apply h1
    exact p

example (P Q : Prop) : P → (P → Q) → Q := by
  intro p h
  exact h p

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  intro h hnotQ p
  apply hnotQ
  apply h
  exact p

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example (P Q : Prop) : P ∧ Q → P := by
  intro h
  exact h.1

example (P Q : Prop) : P → P ∨ Q := by
  intro p
  left
  exact p

example (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  constructor
  · intro h
    constructor
    · exact h.2
    · exact h.1
  · intro h
    constructor
    exact h.2
    exact h.1

/- Write down (with pen and paper) the introduction rule, constructors etc for the "if and only if
operator". -/

example (P Q : Prop) : P → Q → P := by
  intro p q
  exact p

example (P Q : Prop) : (P → ¬ Q) → (Q → ¬ P) := by
  intro h q p
  exact h p q

example (P Q : Prop) : P ∧ Q → Q := by
  intro h
  exact h.2

example (P Q : Prop) : P → Q → P ∧ Q := by
  intro p q
  constructor
  exact p
  exact q

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  exact h.2
  exact h.1

example (P Q : Prop) : ¬ P ∨ Q → P → Q := by
  intro h p
  rcases h with (h1 | h2)
  · exfalso
    exact h1 p
  · exact h2

example (P Q R : Prop) : P ∨ (Q ∧ R) → ¬ P → ¬ Q → False := by
  intro h hP hQ
  rcases h with (p | H)
  · exact hP p
  · exact hQ H.1

/- You can use the `norm_num` tactic to prove explicit relations between natural numbers. -/

example : ∃ (n : ℕ), n * 2 > 7 := by
  use 5
  norm_num

/- Using `Nat.zero_ne_one` (you can check its type, but the name is pretty clear...) prove the
following. You may need the `rw` and `apply` tactics. -/

example (h : ∃ (n : ℕ), 0 = n ∧ 1 = n) : False := by
  obtain ⟨n, hn⟩ := h
  apply Nat.zero_ne_one
  rw [hn.1, hn.2]

example : ¬(∃ (n : ℕ), 0 = n ∧ 1 = n) := by
  intro h
  obtain ⟨n, hn⟩ := h
  apply Nat.zero_ne_one
  rw [hn.1, hn.2]

end logic
