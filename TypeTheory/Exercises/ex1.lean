import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Real

open Real

section basics

/-Check the type of the natural number `10` and of the integers `-5` and `12`.-/

/-Check the type of `ℕ` and of `ℝ`. (You can type the symbol `ℕ` writing `\N`.
In general, if you move your cursor over a symbol, VS Code will tell you how to type it.
Very often, if you how to write the symbol in LaTeX, the same command will work.)-/

/- Find a term of type `Type 12`. -/

/- Show that any term, of any type, is definitionally equal to itself. -/

/- Show that, if `(n : ℕ)`, then `n + 0` is definitionally equal to `n`, but `0 + n` is not.
(Of course `0 + n` is equal to `n`, but the equality is not a definitional equality.) -/

/- Is `(fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (a + 0)` definitionally equal to `a ^ 2 + a`, where `(a : ℕ)`?
Try to answer without using Lean and then check it with Lean.
Do the same for `(fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (0 + a) = a ^ 2 + a` and
`(fun (n : ℕ) ↦ (n + 0) ^ 2 + n) (0 + 4) = 20` -/

/- Check that `π + 0` is not definitionally equal to `π`. -/

/- Are the functions `(fun (n : ℕ) ↦ (n + 0)^3 + n^2)` and `(fun (m : ℕ) ↦ m^3 + m^2 + 0)`
definitionally equal? (Try yo answer without Lean first, but to really check it write the parentheses,
otherwise Lean will be confused.) Same question for `(fun (x : ℝ) ↦ (x + 0)^3 + x^2)` and
`(fun (y : ℝ) ↦ y^3 + y^2 + 0)` -/

/- What happens if you try to prove that `sin = fun (n : ℕ) ↦ n ^ 2`? Can you explain? -/

end basics

/- Check that the type given by functions between two types of `Type 3` is of `Type 3`. -/

/- Define the constant function `f`, from `ℝ` to `ℕ`, that sends everything to `3`. -/

/- Is `f π` definitionally equal to `3 + 0`? -/

/- In the following example you prove that if two functions are equal than their value is the same
at any given point. You need to use the `rw` tactic. The other implication is called functional
extensionality, and it needs an additional axiom to be proven.  -/

example (A B : Type) (f g : A → B) (h : f = g) (a : A) : f a = g a := by
  sorry

/- Define the function that takes a natural number `n` and sends it to the constant function,
from `ℝ` to `ℕ`, that sends everything to `n`. -/

/- Define by hand the function `currying` that takes a function `A × B → C` and sends it to the
corresponding function `A → B → C`. Define also a function `uncurrying` in the other direction.
Check that `rfl` proves the two `example` below. Can you explain why we don't need functional
extensionality to prove them? -/

def currying {A B C : Type} (f : A × B → C) : A → B → C := sorry

def uncurrying {A B C : Type} (f : A → B → C) : A × B → C := sorry

example (A B C : Type) (f : A × B → C) : uncurrying (currying f) = f := sorry

example (A B C : Type) (f : A → B → C) : currying (uncurrying f) = f := sorry

section functions_type

end functions_type

section dependent_functions

notation R "^" n => (Fin n → R) -- notation to use ℝ^n as a type

/- If `(n : ℕ)`, then `ℝ^n` is the type of real vectors with `n` components. Check that the type
of dependent functions that take a natural number `n` and give a function `(ℝ^n) → (ℝ^n)` is `Type`.
(the parentheses are needed to help Lean.) -/

/- Define the function `dep_sum` that takes a natural number `n` and gives the function that takes two
vectors in `ℝ^n` and gives their sum. -/

/- If `(A : Type)` is any type, then `(List A : Type)` is the type of lists of elements of type `A`.
What is the type of `List`? -/

/- If `(A : Type)` and `(a b : A)` are two terms of type `A`, then `(@Eq A a b : Prop)` is the
proposition `a = b` (we don't care about its definition at the moment, also ignore the `@`).
What is the type of `@Eq`? The Type of `@Eq A`? The type of `@Eq ℕ 3`? -/

end dependent_functions

section cartesian_product

/- Define the function from `ℕ × ℝ` that sends a pair `(n, x)` to `x^n`. -/

/- Using the functions `x ↦ x.1` and `x ↦ x.2` define by hand the eliminator of the Cartesian
product `(eliminator : (A → B → C) → (A × B → C))`. Check that `rfl` prove the example below.
-/

def eliminator (A B C : Type) : (A → B → C) → (A × B → C) := sorry

example {A B C : Type} (f : A → B → C) (a : A) (b : B) :
  eliminator A B C f ⟨a, b⟩ = f a b := sorry

/- Do the same for the dependent version of the eliminator. -/

end cartesian_product

section dependent_pairs

/- What is the type of dependent pairs where the first component is a `Type` and the second
component is a list of element whose type is the first component? Check it in Lean. -/

/- The empty list is denoted `[]`. Define a function, from the type of dependent pairs whose first
component is a type `A` and the second component is a list of elements of type `A`, that sends
a pair `(A, L)` to the proposition saying that `L` is empty. -/

/- Do the last two questions in the Cartesian_product section for the dependent pairs type. -/

/- If `(n : ℕ)`, then `(0 : ℝ^n)` is the zero vector with `n` components. Define the function, from
`ℕ` to `(n : ℕ) × ℝ^n`, that sends `n` to the pair `(n, 0)`, where the `0` in the second component
is the zero vectors with `n` component. -/

end dependent_pairs

section disjoint_union

/- If `(A B : Type)`, then `A ⊕ B` is the disjoint union of `A` and `B`. -/

variable (A B : Type)

#check A ⊕ B

/- It is again a special case of an inductive type. Write down the formation rule for the disjoint
union. How may constructor do we have in this case? How does the eliminator work in this case?
How many computation rules do we want? Write them (with pen and paper).

The eliminator is called in Lean `Sum.elim`, you can check its type and see if you guessed correctly. -/

/- If `(A B C D : Type)` and  `(f : A → C)`, `(g : B → D)` define, with pen and paper using the
constructors and the eliminator, a function `A ⊕ B → C ⊕ D`. -/

/- Do the same in Lean, where the constructors are called `Sum.inl` and `Sum.inr` (you can check
their type). Doing it in tactic mode can be a little easier, and you may need the `apply` tactic.
This question requires basic familiarity with Lean (nothing more than the natural number game). -/

def mapsum (A B C D : Type) (f : A → C) (g : B → D) : A ⊕ B → C ⊕ D := by
  sorry

/- Write the computations rules in Lean. -/

end disjoint_union

section proposition

/- `Nat.add_zero` is the theorem that for all `(n : ℕ)` we have `n + 0 = n`. What is the type of
`Nat.add_zero 4`? Check it in Lean. -/

/- Define a dependent function `(n : ℕ) → n + 0 = n` -/

example : (n : ℕ) → n + 0 = n := sorry

/- Check that the type of dependent functions from `ℕ` to `P n`, where `P n` is a statement about
`n`, is `Prop`. -/

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

example : ∀ (x : Unit), x = Unit.unit := sorry

/- Think about the recursor for the `Empty` type and, using the `cases` tactic, construct a function
`Empty → A`, for any given type `A`. -/

example (A : Type) : Empty → A := by
  sorry

end unit_empty

section logic

/- Prove (some of) the following theorems in propositional logic.
Remember the basic tactics `intro`, `apply` and `exact`.
You will also need `constructor`, `rcases`, `left` and `right`. -/

example (P : Prop) : P → P := by
  sorry

example (P Q R : Prop) : (P → Q → R) → (P → Q) → (P → R) := by
  sorry

example (P Q : Prop) : P → (P → Q) → Q := by
  sorry

example (P Q : Prop) : (P → Q) → (¬ Q → ¬ P) := by
  sorry

example (P Q : Prop) (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

example (P Q : Prop) : P ∧ Q → P := by
  sorry

example (P Q : Prop) : P → P ∨ Q := by
  sorry

example (P Q : Prop) : (P ∧ Q) ↔ (Q ∧ P) := by
  sorry

/- Write down (with pen and paper) the introduction rule, constructors etc for the "if and only if
operator". -/

example (P Q : Prop) : P → Q → P := by
  sorry

example (P Q : Prop) : (P → ¬ Q) → (Q → ¬ P) := by
  sorry

example (P Q : Prop) : P ∧ Q → Q := by
  sorry

example (P Q : Prop) : P → Q → P ∧ Q := by
  sorry

example (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

example (P Q : Prop) : ¬ P ∨ Q → P → Q := by
  sorry

example (P Q R : Prop) : P ∨ (Q ∧ R) → ¬ P → ¬ Q → False := by
  sorry

/- You can use the `norm_num` tactic to prove explicit relations between natural numbers. -/

example : ∃ (n : ℕ), n * 2 > 7 := by
  use 5
  norm_num

/- Using `Nat.zero_ne_one` (you can check its type, but the name is pretty clear...) prove the
following. You may need the `rw` and `apply` tactics. -/

example (h : ∃ (n : ℕ), 0 = n ∧ 1 = n) : False := by
  sorry

example : ¬(∃ (n : ℕ), 0 = n ∧ 1 = n) := by
  sorry

end logic
