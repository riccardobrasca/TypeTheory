import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Real

open Real

universe u

section

-- FUNCTION TYPES

-- Formation rule

variable (A B : Type u)

#check A → B

-- Constructor

#check (fun (n : ℕ) ↦ n + 4)

#check (fun (n : ℕ) ↦ π)

example : ℕ → ℕ := by
  intro n
  exact 2 * n + n ^ 2

-- Eliminator

section

variable (a : A) (f : A → B)

#check f a

end

-- Computation rule

example (a : ℝ) : (fun x ↦ sin x) a = sin a := rfl

-- Uniqueness principle

example : f = fun x ↦ f x := rfl

lemma extensionality (g : A → B) (h : ∀ (x : A), f a = f b) : f = g := sorry

#print axioms extensionality

-- Currying

variable (C : Type u) (a : A) (b : B) (f : A → B → C)

#check A → B → C

#check f a b

#check (fun (n : ℕ) ↦ fun (m : ℤ) ↦ n + m)

#check (fun (n : ℕ) (m : ℤ) ↦ n + m)

end

section

-- DEPENDENT PRODUCT

-- Formation rule

section

variable (n : ℕ)

notation R "^" n => (Fin n → R) -- notation to use ℝ^n as a type

#check ℝ^n

#check (n : ℕ) → ℝ^n

-- Constructor

#check (fun (n : ℕ) ↦ (0 : ℝ^n))

example : (n : ℕ) → ℝ^n := by
  intro n
  exact 1

-- Eliminator

variable (A : Type u) (a : A) (B : A → Type u) (f : (x : A) → B x)

#check f a

-- Uniqueness principle

example : f = fun x ↦ f x := rfl

end

-- Identity

def identity : (A : Type u) → A → A := fun (A : Type u) (x : A) ↦ x

#check (A : Type u) → A → A

-- Swap

def swap (C : Type u) : (A : Type u) → (B : Type u) → (A → B → C) → (B → A → C) :=
  fun (A : Type u) (B : Type u) (f : A → B → C) (b : B) (a : A) ↦ f a b

example (C : Type u) : (A : Type u) → (B : Type u) → (A → B → C) → (B → A → C) := by
  intro A
  intro B
  intro f
  intro b
  intro a
  exact f a b

example (A B C : Type u) (f : A → B → C) (a : A) (b : B) : swap C A B f b a = f a b := rfl

end

section

open Prod

-- CARTESIAN PRODUCT

-- Formation rule

variable (A B : Type u) (a : A) (b : B)

#check A × B

-- Constructor

#check (a, b)

-- Eliminator (non-dependent version)

section

variable (C : Type u) (f : A → B → C) (x : A × B)

#check (rec f x : C)

#check (rec f : A × B → C)


-- Computation rule

example (a : A) (b : B) : rec f (a, b) = f a b := rfl 

-- Projections

#check (fst : A × B → A)

#check (fst x)

#check (snd : A × B → B)

#check (snd x)

example : fst (a, b) = a := rfl

end

-- Uniqueness principle

section

variable (C : Type u) (x : A × B)

example : x = (x.1, x.2) := rfl

lemma principle (f : A → B → C) : (rec f : A × B → C) = fun (x : A × B) ↦ f x.1 x.2 := rfl

#print axioms principle

lemma principle1 (f : A → B → C) : (rec f : A × B → C) = fun (x : A × B) ↦ f x.1 x.2 := by
  ext x
  rfl

#print axioms principle1

lemma principle2 (f : A → B → C) : (rec f : A × B → C) = fun (x : A × B) ↦ f x.1 x.2 := by
  have h₁ : f = fun t ↦ f t := rfl
  nth_rewrite 2 [h₁]
  change (fun (t : A × B) ↦ f t.1 t.2) = _
  rfl

#print axioms principle2

lemma principle3 (f : A × B → C) : f = fun (x : A × B) ↦ f (x.1, x.2) := rfl

#print axioms principle3

lemma principle4 (f : A × B → C) : f = fun (x : A × B) ↦ f (x.1, x.2) := by
  change (fun t ↦ f t) = fun x ↦ f x
  rfl

#print axioms principle4

end

-- Eliminator (dependent version)

section

variable (C : A × B → Type u) (f : (a : A) → (b : B) → C (a, b)) (x : A × B)

#check (rec f x : C x)

#check (rec f : (x : A × B) → C x)

-- Computation rule

example (a : A) (b : B) : rec f (a, b) = f a b := rfl 

lemma principle5 : (rec f : (x : A × B) → C x) = fun (x : A × B) ↦ f x.1 x.2 := rfl

lemma principle6 (f : (x : A × B) → C x) : f = fun (x : A × B) ↦ f (x.1, x.2) := rfl

end

end
