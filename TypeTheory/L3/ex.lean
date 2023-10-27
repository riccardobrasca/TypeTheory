import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

section propositions

#check (2 + 2 = 4)

#check (1 < 0)

#check Prop

def FLT := ∀ (n x y z), n > 2 → x^n+y^n=z^n → x*y*z=0

#check FLT

variable (P : Prop) (p : P)

#check p

#check Sort 0 --note that Lean automatically replace Sort 0 with Prop

variable (p₁ : 2 + 2 = 4) (p₂ : 2 + 2 = 5)

#check p₁

#check p₂

theorem easy : 1 + 1 = 2 := by rfl

#check easy

theorem FLT_theorem (n x y z : ℕ) (hn : n > 2) (H : x^n+y^n=z^n) : x*y*z = 0 := by sorry

variable (n x y z : ℕ) (hn : n > 2) (H : x^n+y^n=z^n)

#check FLT_theorem n x y z hn H

variable (A B : Type u) (C : Type v) (D : A → Type v)

#check (A → B)

#check (A → C)

#check (a : A) → D a

end propositions

section implication

variable (P : A → Prop)

example : ∀ n, n + 0 = n := by
  intro n
  rfl

#check (a : A) → P a

variable (A : Sort u) (B : A → Sort v)

#check (a : A) → B a

variable (P Q : Prop)

#check (A → Q)

#check (P → Q)

example : P → Q := by
  intro p
  sorry

example (p : P) (h : P → Q) : Q := by
  exact h p

example (p : P) (h : P → Q) : Q := by
  apply h
  exact p

end implication

section and

variable (P Q : Prop)

#check (P ∧ Q)

variable (p : P) (q : Q)

#check (⟨p, q⟩: P ∧ Q)

example : P ∧ Q := by
  exact ⟨p, q⟩

example : P ∧ Q := by
  constructor
  · exact p
  · exact q

variable (A : Sort u) (f : P → Q → A)

#check And.elim f

example : And.elim f ⟨p, q⟩ = f p q := rfl

variable (t : P ∧ Q)

#check t.1

#check t.2

example : t = ⟨t.1, t.2⟩ := rfl

end and

section double_imp

variable (P Q : Prop)

#check (P ↔ Q)

variable (h1 : P → Q) (h2 : Q → P)

#check (⟨h1, h2⟩: P ↔ Q)

end double_imp

section or

variable (P Q : Prop)

#check (P ∨ Q)

section rules

variable (p : P) (q : Q)

#check Or.intro_left Q p

#check Or.intro_right P q

variable (R : Prop) (f : P → R) (g : Q → R) (t : P ∨ Q)

#check (Or.elim t f g)

example : Or.elim (Or.intro_left Q p) f g = f p := rfl

example : Or.elim (Or.intro_right P q) f g = g q := rfl

end rules

example (p : P) : P ∨ Q := by
  left
  exact p

example (q : Q) : P ∨ Q := by
  right
  exact q

example (R : Prop) (hP : P → R) (hQ : Q → R) (t : P ∨ Q) : R := by
  cases t with
  | inl p => apply hP
             exact p
  | inr q => apply hQ
             exact q

example (R : Prop) (hP : P → R) (hQ : Q → R) (t : P ∨ Q) : R := by
  cases t
  · apply hP
    assumption
  · apply hQ
    assumption

example (R : Prop) (hP : P → R) (hQ : Q → R) (t : P ∨ Q) : R := by
  rcases t with (p | q)
  · exact hP p
  · exact hQ q

end or

section true

#check True

example : True := by
  trivial

end true

section false

section eliminator

#check False

variable (A : sort u) (p : False)

#check (False.elim p : A)

end eliminator

example (p : False) : FLT := by
  intro n x y z hn H
  exfalso
  exact p

example (p : False) : FLT := by
  cases p

end false

section negation

variable (P : Prop)

#check ¬P

example : ¬P := by
  intro h
  sorry

end negation

section existential

variable (A : Sort u) (P : A → Prop)

#check (∃ a, P a)

variable (x : A) (h : P x)

#check (⟨x, h⟩ : ∃ a, P a)

example : ∃ n, n ^ 2 = 1 := by
  use 1
  simp

variable (Q : Prop) (h1 : ∃ a, P a) (h2 : ∀ a, P a → Q)

#check (Exists.elim h1 h2)


example (H : ∃ (x : ℝ), 2 = x^2) : (0 : ℝ) ≤ 2 := by
  obtain ⟨x, hx⟩ := H
  rw [hx]
  exact sq_nonneg x

end existential
