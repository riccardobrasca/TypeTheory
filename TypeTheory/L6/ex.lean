import TypeTheory.L4.ex
import Mathlib.Data.Set.Basic

open N Set Function

namespace ex

universe u v
section equality

inductive Eq {A : Sort u} : A → A → Prop
| refl (a : A) : Eq a a

open Eq

infix:50 " ≃ "  => Eq

section eliminator

#check @Eq.rec

variable (A : Sort u) (a b : A) (h : a ≃ b)

#check @Eq.rec A a

variable (P : A → Prop) (ha : P a)

#check @Eq.rec A a (fun b _ ↦ P b)

#check @Eq.rec A a (fun b _ ↦ P b) ha b h

end eliminator

section equivalence

variable (A : Sort u)

lemma reflexivity (a : A) : a ≃ a := by
  exact refl a

lemma symmetry (a b : A) (h : a ≃ b) : b ≃ a := by
  let P : A → Prop := fun x ↦ x ≃ a
  exact Eq.rec (motive := fun x _ ↦ P x) (reflexivity A a) h

lemma transitivity (a b c : A) (hab : a ≃ b) (hbc : b ≃ c) : a ≃ c := by
  let P : A → Prop := fun x ↦ a ≃ x
  exact Eq.rec (motive := fun x _ ↦ P x) hab hbc

end equivalence

lemma substitution (B : Type v) (f : A → B) (a b : A) (h : a ≃ b) :
    f a ≃ f b := by
  let P : A → Prop := fun x ↦ f a ≃ f x
  exact Eq.rec (motive := fun x _ ↦ P x) (reflexivity B (f a)) h

example (R : A → A → Prop) (hrefl : ∀ a, R a a) (a b : A) (h : a ≃ b) : R a b := by
  let P : A → Prop := fun x ↦ R a x
  exact Eq.rec (motive := fun x _ ↦ P x) (hrefl a) h

example : ∀ (x : N), x ≃ x + 0  := by
  apply N.rec
  · exact Eq.refl _
  · intro d h
    have : succ (d + 0) ≃ succ d + 0 := Eq.refl _
    refine transitivity _ _ _ _ ?_ this
    apply substitution
    exact h

example : ∀ (x : N), x ≃ x + 0  := by
  apply N.rec
  · exact Eq.refl 0
  · intro d h
    have : succ d + 0 ≃ succ (d + 0) := Eq.refl _
    refine Eq.rec (motive := fun n _ ↦ succ d ≃ n) ?_ this
    exact Eq.rec (motive := fun n _ ↦ succ d ≃ succ n) (Eq.refl _) h

example (a b : A) (h h' : a ≃ b) : h ≃ h' := by
  exact Eq.refl _

example (a b : A) (h h' : a ≃ b) : h ≃ h' := by
  let M := fun (x : A) (e : a ≃ x) ↦ ∀ (e' : a ≃ x), e ≃ e'
  apply Eq.rec (motive := M)
  intro e'
  let N := fun (x : A) (f : a ≃ x) ↦ Eq.refl a ≃ e'
  refine Eq.rec (motive := N) ?_ e'
  sorry

end equality

section set

section basic

variable (A : Type u) (S T : Set A)

example : Set A = (A → Prop) := rfl

example : S ∪ T = fun a ↦ S a ∨ T a := rfl

example : S ∩ T = fun a ↦ S a ∧ T a := rfl

example : (∅ : Set A) = fun _ ↦ False := rfl

example : (univ : Set A) = fun _ ↦ True := rfl

example (a : A) : (a ∈ S) = S a := rfl

example : (S ⊆ T) = ∀ a, S a → T a := rfl

example : S ⊆ T ↔ ∀ a, a ∈ S → a ∈ T := Iff.rfl

example : Sᶜ = fun a ↦ ¬(S a) := rfl

example : S \ T = fun a ↦ S a ∧ ¬(T a) := rfl

example : S ⊆ S := by
  intro a ha
  exact ha

example (R : Set A) (hST : S ⊆  T) (hTR : T ⊆  R) : S ⊆  R := by
  intro a ha
  apply hTR
  apply hST
  exact ha

variable (t : S)

#check t --note the arrow

example (a : A) (ha : a ∈ S) (h : S = T) : a ∈ T := by
  rw [h] at ha
  exact ha

example (h : S = T) : ∀ a, a ∈ S ↔ a ∈ T := by
  intro a
  constructor
  · intro ha
    rwa [h] at ha
  · intro ha
    rwa [← h] at ha

example (h : ∀ a, a ∈ S ↔ a ∈ T) : S = T := by
  ext x
  exact h x

end basic

lemma iff_not_self (P : Prop) : ¬(P ↔ ¬P) := by
  intro H
  apply H.1
  · apply H.2
    intro p
    apply H.1
    · exact p
    · exact p
  · exact H.2 (fun p ↦ H.1 p p)

lemma not_surjective (A : Type u) (f : A → Set A) : ¬Surjective f := by
  intro hf
  let X := {a | ¬(a ∈ f a)}
  obtain ⟨x, hx⟩ := hf X
  apply iff_not_self (x ∈ X)
  constructor
  · intro H
    rw [← hx]
    exact H
  · intro H
    show ¬(x ∈ f x)
    rw [hx]
    exact H

lemma not_injective (A : Type u) (g : Set A → A) : ¬Injective g := by
  intro hg
  let f : A → Set A := fun a ↦ {b | ∀ U, a = g U → U b}
  have hfg : Function.RightInverse g f := by
    intro U
    ext x
    constructor
    · intro hx
      exact hx U rfl
    · intro hx
      intro U1 hU1
      rw [← hg hU1]
      exact hx
  apply not_surjective _ f
  exact RightInverse.surjective hfg

end set

end ex
