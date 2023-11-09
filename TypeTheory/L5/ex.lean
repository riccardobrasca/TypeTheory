import TypeTheory.L4.ex
open scoped PiNotation

section proof_irrelevance

example (P : Prop) (p q : P) : p = q := rfl

end proof_irrelevance

namespace Example

variable (A : Type)

inductive Inhabited (A : Type) : Type
| intro (val : A) : Inhabited A

inductive Nonempty (A : Type) : Prop
| intro (val : A) : Nonempty A

namespace Inhabited

universe u

variable (A : Type) (a : A) (B : Sort u) (f : A → B)

#check Inhabited A

#check (⟨a⟩ : Inhabited A)

#check (rec f : Inhabited A → B)

example : rec f ⟨a⟩ = f a := rfl

noncomputable
example (g : A → N) : Inhabited A → N := rec g

noncomputable
def default : Inhabited A → A := rec (fun (x : A) ↦ x)

example : default A ⟨a⟩ = a := rfl

end Inhabited

namespace Nonempty

universe u

variable (A : Type) (a : A) (P : Prop) (f : A → P)

#check Nonempty A

#check (⟨a⟩ : Nonempty A)

#check (rec f : Nonempty A → P)

-- The following is a consequence of proof irrelevance.
example : rec f ⟨a⟩ = f a := rfl

noncomputable
example (g : A → N) : Nonempty A → N := rec g
--gives an error

example (elim : Π (B : Type), (N → B) → (Nonempty N → B))
    (H : ∀ (B : Type) (n : N) (f : N → B), elim B f ⟨n⟩ = f n) : False := by
  let default := elim N id
  let (h0 : Nonempty N) := ⟨0⟩
  let (h1 : Nonempty N) := ⟨1⟩
  have hdefault : default h0 = default h1 := rfl
  have hdefault0 : default h0 = 0 := H N 0 id
  have hdefault1 : default h1 = 1 := H N 1 id
  apply N.zero_ne_one
  rewrite [← hdefault0, ← hdefault1] --here `rw` automatically tries `rfl` and finishes the proof
  exact hdefault

#check rec

#check Inhabited.rec

end Nonempty

end Example

section subsingleton_elimination

#check False.rec

#check And.rec

#check And.elim --non-dependent version

#check Eq.rec

#check Or.rec

#check Or.elim --non-dependent version

end subsingleton_elimination

section inductive_types

#check And

#check Or

#check Exists

#check Prod

#check N.zero

#check N.succ

#check And.intro

#check Prod.mk

#check Or.intro_left

#check Or.intro_right

#check Exists.intro

inductive Foo : Type where
| zero : Foo
| min : (Foo → Prop) → Foo --error

inductive Foo' : Type where
| zero : Foo'
| bar : (Prop → Foo') → Foo' --works

inductive Prod' (A B : Type 2) : Type
| intro : A → B → miao A B --error

inductive And' (P Q : Prop) : Type 4
| intro : P → Q → And' P Q --works

#check And.rec

#check Or.rec

#check Exists.rec

#check N.rec

#check Prod.rec

whatsnew in
inductive And'' (P Q : Prop) : Prop
| intro : P → Q → And'' P Q

whatsnew in
inductive N' : Type where
| zero : N'
| succ : N' → N'

example : N.zero ≠ N.zero.succ := by
  apply N.noConfusion

example (n m : N) (h : n.succ = m.succ) : n = m := by
  injection h

end inductive_types
