import TypeTheory.L4.ex
open scoped PiNotation

section equality

namespace N

inductive Eq : N → N → Prop where
  | refl (a : N) : Eq a a

infix:50 " ≃ "  => Eq

example : ∀ (x : N), x ≃ x + 0  := by
  refine N.rec (Eq.refl _) (fun d h => ?_)
  refine Eq.rec (motive := fun n _ ↦ succ d ≃ n) ?_
    (Eq.refl _ : succ d + 0 ≃ succ (d + 0))
  exact Eq.rec (motive := fun n _ ↦ succ d ≃ succ n) (Eq.refl _) h

end N

end equality
