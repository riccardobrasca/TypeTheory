import TypeTheory.L6.ex

open Classical Set

section diaconescu

example (P : Prop) : P ∨ ¬P := by
  let U : Set Prop := fun x ↦ x = True ∨ P
  let V : Set Prop := fun x ↦ x = False ∨ P

  have PUV : P → U = V := by
    intro hP
    apply funext
    intro x
    apply propext
    constructor
    · intro _
      right
      exact hP
    · intro _
      right
      exact hP

  have exU : Nonempty U := ⟨True, Or.inl rfl⟩
  have exV : Nonempty V := ⟨False, Or.inl rfl⟩
  let u : Prop := (choice exU).1
  let v : Prop := (choice exV).1
  have u_def : u ∈ U := (choice exU).2
  have v_def : v ∈ V := (choice exV).2

  have Puv : P → ∀ (hU : Nonempty U) (hV : Nonempty V),
      (choice hU).1 = (choice hV).1 := by
    intro hP
    rw [PUV hP]
    intro _ _
    rfl

  cases u_def with
  | inl hu => cases v_def with
    | inl hv =>
      right
      intro hP
      have : u ≠ v := by
        intro h
        rw [← hv, ← h, hu]
        trivial
      apply this
      exact Puv hP _ _
    | inr hv =>
      left
      exact hv
  | inr hu => cases v_def with
    | inl hv =>
      left
      exact hu
    | inr hv =>
      left
      exact hu

end diaconescu
