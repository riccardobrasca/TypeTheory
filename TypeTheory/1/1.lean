import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Real

open Real

#check 0

#check π

#check Complex.I 

#check (-1 : ℤ)

#check (2/3 : ℚ)

#check (fun x ↦ sin x)

#check Type

#check Type 1

#check (1 + 1 = 2)

#check (1 + 1 = 3)

example : 641 = 641 := rfl

example : (fun x ↦ sin x) = (fun y ↦ sin y) := rfl

example : (fun x ↦ sin x) π = sin π := rfl

example : sin = (fun x ↦ sin x) := rfl

example : 1 + 1 = 2 := rfl

example (n : ℕ) : n + 0 = n := rfl

example (x : ℝ × ℝ) : x = ⟨x.1, x.2⟩ := rfl