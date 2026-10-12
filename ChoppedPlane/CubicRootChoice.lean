module

public import ChoppedPlane.QWeylPullback
public import Mathlib.FieldTheory.IsAlgClosed.Basic

@[expose] public section

/-! The cubic witness parameters exist over every algebraically closed
characteristic-zero field. -/
namespace ChoppedPlane.QWeyl
variable {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]

/-- A nontrivial cube root of unity with its exact quadratic relation. -/
theorem exists_cubic_parameter : ∃ q : K, q ^ 2 + q + 1 = 0 ∧ q ≠ 0 ∧ q ≠ 1 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (-3 : K) (by decide : 0 < 2)
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hq : ((w-1)/2)^2 + (w-1)/2 + 1 = 0 := by
    field_simp
    linear_combination hw
  refine ⟨(w-1)/2, hq, ?_, ?_⟩
  · intro h
    rw [h] at hq
    norm_num at hq
  · intro h
    rw [h] at hq
    norm_num at hq

end ChoppedPlane.QWeyl
