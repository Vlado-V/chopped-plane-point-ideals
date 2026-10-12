module

public import ChoppedPlane.ProfileFiniteKernel
public import ChoppedPlane.ProfileCrossing

@[expose] public section

/-! The actual cubic differentials satisfy the two kernel-vanishing bounds
at the critical twists. -/
noncomputable section
namespace ChoppedPlane.QWeyl
variable {K : Type*} [Field K] [CharZero K]

theorem profileCriticalDifferential_injective
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℕ) :
    Function.Injective (operatorDifferential (gradedProfileOperators q s (r : ℤ))
      (profileCriticalDegree s r)) := by
  apply profileDifferential_injective q hq s (r : ℤ) (profileCriticalDegree s r)
  intro k
  have hm : (profileMultiplicity s : ℤ) = 3 - (profileIndex s : ℤ) := by
    cases s <;> rfl
  simpa only [hm, Nat.cast_add, Nat.cast_one] using profile_right_degree_bound s r k

theorem profileCriticalDualDifferential_injective
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℕ)
    (hn : 0 < profileCriticalDegree s r) :
    Function.Injective (operatorDifferential
      (gradedProfileDualOperators q s ((profileCriticalDegree s r : ℤ) - (r : ℤ)))
      (profileCriticalDegree s r - 1)) := by
  apply profileDualDifferential_injective q hq s
    ((profileCriticalDegree s r : ℤ) - (r : ℤ)) (profileCriticalDegree s r - 1)
  intro k
  have hm : (profileMultiplicity s : ℤ) = 3 - (profileIndex s : ℤ) := by
    cases s <;> rfl
  have hn' : ((profileCriticalDegree s r - 1 + 1 : ℕ) : ℤ) =
      (profileCriticalDegree s r : ℤ) := by omega
  simpa only [hm, hn'] using profile_left_dual_degree_bound s r k

end ChoppedPlane.QWeyl
