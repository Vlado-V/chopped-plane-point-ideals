module

public import ChoppedPlane.ProfileOperators
public import ChoppedPlane.PolynomialOperatorDuality

@[expose] public section

/-! Actual excess-three matrices in finite bases of the graded cubic modules. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open Module
variable {K : Type*} [Field K]

/-- The entries are the literal transposed coefficients of multiplication by
`u`, `v`, and the cyclic `z` action on consecutive graded components. -/
def profileLinearMatrix (q : K) (s : CubicProfile) (r : ℕ) :
    LinearMatrix K (profileRows s r) (profileRows s r+3) :=
  operatorLinearMatrix (profileSourceBasis s r) (profileTargetBasis s r)
    (gradedProfileOperators q s (r : ℤ))

/-- The stated critical auxiliary degree is exactly the numerical matrix crossing. -/
theorem profileLinearMatrix_criticalTwist (s : CubicProfile) (r : ℕ) :
    linearMatrixCriticalTwist (profileRows s r) (profileRows s r+3) =
      profileCriticalDegree s r := by
  simp [linearMatrixCriticalTwist, profileCriticalDegree]

/-- Two genuine differential checks give maximal rank of the actual profile
matrix in every twist. -/
theorem profileLinearMatrix_maximalRank_of_differential_checks [CharZero K]
    (q : K) (s : CubicProfile) (r : ℕ)
    (hright : Function.Injective (operatorDifferential
      (gradedProfileOperators q s (r : ℤ)) (profileCriticalDegree s r)))
    (hleft : 0 < profileCriticalDegree s r → Function.Surjective (operatorDifferential
      (gradedProfileOperators q s (r : ℤ)) (profileCriticalDegree s r-1))) :
    ∀ t, LinearMatrixMaximalRank (profileLinearMatrix q s r) t := by
  apply linearMatrixMaximalRank_all_of_numeric_critical_checks _ (by omega)
  · rw [profileLinearMatrix_criticalTwist]
    intro hpos
    apply linearMatrixMaximalRank_of_injective
    exact (operatorDifferential_surjective_iff_linearMatrixMap_injective
      (profileSourceBasis s r) (profileTargetBasis s r)
      (gradedProfileOperators q s (r : ℤ)) (profileCriticalDegree s r-1)).mp (hleft hpos)
  · rw [profileLinearMatrix_criticalTwist]
    apply linearMatrixMaximalRank_of_surjective
    exact (operatorDifferential_injective_iff_linearMatrixMap_surjective
      (profileSourceBasis s r) (profileTargetBasis s r)
      (gradedProfileOperators q s (r : ℤ)) (profileCriticalDegree s r)).mp hright

/-- Concrete profile matrices cover every excess-three shape. -/
theorem exists_three_extra_columns_maximalRank_of_profile_matrices
    (q : K) (hprofiles : ∀ s : CubicProfile, ∀ r : ℕ,
      ∀ t, LinearMatrixMaximalRank (profileLinearMatrix q s r) t) (a : ℕ) :
    ∃ L : LinearMatrix K a (a+3), ∀ t, LinearMatrixMaximalRank L t := by
  by_cases ha : 0 < a
  · obtain ⟨s, r, h⟩ := exists_profileRows a ha
    have hex : ∃ L : LinearMatrix K (profileRows s r) (profileRows s r+3),
        ∀ t, LinearMatrixMaximalRank L t := ⟨profileLinearMatrix q s r, hprofiles s r⟩
    rwa [h] at hex
  · have h : a = 0 := by omega
    subst a
    refine ⟨0, ?_⟩
    intro t
    apply linearMatrixMaximalRank_of_surjective
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end ChoppedPlane.QWeyl
