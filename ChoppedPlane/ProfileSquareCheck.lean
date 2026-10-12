module

public import ChoppedPlane.ProfileFiniteKernel
public import ChoppedPlane.ProfileMatrix

@[expose] public section

/-! The divisible-by-three excess-three witnesses are square at the lower
critical twist. The actual tensor kernel theorem therefore supplies both
critical rank checks without a Laurent cokernel argument. -/
noncomputable section
namespace ChoppedPlane.QWeyl
variable {K : Type*} [Field K] [CharZero K]

theorem profileSquareDifferential_injective
    (q : K) (hq : q ^ 2 + q + 1 = 0) (r : ℕ) :
    Function.Injective (operatorDifferential
      (gradedProfileOperators q .degreeThree (r : ℤ))
      (profileCriticalDegree .degreeThree r - 1)) := by
  apply profileDifferential_injective q hq .degreeThree (r : ℤ)
    (profileCriticalDegree .degreeThree r - 1)
  intro k
  have hn : 0 < profileCriticalDegree .degreeThree r := by
    norm_num [profileCriticalDegree, profileRows, profileIndex]
    omega
  have he : ((profileCriticalDegree .degreeThree r - 1 + 1 : ℕ) : ℤ) =
      (profileCriticalDegree .degreeThree r : ℤ) := by omega
  simpa [he, profileMultiplicity] using profile_square_degree_bound r k

theorem profileSquare_matrix_dimensions (K : Type*) [Field K] (r : ℕ) :
    Module.finrank K (MatrixSource K (profileRows .degreeThree r+3)
      (profileCriticalDegree .degreeThree r-1)) =
    Module.finrank K (MatrixTarget K (profileRows .degreeThree r)
      (profileCriticalDegree .degreeThree r-1)) := by
  apply Nat.le_antisymm
  · apply (matrixSource_le_target_iff K _ _ _).mpr
    norm_num [profileCriticalDegree, profileRows, profileIndex]
    have he : (2*(3*r+3)/3-1) = 2*r+1 := by omega
    rw [he]
    nlinarith
  · apply (matrixTarget_le_source_iff K _ _ _).mpr
    norm_num [profileCriticalDegree, profileRows, profileIndex]
    have he : (2*(3*r+3)/3-1) = 2*r+1 := by omega
    rw [he]
    nlinarith

theorem profileSquareDifferential_surjective
    (q : K) (hq : q ^ 2 + q + 1 = 0) (r : ℕ) :
    Function.Surjective (operatorDifferential
      (gradedProfileOperators q .degreeThree (r : ℤ))
      (profileCriticalDegree .degreeThree r - 1)) := by
  have hinj := profileSquareDifferential_injective q hq r
  have hsurj := (operatorDifferential_injective_iff_linearMatrixMap_surjective
    (profileSourceBasis .degreeThree r) (profileTargetBasis .degreeThree r)
    (gradedProfileOperators q .degreeThree (r : ℤ))
    (profileCriticalDegree .degreeThree r-1)).mp hinj
  have hmatrixinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (profileSquare_matrix_dimensions K r)).mpr hsurj
  exact (operatorDifferential_surjective_iff_linearMatrixMap_injective
    (profileSourceBasis .degreeThree r) (profileTargetBasis .degreeThree r)
    (gradedProfileOperators q .degreeThree (r : ℤ))
    (profileCriticalDegree .degreeThree r-1)).mpr hmatrixinj

end ChoppedPlane.QWeyl
