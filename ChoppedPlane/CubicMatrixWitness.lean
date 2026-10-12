module

public import ChoppedPlane.ProfileMatrix
public import ChoppedPlane.ProfileCriticalChecks
public import ChoppedPlane.ProfileLaurentDuality
public import ChoppedPlane.CubicRootChoice
public import ChoppedPlane.UniformMatrixAssembly
public import ChoppedPlane.MainAssembly

@[expose] public section

/-! Uniform actual linear matrices, with both critical rank checks proved. -/
noncomputable section
namespace ChoppedPlane.QWeyl
variable {K : Type*} [Field K] [CharZero K]

theorem profileLinearMatrix_maximalRank
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℕ) :
    ∀ t, LinearMatrixMaximalRank (profileLinearMatrix q s r) t := by
  apply profileLinearMatrix_maximalRank_of_differential_checks
  · exact profileCriticalDifferential_injective q hq s r
  · intro hn
    exact (profileDifferential_surjective_iff_topMultiply_injective q hq s
      (r : ℤ) (profileCriticalDegree s r - 1)).mpr
      (profileLaurentTopMultiply_critical_injective q hq s r hn)

theorem exists_three_extra_columns_maximalRank [IsAlgClosed K] (a : ℕ) :
    ∃ L : LinearMatrix K a (a+3), ∀ t, LinearMatrixMaximalRank L t := by
  obtain ⟨q,hq,_,_⟩ := exists_cubic_parameter (K := K)
  exact exists_three_extra_columns_maximalRank_of_profile_matrices q
    (profileLinearMatrix_maximalRank q hq) a

theorem exists_linearMatrix_maximalRank [IsAlgClosed K]
    (a c : ℕ) (hac : a < c) (hgap : 2 ≤ c-a) :
    ∃ L : LinearMatrix K a c, ∀ t, LinearMatrixMaximalRank L t :=
  exists_linearMatrix_maximalRank_of_three
    (exists_three_extra_columns_maximalRank (K := K)) a c hac hgap

end ChoppedPlane.QWeyl

namespace ChoppedPlane
variable {K : Type*} [Field K] [CharZero K]

theorem uniformLinearMatrixWitness : UniformLinearMatrixWitness K := by
  intro a c hac hgap
  exact QWeyl.exists_linearMatrix_maximalRank a c hac hgap

end ChoppedPlane
