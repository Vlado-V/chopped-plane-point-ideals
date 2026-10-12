module

public import ChoppedPlane.CubicMatrixWitness
public import ChoppedPlane.ExpectedSyzygy

@[expose] public section

/-! Theorem 1.1 and Corollary 5.1, without mathematical witness premises. -/
namespace ChoppedPlane

theorem main_theorem : MainStatement :=
  mainStatement_of_uniform_linear_witness fun K _ _ => uniformLinearMatrixWitness (K := K)

theorem expected_syzygy_theorem : ExpectedSyzygyStatement :=
  expectedSyzygyStatement_of_mainStatement main_theorem

theorem genericChoppedConclusion_positive_degree {K : Type*} [Field K] [CharZero K]
    (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p) : GenericChoppedConclusion K d p :=
  genericChoppedConclusion_positive_degree_of_uniform_linear_witness
    uniformLinearMatrixWitness d p hd hp

end ChoppedPlane
