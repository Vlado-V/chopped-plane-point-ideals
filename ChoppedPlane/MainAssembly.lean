module

public import ChoppedPlane.EasyRange
public import ChoppedPlane.OneGeneratorCase
public import ChoppedPlane.TwoGeneratorCase
public import ChoppedPlane.NonpositiveCase
public import ChoppedPlane.PositiveCase

@[expose] public section

/-!
# Assembly of the complete chopped-ideal conclusion

Every point-count branch is proved. The one pending input is stated literally:
for each requested shape there is an actual matrix of linear forms over the
algebraic closure whose genuine multiplication maps have maximal rank in every
degree. No conclusion about chopped ideals is included in that input.
-/
noncomputable section
namespace ChoppedPlane

variable {K : Type*} [Field K]

/-- A uniform family of genuine all-degree maximal-rank linear matrices over
the algebraic closure of the coefficient field. -/
def UniformLinearMatrixWitness (K : Type*) [Field K] : Prop :=
  ∀ a c : ℕ, a < c → 2 ≤ c - a →
    ∃ M : LinearMatrix (AlgebraicClosure K) a c,
      ∀ t, LinearMatrixMaximalRank M t

/-- Every branch of the main conclusion follows from the literal uniform
linear-matrix witness input. -/
theorem genericChoppedConclusion_of_uniform_linear_witness [CharZero K]
    (hlinear : UniformLinearMatrixWitness K)
    (d p : ℕ) (hd : 2 ≤ d) (hp : 1 ≤ p) :
    GenericChoppedConclusion K d p := by
  by_cases hlo : p ≤ N (d - 1)
  · exact genericChoppedConclusion_outside_intermediate d p (by omega) (Or.inl hlo)
  by_cases hhi : N d ≤ p
  · exact genericChoppedConclusion_outside_intermediate d p (by omega) (Or.inr hhi)
  have hlo' : N (d - 1) < p := by omega
  have hhi' : p < N d := by omega
  by_cases hr1 : N d - p = 1
  · exact genericChoppedConclusion_one_generator (K := K) (by omega) hp hlo' hhi' hr1
  by_cases hr2 : N d - p = 2
  · exact genericChoppedConclusion_two_generator (K := K) hd hp hlo' hhi' hr2
  have hr : 3 ≤ N d - p := by omega
  by_cases ha : aCount d (N d - p) ≤ 0
  · exact genericChoppedConclusion_nonpositive d p hd hlo' hhi' hr ha
  · exact genericChoppedConclusion_positive_of_uniform_linear_witness
      hlinear d p hd hlo' hhi' hr (by omega)

/-- The complete field-uniform main statement has only the literal matrix
witness family as its current input. -/
theorem mainStatement_of_uniform_linear_witness
    (hlinear : ∀ (K : Type) [Field K] [CharZero K], UniformLinearMatrixWitness K) :
    MainStatement := by
  intro K _ _ d p hd hp
  exact genericChoppedConclusion_of_uniform_linear_witness (hlinear K) d p hd hp

/-- The degree-one boundary case needs no matrix witness input. -/
theorem genericChoppedConclusion_degree_one [CharZero K]
    (p : ℕ) (hp : 1 ≤ p) : GenericChoppedConclusion K 1 p := by
  by_cases hlo : p ≤ N (1 - 1)
  · exact genericChoppedConclusion_outside_intermediate 1 p (by decide) (Or.inl hlo)
  by_cases hhi : N 1 ≤ p
  · exact genericChoppedConclusion_outside_intermediate 1 p (by decide) (Or.inr hhi)
  have hlo' : N (1 - 1) < p := by omega
  have hhi' : p < N 1 := by omega
  have hr : N 1 - p = 1 := by
    norm_num [N] at hlo' hhi' ⊢
    omega
  exact genericChoppedConclusion_one_generator (K := K) (by decide) hp hlo' hhi' hr

/-- The assembled conclusion covers every positive chop degree when the
literal uniform matrix witnesses are supplied. -/
theorem genericChoppedConclusion_positive_degree_of_uniform_linear_witness
    [CharZero K] (hlinear : UniformLinearMatrixWitness K)
    (d p : ℕ) (hd : 1 ≤ d) (hp : 1 ≤ p) :
    GenericChoppedConclusion K d p := by
  by_cases hd1 : d = 1
  · subst d
    exact genericChoppedConclusion_degree_one p hp
  · exact genericChoppedConclusion_of_uniform_linear_witness hlinear d p (by omega) hp

end ChoppedPlane
