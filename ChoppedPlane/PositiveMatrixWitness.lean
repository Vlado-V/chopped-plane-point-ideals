module

public import ChoppedPlane.GenericPointMatrix
public import ChoppedPlane.PointMatrixHilbert
public import ChoppedPlane.RowProfiles

@[expose] public section

/-!
# Actual positive-profile point and matrix witnesses

The reduced-point open and the all-twist linear-block rank open are genuine
principal opens in the same independent row-coefficient parameter space.
Their intersection supplies literal distinct points, with their actual ideal
pieces equal to the matrix minor ideal in every homogeneous degree.
-/

noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K]

/-- A genuine all-twist matrix witness yields a nonempty open of actual points
and homogeneous row matrices satisfying both geometric and rank conditions. -/
theorem positiveRow_point_matrix_principal_open [Infinite K] [IsAlgClosed K]
    {r a : ℕ} (hr : 2 ≤ r)
    (hw : ∃ M : LinearMatrix K a (positiveRowColumns r a),
      ∀ t, LinearMatrixMaximalRank M t) :
    ∃ D : MvPolynomial (RowMatrixParameter (positiveRowProfile r a)) K,
      (∃ u, eval u D ≠ 0) ∧ ∀ u, eval u D ≠ 0 →
        PrimitiveMaximalMinors
          (rowMatrixVal (positiveRowProfile r a) (universalRowMatrix _ u)) ∧
        ∃ z : PointCoordinates K (N (positiveRowGeneratorDegree r a) - r),
          DistinctPoints K z ∧
          (∀ t, pointDegreePiece K z t = idealFormPiece
            (maximalMinorIdeal
              (rowMatrixVal (positiveRowProfile r a) (universalRowMatrix _ u))) t) ∧
          (∀ t, LinearMatrixMaximalRank
            (universalPositiveLinearBlock (by omega : 0 < r) u) t) ∧
          Function.Surjective (pointEvaluation K z (positiveRowGeneratorDegree r a)) ∧
          ∀ e, pointHilbertFunction K z (positiveRowGeneratorDegree r a + e) =
            N (positiveRowGeneratorDegree r a) - r := by
  classical
  have hrpos : 0 < r := by omega
  have hdegree : 0 < ∑ i, positiveRowProfile r a i := by
    rw [positiveRowProfile_sum r a hrpos]
    omega
  obtain ⟨P, ⟨uP, huP⟩, hpoints⟩ :=
    universalRowMatrix_actual_points_principal_open (K := K)
      (positiveRowProfile r a) hdegree
  obtain ⟨Q, ⟨uQ, huQ⟩, hrank⟩ := positiveRow_linearBlock_allTwists_open hr hw
  have hP : P ≠ 0 := by
    intro h
    rw [h, map_zero] at huP
    exact huP rfl
  have hQ : Q ≠ 0 := by
    intro h
    rw [h, map_zero] at huQ
    exact huQ rfl
  obtain ⟨u₀, hu₀⟩ := nonempty_principal_intersection ![P, Q]
    (fun i => by fin_cases i <;> assumption)
  refine ⟨P * Q, ⟨u₀, ?_⟩, fun u hu => ?_⟩
  · simpa only [map_mul, Matrix.cons_val_zero, Matrix.cons_val_one] using
      mul_ne_zero (hu₀ 0) (hu₀ 1)
  · have hparts : eval u P ≠ 0 ∧ eval u Q ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [map_mul] using hu)
    obtain ⟨hprimitive, hcoords⟩ := hpoints u hparts.1
    rw [positiveRowProfile_selected_card r a hrpos] at hcoords
    obtain ⟨z, hdist, hpieces⟩ := hcoords
    obtain ⟨hsurj, hconstant⟩ := positiveRow_points_properties hrpos
      (universalRowMatrix (positiveRowProfile r a) u) hprimitive z hpieces
    exact ⟨hprimitive, z, hdist, hpieces, hrank u hparts.2, hsurj, hconstant⟩

/-- The principal-open intersection gives one actual point configuration and
one universal row matrix, with the required length and all-twist ranks. -/
theorem positiveRow_exists_point_matrix_witness [Infinite K] [IsAlgClosed K]
    {r a : ℕ} (hr : 2 ≤ r)
    (hw : ∃ M : LinearMatrix K a (positiveRowColumns r a),
      ∀ t, LinearMatrixMaximalRank M t) :
    ∃ (B : HomogeneousRowMatrix K (positiveRowProfile r a))
      (z : PointCoordinates K (N (positiveRowGeneratorDegree r a) - r)),
      PrimitiveMaximalMinors
        (rowMatrixVal (positiveRowProfile r a) B) ∧
      DistinctPoints K z ∧
      (∀ t, pointDegreePiece K z t = idealFormPiece
        (maximalMinorIdeal
          (rowMatrixVal (positiveRowProfile r a) B)) t) ∧
      (∀ t, LinearMatrixMaximalRank
        (positiveLinearBlock (by omega : 0 < r) B) t) ∧
      Function.Surjective (pointEvaluation K z (positiveRowGeneratorDegree r a)) ∧
      ∀ e, pointHilbertFunction K z (positiveRowGeneratorDegree r a + e) =
        N (positiveRowGeneratorDegree r a) - r := by
  obtain ⟨D, ⟨u, hu⟩, hgood⟩ := positiveRow_point_matrix_principal_open hr hw
  obtain ⟨hprimitive, z, hdist, hpieces, hrank, hsurj, hconstant⟩ := hgood u hu
  exact ⟨universalRowMatrix (positiveRowProfile r a) u, z, hprimitive,
    hdist, hpieces, hrank, hsurj, hconstant⟩

end ChoppedPlane
