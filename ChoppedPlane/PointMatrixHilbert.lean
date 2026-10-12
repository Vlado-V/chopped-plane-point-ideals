module

public import ChoppedPlane.GenericPointMatrix
public import ChoppedPlane.RowProfiles
public import ChoppedPlane.GeneralPoints

@[expose] public section

/-! The point-ideal and actual cofactor quotient Hilbert functions agree;
the row-profile formula supplies interpolation in the generating degree. -/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial
variable {K : Type*} [Field K] {c p : ℕ}

/-- In natural degrees the two actual quotient-image definitions agree. -/
theorem minorHilbertFunction_nat
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (t : ℕ) :
    minorHilbertFunction B (t : ℤ) =
      idealQuotientHilbertFunction (maximalMinorIdeal B) t := by
  unfold minorHilbertFunction minorFormToRingQuotient
  rw [signedForms_nat]
  rfl

/-- Agreement of all homogeneous ideal pieces identifies the actual point
Hilbert function with the actual cofactor quotient Hilbert function. -/
theorem pointHilbertFunction_eq_minor_of_pieces
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (a : PointCoordinates K p)
    (hpieces : ∀ t, pointDegreePiece K a t = idealFormPiece (maximalMinorIdeal B) t)
    (t : ℕ) : pointHilbertFunction K a t = minorHilbertFunction B (t : ℤ) := by
  rw [pointHilbertFunction_eq_of_idealFormPiece _ a hpieces,
    finrank_idealFormQuotient, minorHilbertFunction_nat]

/-- The one/two row profile has exactly the paper's required number of points. -/
theorem positiveRowProfile_selected_card (r a : ℕ) (hr : 0 < r) :
    Fintype.card (Ferrers.SelectedIndex (positiveRowProfile r a)) =
      N (positiveRowGeneratorDegree r a) - r := by
  apply Ferrers.selected_card_of_sums
  · rw [positiveRowProfile_sum r a hr]
    unfold positiveRowGeneratorDegree
    omega
  · have hsq : (∑ i, positiveRowProfile r a i ^ 2) = 4 * r + a := by
      calc
        _ = ∑ i : Fin (r + a), Ferrers.positiveProfile r a i ^ 2 :=
          Fintype.sum_equiv (finCongr (positiveRowColumns_rows r a hr)) _ _ (fun _ => rfl)
        _ = _ := Ferrers.positiveProfile_square_sum r a
    rw [hsq]
    unfold positiveRowGeneratorDegree
    omega

/-- Actual points extracted from a primitive matrix of this profile interpolate
in degree `d` and have constant point Hilbert function above it. -/
theorem positiveRow_points_properties
    {r a : ℕ} (hr : 0 < r)
    (B : HomogeneousRowMatrix K (positiveRowProfile r a))
    (hprimitive : PrimitiveMaximalMinors (rowMatrixVal (positiveRowProfile r a) B))
    (z : PointCoordinates K (N (positiveRowGeneratorDegree r a) - r))
    (hpieces : ∀ t, pointDegreePiece K z t =
      idealFormPiece (maximalMinorIdeal (rowMatrixVal (positiveRowProfile r a) B)) t) :
    Function.Surjective (pointEvaluation K z (positiveRowGeneratorDegree r a)) ∧
      ∀ e, pointHilbertFunction K z (positiveRowGeneratorDegree r a + e) =
        N (positiveRowGeneratorDegree r a) - r := by
  have hf (e : ℕ) : pointHilbertFunction K z (positiveRowGeneratorDegree r a + e) =
      N (positiveRowGeneratorDegree r a) - r := by
    have h := positiveRow_minorHilbertFunction_formula hr B hprimitive
      ((positiveRowGeneratorDegree r a + e : ℕ) : ℤ)
    rw [← pointHilbertFunction_eq_minor_of_pieces _ z hpieces] at h
    have ht : ¬ ((positiveRowGeneratorDegree r a + e : ℕ) : ℤ) <
        (positiveRowGeneratorDegree r a : ℤ) := by omega
    rw [ite_eq_right ht] at h
    have hle : r ≤ N (positiveRowGeneratorDegree r a) := by
      have hd : r ≤ positiveRowGeneratorDegree r a + 1 := by
        unfold positiveRowGeneratorDegree
        omega
      have hN : positiveRowGeneratorDegree r a + 1 ≤ N (positiveRowGeneratorDegree r a) := by
        have hN := twice_N (positiveRowGeneratorDegree r a)
        nlinarith
      exact hd.trans hN
    rw [← Nat.cast_sub hle] at h
    exact_mod_cast h
  refine ⟨pointEvaluation_surjective_of_hilbert_eq z ?_, hf⟩
  simpa only [Nat.add_zero] using hf 0

end ChoppedPlane
