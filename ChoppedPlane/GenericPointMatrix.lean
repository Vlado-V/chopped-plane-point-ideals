module

public import ChoppedPlane.RowPrimitiveChart
public import ChoppedPlane.GenericReducedMatrix
public import ChoppedPlane.FerrersAffineQuotient
public import ChoppedPlane.ProjectiveChartPoints

@[expose] public section

/-! The explicit split grid supplies an unconditional reduced-point open in
the space of independent homogeneous row matrices. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {c : ℕ}

/-- The finite affine algebra of the actual split row matrix is the function
algebra of its selected grid points. -/
def ferrersRowMatrix_splitWitness (δ : Fin (c + 1) → ℕ)
    (α β : Ferrers.RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    AffineCoordinateAlgebra (maximalMinorIdeal
      (rowMatrixVal δ (universalRowMatrix δ
        (rowMatrixCoordinates δ (ferrersHomogeneousRowMatrix δ α β))))) ≃ₐ[K]
      (Ferrers.SelectedIndex δ → K) := by
  have hI : maximalMinorIdeal (Ferrers.seedMatrix δ α β) = Ferrers.cofactorIdeal δ α β :=
    Ferrers.seedMatrix_cofactorIdeal δ α β
  rw [universalRowMatrix_coordinates, rowMatrixVal_ferrers]
  change (Poly K 2 ⧸ (maximalMinorIdeal (Ferrers.seedMatrix δ α β)).map
    (affineDehom (K := K)).toRingHom) ≃ₐ[K] (Ferrers.SelectedIndex δ → K)
  rw [hI]
  exact Ferrers.affineCofactorQuotientAlgEquiv δ α β hα hβ

/-- Positive total row degree suffices for an unconditional nonempty open of
primitive matrices with finite reduced affine quotients of the correct length. -/
theorem universalRowMatrix_points_principal_open [Infinite K]
    (δ : Fin (c + 1) → ℕ) (hdegree : 0 < ∑ i, δ i) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      (∃ u, eval u D ≠ 0) ∧ ∀ u, eval u D ≠ 0 →
        PrimitiveMaximalMinors (rowMatrixVal δ (universalRowMatrix δ u)) ∧
        PrimitiveMaximalMinors (universalInfinityMatrix δ u) ∧
        (∀ f : Forms K 2 (2 * ∑ i, δ i),
          f.val ∈ maximalMinorIdeal (universalInfinityMatrix δ u)) ∧
        IsReduced (AffineCoordinateAlgebra (maximalMinorIdeal
          (rowMatrixVal δ (universalRowMatrix δ u)))) ∧
        Module.Finite K (AffineCoordinateAlgebra (maximalMinorIdeal
          (rowMatrixVal δ (universalRowMatrix δ u)))) ∧
        finrank K (AffineCoordinateAlgebra (maximalMinorIdeal
          (rowMatrixVal δ (universalRowMatrix δ u)))) =
            Fintype.card (Ferrers.SelectedIndex δ) := by
  classical
  let α := Ferrers.canonicalRoots (K := K) δ
  have hα : Function.Injective α := Ferrers.canonicalRoots_injective δ
  let a₀ := rowMatrixCoordinates δ (ferrersHomogeneousRowMatrix δ α α)
  obtain ⟨H₀, hH₀, hbase⟩ := universalRowMatrix_primitive_cut_principal_open δ hdegree α α
  obtain ⟨D, hD, hgood⟩ := universalRowMatrix_reduced_principal_open δ
    (2 * ∑ i, δ i) H₀ a₀ hH₀
    (fun u hu => (hbase u hu).1)
    (fun u hu => (hbase u hu).2.1)
    (fun u hu => (hbase u hu).2.2)
    (ferrersRowMatrix_splitWitness δ α α hα hα)
  refine ⟨D, ⟨a₀, hD⟩, fun u hu => ?_⟩
  obtain ⟨hHu, hred, hfinite, hlen⟩ := hgood u hu
  obtain ⟨hprim, hbinary, hcut⟩ := hbase u hHu
  exact ⟨hprim, hbinary, hcut, hred, hfinite, hlen⟩

/-- Over an algebraically closed field the open gives literal distinct points,
and the actual point ideal agrees with the cofactor ideal in every degree. -/
theorem universalRowMatrix_actual_points_principal_open [Infinite K] [IsAlgClosed K]
    (δ : Fin (c + 1) → ℕ) (hdegree : 0 < ∑ i, δ i) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      (∃ u, eval u D ≠ 0) ∧ ∀ u, eval u D ≠ 0 →
        PrimitiveMaximalMinors (rowMatrixVal δ (universalRowMatrix δ u)) ∧
        ∃ a : PointCoordinates K (Fintype.card (Ferrers.SelectedIndex δ)),
          DistinctPoints K a ∧
          ∀ t, pointDegreePiece K a t = idealFormPiece
            (maximalMinorIdeal (rowMatrixVal δ (universalRowMatrix δ u))) t := by
  obtain ⟨D, hD, hgood⟩ := universalRowMatrix_points_principal_open (K := K) δ hdegree
  refine ⟨D, hD, fun u hu => ?_⟩
  obtain ⟨hprim, hbinary, hcut, hred, hfinite, hlen⟩ := hgood u hu
  let I := maximalMinorIdeal (rowMatrixVal δ (universalRowMatrix δ u))
  let : IsReduced (AffineCoordinateAlgebra I) := hred
  have hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K) :=
    maximalMinorIdeal_homogeneous δ _ (rowMatrixVal_homogeneous δ _)
  have hsat : ∀ f : Poly K 3, X 2 * f ∈ I → f ∈ I :=
    rowMatrix_z_saturated δ _ hbinary
  have hCut : ∀ f : Forms K 3 (2 * ∑ i, δ i), f.val ∈ I ⊔ Ideal.span {X (R := K) 2} :=
    rowMatrix_form_cut_of_binary δ _ _ hcut
  obtain ⟨a, hdist, hpieces, _⟩ := exists_projective_chart_points I hI hsat
    (2 * ∑ i, δ i) hCut hlen
  exact ⟨hprim, a, hdist, hpieces⟩

end ChoppedPlane
