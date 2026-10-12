module

public import ChoppedPlane.FiniteAffineChart
public import ChoppedPlane.AffinePoints

@[expose] public section

/-!
# Actual projective chart points from finite reduced homogeneous quotients

The finite affine algebra constructed from a homogeneous saturated ideal splits
into copies of an algebraically closed field. Its polynomial presentation gives
actual distinct normalized plane points, and their homogeneous equations agree
with the original ideal in every degree.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K]

/-- Evaluation on the normalized chart commutes with actual dehomogenization. -/
theorem affineDehom_eval (f : Poly K 3) (a : Fin 2 → K) :
    eval ![a 0, a 1, 1] f = eval a (affineDehom f) := by
  have h : (aeval a).comp (affineDehom (K := K)) =
      aeval ![a 0, a 1, 1] := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [affineDehom, AlgHom.comp_apply]
  exact (AlgHom.congr_fun h f).symm

/-- The plane degree map of an affine presentation is evaluation at its actual
normalized coordinates. -/
theorem affinePresentation_plane_apply {p : ℕ}
    (φ : Poly K 2 →ₐ[K] (Fin p → K)) (f : Poly K 3) (i : Fin p) :
    φ (affineDehom f) i = eval (chartPoint K (affinePresentationCoordinates φ) i) f := by
  rw [affinePresentation_apply]
  exact (affineDehom_eval f (fun j => affinePresentationCoordinates φ (i, j))).symm

/-- A finite reduced chart of length `p` supplies actual distinct points whose
homogeneous equations are exactly those of the original ideal. Evaluation is
surjective in every degree past the cut at infinity. -/
theorem exists_projective_chart_points [IsAlgClosed K] {p : ℕ}
    (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ f, (X 2 : Poly K 3) * f ∈ I → f ∈ I)
    (N : ℕ) (hcut : ∀ f : Forms K 3 N, f.val ∈ I ⊔ Ideal.span {X (R := K) 2})
    [IsReduced (AffineCoordinateAlgebra I)]
    (hlen : finrank K (AffineCoordinateAlgebra I) = p) :
    ∃ a : PointCoordinates K p, DistinctPoints K a ∧
      (∀ t, pointDegreePiece K a t = idealFormPiece I t) ∧
      (∀ t, N ≤ t → Function.Surjective (pointEvaluation K a t)) := by
  let : Module.Finite K (AffineCoordinateAlgebra I) :=
    affineCoordinateAlgebra_finite I hI N hcut
  let e : AffineCoordinateAlgebra I ≃ₐ[K] (Fin p → K) :=
    finiteReducedAlgebraFinEquiv (K := K) p hlen
  let φ : Poly K 2 →ₐ[K] (Fin p → K) :=
    e.toAlgHom.comp (Ideal.Quotient.mkₐ K (I.map (affineDehom (K := K)).toRingHom))
  let a := affinePresentationCoordinates φ
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hmap (t : ℕ) : pointEvaluation K a t =
      e.toLinearMap.comp (formChartMap (affineQuotientMap I) t) := by
    ext f i
    exact (affinePresentation_plane_apply φ f.val i).symm
  refine ⟨a, affinePresentation_distinct φ hφ, ?_, ?_⟩
  · intro t
    ext f
    change pointEvaluation K a t f = 0 ↔ f.val ∈ I
    rw [hmap, LinearMap.comp_apply]
    change e (affineQuotientMap I f.val) = 0 ↔ f.val ∈ I
    rw [← map_zero e, e.injective.eq_iff]
    exact affineQuotientMap_form_eq_zero_iff I hI hsat t f
  · intro t hNt
    rw [hmap]
    exact e.surjective.comp
      (formChartMap_surjective_of_le (affineQuotientMap I) (affineQuotientMap_surjective I)
        (affineQuotientMap_z I) I hI
        (fun _ hf => affineQuotientMap_eq_zero_of_mem I hf) N t hNt hcut)

/-- Every Hilbert function of the resulting actual point ideal equals the
homogeneous Hilbert function of the original ideal. -/
theorem pointHilbertFunction_eq_of_idealFormPiece {p : ℕ}
    (I : Ideal (Poly K 3)) (a : PointCoordinates K p)
    (hpieces : ∀ t, pointDegreePiece K a t = idealFormPiece I t) (t : ℕ) :
    pointHilbertFunction K a t = finrank K (Forms K 3 t ⧸ idealFormPiece I t) := by
  exact (Submodule.quotEquivOfEq _ _ (hpieces t)).finrank_eq

end ChoppedPlane
