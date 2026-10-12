module

public import Mathlib

@[expose] public section

/-!
# Reduced finite algebras over an algebraically closed field

The Artinian decomposition identifies a reduced finite algebra with a product
of residue fields. Algebraic closedness identifies each residue field with the
base field, yielding actual coordinates for a finite reduced point set.
-/

noncomputable section
namespace ChoppedPlane

variable {K A : Type*} [Field K] [IsAlgClosed K] [CommRing A] [Algebra K A]
  [Module.Finite K A] [IsReduced A]

/-- Every residue field of a finite algebra over an algebraically closed field
is the base field. -/
noncomputable def residueFieldEquiv (m : MaximalSpectrum A) :
    (A ⧸ m.asIdeal) ≃ₐ[K] K := by
  letI := Ideal.Quotient.field m.asIdeal
  exact (AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m.asIdeal))
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K))).symm

/-- A reduced finite algebra splits as a finite product of the base field. -/
noncomputable def finiteReducedAlgebraEquiv : A ≃ₐ[K] (MaximalSpectrum A → K) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  exact ((IsArtinianRing.equivPi A).restrictScalars K).trans
    (AlgEquiv.piCongrRight residueFieldEquiv)

/-- The number of factors is the vector-space dimension of the algebra. -/
theorem card_maximalSpectrum_eq_finrank :
    Nat.card (MaximalSpectrum A) = Module.finrank K A := by
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let := Fintype.ofFinite (MaximalSpectrum A)
  simpa using (finiteReducedAlgebraEquiv (K := K) (A := A)).toLinearEquiv.finrank_eq.symm

/-- The factors can be indexed by `Fin p` when the algebra has dimension `p`. -/
noncomputable def finiteReducedAlgebraFinEquiv (p : ℕ) (h : Module.finrank K A = p) :
    A ≃ₐ[K] (Fin p → K) := by
  letI : IsArtinianRing A := IsArtinianRing.of_finite K A
  letI := Fintype.ofFinite (MaximalSpectrum A)
  have hc : Fintype.card (MaximalSpectrum A) = p := by
    rw [← Nat.card_eq_fintype_card, card_maximalSpectrum_eq_finrank (K := K), h]
  exact (finiteReducedAlgebraEquiv (K := K) (A := A)).trans
    (AlgEquiv.piCongrLeft K (fun _ : MaximalSpectrum A => K)
      (Fintype.equivFinOfCardEq hc).symm).symm

end ChoppedPlane
