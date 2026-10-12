module

public import ChoppedPlane.Points
public import ChoppedPlane.SplitFiniteAlgebra

@[expose] public section

/-!
# Coordinates of split finite affine quotients

A surjection from the two-variable polynomial algebra onto `K^p` is evaluation
at `p` distinct affine points. This identifies the quotient kernel with their
actual evaluation equations, rather than an abstract finite-dimensional model.
-/

noncomputable section
namespace ChoppedPlane
open MvPolynomial

variable {K : Type*} [Field K] {p : ℕ}

/-- The coordinates recovered from a split affine algebra presentation. -/
def affinePresentationCoordinates
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K)) : PointCoordinates K p :=
  fun ij => φ (X ij.2) ij.1

/-- Every coordinate of an affine presentation is point evaluation. -/
theorem affinePresentation_apply
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K))
    (f : MvPolynomial (Fin 2) K) (i : Fin p) :
    φ f i = eval (fun j => affinePresentationCoordinates φ (i, j)) f := by
  have h : (Pi.evalAlgHom K (fun _ : Fin p => K) i).comp φ =
      aeval (fun j => affinePresentationCoordinates φ (i, j)) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [affinePresentationCoordinates]
  exact congrArg (fun g : MvPolynomial (Fin 2) K →ₐ[K] K => g f) h

/-- Surjectivity rules out repeated affine coordinates. -/
theorem affinePresentation_distinct
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K))
    (hφ : Function.Surjective φ) : DistinctPoints K (affinePresentationCoordinates φ) := by
  classical
  intro i j hij
  have hc : (fun k => affinePresentationCoordinates φ (i, k)) =
      (fun k => affinePresentationCoordinates φ (j, k)) := by
    funext k
    fin_cases k
    · exact congrArg Prod.fst hij
    · exact congrArg Prod.snd hij
  by_contra hne
  obtain ⟨f, hf⟩ := hφ (Pi.single i 1)
  have he : φ f i = φ f j := by
    rw [affinePresentation_apply, affinePresentation_apply, hc]
  rw [hf] at he
  simp [Ne.symm hne] at he

/-- The presentation kernel is exactly simultaneous vanishing at its points. -/
theorem affinePresentation_ker
    (φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K))
    (f : MvPolynomial (Fin 2) K) :
    φ f = 0 ↔ ∀ i, eval (fun j => affinePresentationCoordinates φ (i, j)) f = 0 := by
  simp only [funext_iff, Pi.zero_apply, affinePresentation_apply]

/-- A reduced finite quotient over an algebraically closed field supplies
an actual distinct-point presentation with the original ideal as its kernel. -/
theorem exists_affine_point_presentation [IsAlgClosed K]
    (I : Ideal (MvPolynomial (Fin 2) K))
    [Module.Finite K (MvPolynomial (Fin 2) K ⧸ I)]
    [IsReduced (MvPolynomial (Fin 2) K ⧸ I)]
    (h : Module.finrank K (MvPolynomial (Fin 2) K ⧸ I) = p) :
    ∃ φ : MvPolynomial (Fin 2) K →ₐ[K] (Fin p → K),
      Function.Surjective φ ∧ DistinctPoints K (affinePresentationCoordinates φ) ∧
      ∀ f, φ f = 0 ↔ f ∈ I := by
  let e := finiteReducedAlgebraFinEquiv (K := K) p h
  let φ := e.toAlgHom.comp (Ideal.Quotient.mkₐ K I)
  have hφ : Function.Surjective φ := e.surjective.comp Ideal.Quotient.mk_surjective
  refine ⟨φ, hφ, affinePresentation_distinct φ hφ, ?_⟩
  intro f
  change e (Ideal.Quotient.mk I f) = 0 ↔ f ∈ I
  rw [← map_zero e, e.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

end ChoppedPlane
