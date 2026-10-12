module

public import Mathlib

@[expose] public section

/-!
# Nondegenerate trace forms certify reduced finite algebras

A nilpotent element pairs to zero with every element under the algebra trace
form. Thus a nondegenerate trace form rules out nonzero nilpotents. For a finite
product of copies of the base field, the standard trace matrix is the identity.
-/

noncomputable section
namespace ChoppedPlane
open Module

variable {K A J : Type*} [Field K] [CommRing A] [Algebra K A]

/-- A nilpotent element lies in the left radical of the algebra trace form. -/
theorem traceForm_eq_zero_of_nilpotent {x : A} (hx : IsNilpotent x) (y : A) :
    Algebra.traceForm K A x y = 0 := by
  rw [Algebra.traceForm_apply]
  exact (Algebra.isNilpotent_trace_of_isNilpotent
    ((Commute.all x y).isNilpotent_mul_right hx)).eq_zero

/-- Nondegeneracy of the trace form implies that the algebra is reduced. -/
theorem isReduced_of_traceForm_nondegenerate
    (h : (Algebra.traceForm K A).Nondegenerate) : IsReduced A := by
  refine ⟨fun x hx => ?_⟩
  exact h.1 x (fun y => traceForm_eq_zero_of_nilpotent hx y)

/-- A nonzero determinant of the trace matrix certifies reducedness. -/
theorem isReduced_of_traceForm_det_ne_zero [Fintype J] [DecidableEq J]
    (b : Basis J K A)
    (h : ((Algebra.traceForm K A).toMatrix b).det ≠ 0) : IsReduced A :=
  isReduced_of_traceForm_nondegenerate
    (LinearMap.BilinForm.nondegenerate_of_det_ne_zero (Algebra.traceForm K A) b h)

/-- Trace in a finite product of the base field is the sum of its coordinates. -/
theorem algebra_trace_pi [Fintype J] (x : J → K) :
    Algebra.trace K (J → K) x = ∑ j, x j := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K J), Matrix.trace]
  apply Finset.sum_congr rfl
  intro j _
  change Algebra.leftMulMatrix (Pi.basisFun K J) x j j = x j
  rw [Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr]
  simp [Pi.basisFun_apply]

/-- The trace form of a finite product is the usual coordinate pairing. -/
theorem algebra_traceForm_pi [Fintype J] (x y : J → K) :
    Algebra.traceForm K (J → K) x y = ∑ j, x j * y j := by
  rw [Algebra.traceForm_apply, algebra_trace_pi]
  rfl

/-- The standard basis has identity trace matrix over every base field. -/
theorem algebra_traceForm_pi_matrix [Fintype J] [DecidableEq J] :
    (Algebra.traceForm K (J → K)).toMatrix (Pi.basisFun K J) = 1 := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, algebra_traceForm_pi]
  simp [Pi.basisFun_apply, Pi.single_apply, mul_ite, Matrix.one_apply, eq_comm]

/-- A finite product of the base field has nondegenerate algebra trace form. -/
theorem algebra_traceForm_pi_nondegenerate [Fintype J] :
    (Algebra.traceForm K (J → K)).Nondegenerate := by
  classical
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero
    (Algebra.traceForm K (J → K)) (Pi.basisFun K J)
  rw [algebra_traceForm_pi_matrix, Matrix.det_one]
  exact one_ne_zero

/-- Algebra equivalences preserve the trace pairing. -/
theorem algebra_traceForm_equiv {A' : Type*} [CommRing A'] [Algebra K A']
    (e : A ≃ₐ[K] A') (x y : A) :
    Algebra.traceForm K A' (e x) (e y) = Algebra.traceForm K A x y := by
  rw [Algebra.traceForm_apply, ← map_mul, Algebra.trace_eq_of_algEquiv,
    Algebra.traceForm_apply]

/-- Nondegeneracy of the trace form is preserved by an algebra equivalence. -/
theorem traceForm_nondegenerate_of_algEquiv {A' : Type*} [CommRing A'] [Algebra K A']
    (e : A ≃ₐ[K] A') (h : (Algebra.traceForm K A').Nondegenerate) :
    (Algebra.traceForm K A).Nondegenerate := by
  constructor
  · intro x hx
    apply e.injective
    rw [map_zero]
    apply h.1 (e x)
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [algebra_traceForm_equiv]
    exact hx z
  · intro y hy
    apply e.injective
    rw [map_zero]
    apply h.2 (e y)
    intro x
    obtain ⟨z, rfl⟩ := e.surjective x
    rw [algebra_traceForm_equiv]
    exact hy z

/-- An algebra split as a finite product of the base field has nondegenerate
trace form in every characteristic. -/
theorem traceForm_nondegenerate_of_split [Fintype J] (e : A ≃ₐ[K] (J → K)) :
    (Algebra.traceForm K A).Nondegenerate :=
  traceForm_nondegenerate_of_algEquiv e algebra_traceForm_pi_nondegenerate

end ChoppedPlane
