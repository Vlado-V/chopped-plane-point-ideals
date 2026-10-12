module

public import ChoppedPlane.ChoppedFunctions
public import Mathlib.LinearAlgebra.Dimension.RankNullity

@[expose] public section

/-!
# The difference between two genuine homogeneous quotient functions

For nested submodules the larger quotient dimension is the smaller quotient
dimension plus the dimension of the intervening submodule quotient.  Applied
in each actual homogeneous form space, this gives the Hilbert function of a
chop as the point Hilbert function plus the dimension of the residual piece.
-/
noncomputable section
namespace ChoppedPlane
open Module

variable {K : Type*} [Field K]

/-- A nested submodule, viewed inside its containing submodule, has the same
finite dimension as in the ambient space. -/
theorem finrank_comap_subtype_of_le {V : Type*} [AddCommGroup V] [Module K V]
    (J I : Submodule K V) (hJI : J ≤ I) :
    finrank K (J.comap I.subtype) = finrank K J := by
  have h := (I.equivSubtypeMap (J.comap I.subtype)).finrank_eq
  rw [Submodule.map_comap_subtype, inf_eq_right.mpr hJI] at h
  exact h

/-- Dimension additivity for the quotients of two nested submodules. -/
theorem finrank_quotient_eq_quotient_add_nested {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (J I : Submodule K V) (hJI : J ≤ I) :
    finrank K (V ⧸ J) = finrank K (V ⧸ I) +
      finrank K (I ⧸ J.comap I.subtype) := by
  have hJ := J.finrank_quotient_add_finrank
  have hI := I.finrank_quotient_add_finrank
  have hquot := (J.comap I.subtype).finrank_quotient_add_finrank
  rw [finrank_comap_subtype_of_le J I hJI] at hquot
  omega

/-- Dimension of the quotient between two nested submodules, over the integers. -/
theorem finrank_nested_quotient_int {V : Type*} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (J I : Submodule K V) (hJI : J ≤ I) :
    (finrank K (I ⧸ J.comap I.subtype) : ℤ) =
      (finrank K I : ℤ) - (finrank K J : ℤ) := by
  have h := (J.comap I.subtype).finrank_quotient_add_finrank
  rw [finrank_comap_subtype_of_le J I hJI] at h
  have hc := congrArg (fun j : ℕ => (j : ℤ)) h
  rw [Nat.cast_add] at hc
  omega

/-- Integer-valued form of dimension additivity, with no truncated subtraction. -/
theorem finrank_quotient_eq_quotient_add_nested_int {V : Type*}
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (J I : Submodule K V) (hJI : J ≤ I) :
    (finrank K (V ⧸ J) : ℤ) = (finrank K (V ⧸ I) : ℤ) +
      (finrank K (I ⧸ J.comap I.subtype) : ℤ) := by
  exact_mod_cast finrank_quotient_eq_quotient_add_nested J I hJI

/-- The degree piece of a genuine ideal, inside the actual form space. -/
def idealFormPiece {n : ℕ} (I : Ideal (Poly K n)) (t : ℕ) :
    Submodule K (Forms K n t) :=
  (I.restrictScalars K).comap (Forms K n t).subtype

/-- The actual degree map from forms into the polynomial-ring quotient. -/
def idealFormQuotientMap {n : ℕ} (I : Ideal (Poly K n)) (t : ℕ) :
    Forms K n t →ₗ[K] Poly K n ⧸ I :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.comp (Forms K n t).subtype

/-- Hilbert function as the homogeneous image in a genuine ring quotient. -/
def idealQuotientHilbertFunction {n : ℕ} (I : Ideal (Poly K n)) (t : ℕ) : ℕ :=
  finrank K (idealFormQuotientMap I t).range

@[simp] theorem idealFormQuotientMap_ker {n : ℕ}
    (I : Ideal (Poly K n)) (t : ℕ) :
    (idealFormQuotientMap I t).ker = idealFormPiece I t := by
  ext f
  change Ideal.Quotient.mk I f.val = 0 ↔ f.val ∈ I
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The abstract degree quotient is linearly isomorphic to the genuine degree
image in the polynomial-ring quotient. -/
def idealFormQuotientEquivImage {n : ℕ} (I : Ideal (Poly K n)) (t : ℕ) :
    (Forms K n t ⧸ idealFormPiece I t) ≃ₗ[K]
      (idealFormQuotientMap I t).range :=
  (Submodule.quotEquivOfEq _ _ (idealFormQuotientMap_ker I t).symm).trans
    (idealFormQuotientMap I t).quotKerEquivRange

theorem finrank_idealFormQuotient {n : ℕ} (I : Ideal (Poly K n)) (t : ℕ) :
    finrank K (Forms K n t ⧸ idealFormPiece I t) =
      idealQuotientHilbertFunction I t :=
  (idealFormQuotientEquivImage I t).finrank_eq

/-- Nested ideals induce nested pieces in every genuine homogeneous degree. -/
theorem idealFormPiece_mono {n : ℕ} {J I : Ideal (Poly K n)}
    (hJI : J ≤ I) (t : ℕ) : idealFormPiece J t ≤ idealFormPiece I t :=
  fun _ h => hJI h

/-- The quotient of one submodule by the intersection with another. -/
abbrev nestedSubmoduleQuotient {V : Type*} [AddCommGroup V] [Module K V]
    (J I : Submodule K V) := I ⧸ J.comap I.subtype

/-- The residual degree piece of a pair of genuine ideals. -/
abbrev idealResidualPiece {n : ℕ} (J I : Ideal (Poly K n)) (t : ℕ) : Type _ :=
  nestedSubmoduleQuotient (idealFormPiece J t) (idealFormPiece I t)

/-- Exact Hilbert-function difference for two actual ideals in every degree. -/
theorem idealQuotientHilbertFunction_eq_add_residual {n : ℕ}
    (J I : Ideal (Poly K n)) (hJI : J ≤ I) (t : ℕ) :
    idealQuotientHilbertFunction J t = idealQuotientHilbertFunction I t +
      finrank K (idealResidualPiece J I t) := by
  rw [← finrank_idealFormQuotient J t, ← finrank_idealFormQuotient I t]
  exact finrank_quotient_eq_quotient_add_nested _ _ (idealFormPiece_mono hJI t)

/-- Integer version of the exact Hilbert-function difference for actual ideals. -/
theorem idealQuotientHilbertFunction_eq_add_residual_int {n : ℕ}
    (J I : Ideal (Poly K n)) (hJI : J ≤ I) (t : ℕ) :
    (idealQuotientHilbertFunction J t : ℤ) =
      (idealQuotientHilbertFunction I t : ℤ) +
      (finrank K (idealResidualPiece J I t) : ℤ) := by
  exact_mod_cast idealQuotientHilbertFunction_eq_add_residual J I hJI t

@[simp] theorem idealFormPiece_pointIdeal {p : ℕ}
    (a : PointCoordinates K p) (t : ℕ) :
    idealFormPiece (pointIdeal K a) t = pointDegreePiece K a t := by
  ext f
  exact homogeneous_mem_pointIdeal_iff a f

@[simp] theorem idealQuotientHilbertFunction_pointIdeal {p : ℕ}
    (a : PointCoordinates K p) (t : ℕ) :
    idealQuotientHilbertFunction (pointIdeal K a) t = pointHilbertFunction K a t := by
  rw [← finrank_idealFormQuotient, idealFormPiece_pointIdeal]
  rfl

@[simp] theorem idealQuotientHilbertFunction_choppedIdeal {p : ℕ}
    (a : PointCoordinates K p) (d t : ℕ) :
    idealQuotientHilbertFunction (choppedIdeal K a d) t =
      choppedHilbertFunction a d t := rfl

/-- Above the generating degree, the genuine chopped-ideal piece is the
homogeneous product space used by the multiplication maps. -/
@[simp] theorem idealFormPiece_choppedIdeal_add {p : ℕ}
    (a : PointCoordinates K p) (d e : ℕ) :
    idealFormPiece (choppedIdeal K a d) (d + e) =
      generatedProducts (d := d) (pointDegreeSpace K a d) e := by
  rw [← idealFormQuotientMap_ker]
  exact ker_formToRingQuotient _ (pointDegreeSpace_homogeneous a) e

/-- In every degree, the actual chop quotient dimension is the point quotient
dimension plus the dimension of the actual residual ideal quotient. -/
theorem choppedHilbertFunction_eq_point_add_residual {p : ℕ}
    (a : PointCoordinates K p) (d t : ℕ) :
    choppedHilbertFunction a d t = pointHilbertFunction K a t +
      finrank K (idealResidualPiece (choppedIdeal K a d) (pointIdeal K a) t) := by
  simpa using idealQuotientHilbertFunction_eq_add_residual
    (choppedIdeal K a d) (pointIdeal K a) (choppedIdeal_le_pointIdeal a) t

/-- The same chop identity over the integers, useful for numerator formulas. -/
theorem choppedHilbertFunction_eq_point_add_residual_int {p : ℕ}
    (a : PointCoordinates K p) (d t : ℕ) :
    (choppedHilbertFunction a d t : ℤ) = (pointHilbertFunction K a t : ℤ) +
      (finrank K (idealResidualPiece (choppedIdeal K a d) (pointIdeal K a) t) : ℤ) := by
  exact_mod_cast choppedHilbertFunction_eq_point_add_residual a d t

end ChoppedPlane
