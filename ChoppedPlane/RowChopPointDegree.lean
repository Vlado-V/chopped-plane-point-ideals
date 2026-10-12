module

public import ChoppedPlane.RowChopPresentation

@[expose] public section

/-!
# Identifying the actual degree chop with the quadratic-row minors

The graded cofactor surjection in degree zero has constant coefficients in
quadratic rows and no coefficients in linear rows. Thus the degree-`d` piece
is the coefficient-field span of the actual degree-`d` maximal minors.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K] {n p r a c d : ℕ}

/-- Signed degree-zero polynomials are actual constants. -/
theorem signedForms_zero_eq_C (f : signedForms K n 0) : f.val = C (f.val.coeff 0) := by
  obtain ⟨a,ha⟩ : ∃ a : K, C a = f.val := by simpa [signedForms] using f.property
  rw [← ha]
  simp

/-- The actual degree-`d` piece of the maximal-minor ideal is the span of the
quadratic-row cofactors. No exactness or primitivity assumption is required. -/
theorem idealFormPiece_map_eq_quadraticMinorSpace
    (B : Matrix (Fin (c+1)) (Fin c) (Poly K n)) (h : r+a=c+1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hdegree : ∑ i, standardRowDegrees r c i = d+2) :
    (idealFormPiece (maximalMinorIdeal B) d).map (Forms K n d).subtype =
      quadraticMinorSpace B h := by
  classical
  apply le_antisymm
  · rintro f ⟨g,hg,rfl⟩
    have ht : (0 : ℤ)-2+(∑ i, standardRowDegrees r c i : ℕ) = d := by
      rw [hdegree]
      omega
    let E : rowCofactorImage (r := r) B hB 0 ≃ₗ[K]
        idealFormPiece (maximalMinorIdeal B) d :=
      (rowCofactorImageEquivSignedIdeal B hB 0).trans
        (signedIdealPieceEquivNatOfEq (maximalMinorIdeal B) d ht)
    let fI : idealFormPiece (maximalMinorIdeal B) d := ⟨g,hg⟩
    let fimage := E.symm fI
    have hE (q : rowCofactorImage (r := r) B hB 0) : (E q).val.val = q.val.val := by
      change ((signedIdealPieceEquivNatOfEq (maximalMinorIdeal B) d ht)
        (rowCofactorImageEquivSignedIdeal B hB 0 q)).val.val = q.val.val
      rw [signedIdealPieceEquivNatOfEq_val,rowCofactorImageEquivSignedIdeal_val]
    have hrep : fimage.val.val = g.val := by
      calc
        _ = (E fimage).val.val := (hE fimage).symm
        _ = fI.val.val := congrArg (fun q : idealFormPiece (maximalMinorIdeal B) d => q.val.val)
          (E.apply_symm_apply fI)
        _ = g.val := rfl
    obtain ⟨⟨v,w⟩,hv⟩ := splitCofactorMap_surjective B h hB 0 fimage
    have hw : w = 0 := by
      funext i
      apply Subtype.ext
      have hh := (w i).property
      simpa [signedForms] using hh
    subst w
    have hcomb : (∑ i : Fin r, signedMaximalMinor B (quadraticRow h i) * (v i).val) =
        g.val := by
      calc
        _ = (splitCofactorMap B h hB 0 (v,0)).val.val :=
          (splitCofactorMap_quadratic_val B h hB 0 v).symm
        _ = fimage.val.val := congrArg (fun q => q.val.val) hv
        _ = g.val := hrep
    change g.val ∈ quadraticMinorSpace B h
    rw [← hcomb]
    apply Submodule.sum_mem
    intro i _
    rw [signedForms_zero_eq_C (v i),mul_comm,← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro f ⟨i,rfl⟩
    apply Submodule.mem_map.mpr
    refine ⟨⟨signedMaximalMinor B (quadraticRow h i),
      quadraticMinor_homogeneous B h hB hdegree i⟩,?_,rfl⟩
    change signedMaximalMinor B (quadraticRow h i) ∈ maximalMinorIdeal B
    exact Ideal.subset_span ⟨quadraticRow h i,rfl⟩

/-- Equality of genuine ideal pieces identifies the actual point equation
space in the chop degree with the quadratic-row maximal minors. -/
theorem pointDegreeSpace_eq_quadraticMinorSpace
    (B : Matrix (Fin (c+1)) (Fin c) (Poly K 3)) (h : r+a=c+1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hdegree : ∑ i, standardRowDegrees r c i = d+2)
    (cfg : PointCoordinates K p)
    (hpieces : ∀ t, pointDegreePiece K cfg t = idealFormPiece (maximalMinorIdeal B) t) :
    pointDegreeSpace K cfg d = quadraticMinorSpace B h := by
  rw [pointDegreeSpace,hpieces d]
  exact idealFormPiece_map_eq_quadraticMinorSpace B h hB hdegree

/-- Consequently the actual point chop is precisely the quadratic-minor ideal. -/
theorem choppedIdeal_eq_quadraticMinorIdeal
    (B : Matrix (Fin (c+1)) (Fin c) (Poly K 3)) (h : r+a=c+1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hdegree : ∑ i, standardRowDegrees r c i = d+2)
    (cfg : PointCoordinates K p)
    (hpieces : ∀ t, pointDegreePiece K cfg t = idealFormPiece (maximalMinorIdeal B) t) :
    choppedIdeal K cfg d = quadraticMinorIdeal B h := by
  rw [choppedIdeal,pointDegreeSpace_eq_quadraticMinorSpace B h hB hdegree cfg hpieces]
  exact quadraticMinorSpace_idealSpan B h

/-- The actual chopped Hilbert function is the quotient Hilbert function of
the quadratic-minor ideal appearing in the row presentation. -/
theorem choppedHilbertFunction_eq_quadraticMinorIdeal
    (B : Matrix (Fin (c+1)) (Fin c) (Poly K 3)) (h : r+a=c+1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hdegree : ∑ i, standardRowDegrees r c i = d+2)
    (cfg : PointCoordinates K p)
    (hpieces : ∀ t, pointDegreePiece K cfg t = idealFormPiece (maximalMinorIdeal B) t)
    (t : ℕ) :
    choppedHilbertFunction cfg d t = idealQuotientHilbertFunction (quadraticMinorIdeal B h) t := by
  rw [choppedHilbertFunction,pointDegreeSpace_eq_quadraticMinorSpace B h hB hdegree cfg hpieces]
  rw [← quadraticMinorSpace_idealSpan]
  rfl

end ChoppedPlane
