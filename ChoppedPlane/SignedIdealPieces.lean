module

public import ChoppedPlane.GradedPresentation
public import ChoppedPlane.HilbertDifference

@[expose] public section

/-!
# Actual ideal pieces with signed degrees

Canonical degree transport and the comparison with natural homogeneous
pieces preserve the underlying polynomial of every representative.
-/
noncomputable section
namespace ChoppedPlane

variable {K : Type*} [Field K] {n : ℕ}

/-- The genuine ideal piece inside the signed homogeneous form space. -/
def signedIdealPiece (I : Ideal (Poly K n)) (t : ℤ) :
    Submodule K (signedForms K n t) :=
  (I.restrictScalars K).comap (signedForms K n t).subtype

/-- The actual residual ideal quotient in a signed homogeneous degree. -/
abbrev signedIdealResidualPiece (J I : Ideal (Poly K n)) (t : ℤ) :=
  nestedSubmoduleQuotient (signedIdealPiece J t) (signedIdealPiece I t)

/-- Equal signed degrees canonically identify the ideal pieces. -/
def signedIdealPieceEquivOfEq (I : Ideal (Poly K n)) {t u : ℤ} (h : t = u) :
    signedIdealPiece I t ≃ₗ[K] signedIdealPiece I u := by
  subst u
  exact LinearEquiv.refl K _

@[simp] theorem signedIdealPieceEquivOfEq_val (I : Ideal (Poly K n))
    {t u : ℤ} (h : t = u) (f : signedIdealPiece I t) :
    ((signedIdealPieceEquivOfEq I h f).val).val = f.val.val := by
  subst u
  rfl

/-- At a natural degree, signed and ordinary ideal pieces canonically agree. -/
def signedIdealPieceNatEquiv (I : Ideal (Poly K n)) (t : ℕ) :
    signedIdealPiece I (t : ℤ) ≃ₗ[K] idealFormPiece I t where
  toFun f := ⟨⟨f.val.val, by simpa only [signedForms_nat] using f.val.property⟩, f.property⟩
  invFun f := ⟨⟨f.val.val, by simpa only [signedForms_nat] using f.val.property⟩, f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem signedIdealPieceNatEquiv_val (I : Ideal (Poly K n))
    (t : ℕ) (f : signedIdealPiece I (t : ℤ)) :
    ((signedIdealPieceNatEquiv I t f).val).val = f.val.val := rfl

@[simp] theorem signedIdealPieceNatEquiv_symm_val (I : Ideal (Poly K n))
    (t : ℕ) (f : idealFormPiece I t) :
    (((signedIdealPieceNatEquiv I t).symm f).val).val = f.val.val := rfl

/-- Transport a signed ideal piece to an ordinary piece whenever its degree
is equal to the corresponding natural degree. -/
def signedIdealPieceEquivNatOfEq (I : Ideal (Poly K n))
    {u : ℤ} (t : ℕ) (h : u = (t : ℤ)) :
    signedIdealPiece I u ≃ₗ[K] idealFormPiece I t :=
  (signedIdealPieceEquivOfEq I h).trans (signedIdealPieceNatEquiv I t)

@[simp] theorem signedIdealPieceEquivNatOfEq_val (I : Ideal (Poly K n))
    {u : ℤ} (t : ℕ) (h : u = (t : ℤ)) (f : signedIdealPiece I u) :
    ((signedIdealPieceEquivNatOfEq I t h f).val).val = f.val.val := by
  simp [signedIdealPieceEquivNatOfEq]

/-- The natural comparison carries the actual residual submodule onto the
ordinary residual submodule. -/
theorem signedIdealPieceNatEquiv_map_residual (J I : Ideal (Poly K n)) (t : ℕ) :
    ((signedIdealPiece J (t : ℤ)).comap (signedIdealPiece I (t : ℤ)).subtype).map
      (signedIdealPieceNatEquiv I t).toLinearMap =
      (idealFormPiece J t).comap (idealFormPiece I t).subtype := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact hg
  · intro hf
    refine ⟨(signedIdealPieceNatEquiv I t).symm f, hf, ?_⟩
    exact (signedIdealPieceNatEquiv I t).apply_symm_apply f

/-- The actual signed residual quotient is canonically equivalent to the
ordinary residual quotient in every natural degree. -/
def signedIdealResidualPieceNatEquiv (J I : Ideal (Poly K n)) (t : ℕ) :
    signedIdealResidualPiece J I (t : ℤ) ≃ₗ[K] idealResidualPiece J I t :=
  Submodule.Quotient.equiv _ _ (signedIdealPieceNatEquiv I t)
    (signedIdealPieceNatEquiv_map_residual J I t)

/-- This quotient comparison sends each class to the class represented by the
same polynomial in the ordinary homogeneous space. -/
@[simp] theorem signedIdealResidualPieceNatEquiv_mk (J I : Ideal (Poly K n))
    (t : ℕ) (f : signedIdealPiece I (t : ℤ)) :
    signedIdealResidualPieceNatEquiv J I t (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (signedIdealPieceNatEquiv I t f) := rfl

/-- Equal signed target degrees canonically identify the residual quotients. -/
def signedIdealResidualPieceEquivOfEq (J I : Ideal (Poly K n))
    {t u : ℤ} (h : t = u) :
    signedIdealResidualPiece J I t ≃ₗ[K] signedIdealResidualPiece J I u := by
  subst u
  exact LinearEquiv.refl K _

/-- Transport a signed residual quotient to an ordinary one at an equal
natural target degree. -/
def signedIdealResidualPieceEquivNatOfEq (J I : Ideal (Poly K n))
    {u : ℤ} (t : ℕ) (h : u = (t : ℤ)) :
    signedIdealResidualPiece J I u ≃ₗ[K] idealResidualPiece J I t :=
  (signedIdealResidualPieceEquivOfEq J I h).trans
    (signedIdealResidualPieceNatEquiv J I t)

@[simp] theorem finrank_signedIdealResidualPiece_nat (J I : Ideal (Poly K n)) (t : ℕ) :
    Module.finrank K (signedIdealResidualPiece J I (t : ℤ)) =
      Module.finrank K (idealResidualPiece J I t) :=
  (signedIdealResidualPieceNatEquiv J I t).finrank_eq

/-- Nested genuine ideals induce nested signed homogeneous pieces. -/
theorem signedIdealPiece_mono {J I : Ideal (Poly K n)} (hJI : J ≤ I) (t : ℤ) :
    signedIdealPiece J t ≤ signedIdealPiece I t := fun _ hf => hJI hf

end ChoppedPlane
