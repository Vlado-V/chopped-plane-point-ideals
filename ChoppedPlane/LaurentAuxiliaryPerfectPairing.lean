module

public import ChoppedPlane.LaurentAuxiliaryAdjoints

@[expose] public section

/-! Perfect factorial-weighted residue duality in finite auxiliary
coefficient coordinates, and actual transpose conjugacy for three-operator
differentiation and projected auxiliary multiplication. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ChoppedPlane.LaurentPairing
open Module SymmetricDerivative
variable {K : Type*} [Field K] {J : Type*}

/-- Actual perfect duality after coefficient-preserving finite flattening. -/
def auxiliaryCoefficientResidueDualEquiv [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    (Sym (Fin 3) t → negativeGrade (K := K) g r) ≃ₗ[K]
      Module.Dual K (Sym (Fin 3) t → positiveGrade (K := K) g r) :=
  (negativeGradeSplit g r).symm.trans
    ((auxiliaryResidueDualEquiv g r t).trans (positiveGradeSplit g r).symm.dualMap)

@[simp] theorem auxiliaryCoefficientResidueDualEquiv_apply [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ)
    (q : Sym (Fin 3) t → negativeGrade (K := K) g r)
    (p : Sym (Fin 3) t → positiveGrade (K := K) g r) :
    auxiliaryCoefficientResidueDualEquiv g r t q p =
      auxiliaryCoefficientPair (residuePair g r) t q p := by
  change auxiliaryResiduePair g r t ((negativeGradeSplit g r).symm q)
    ((positiveGradeSplit g r).symm p) = _
  simpa only [auxiliaryGeneratorWeights, LinearEquiv.apply_symm_apply] using
    (auxiliaryResiduePair_eq_coefficientPair (K := K) g r t
      ((negativeGradeSplit g r).symm q) ((positiveGradeSplit g r).symm p))

end ChoppedPlane.LaurentPairing
