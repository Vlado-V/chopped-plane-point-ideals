module

public import ChoppedPlane.LaurentPairing
public import ChoppedPlane.PolynomialFactorialWeights
public import ChoppedPlane.HomogeneousTensorCoordinates

@[expose] public section

/-!
Factorial-weighted perfect residue pairings on genuine finite Laurent grades.
Generator shifts are complemented by `g ↦ 2-g`; auxiliary monomials carry the
product of their exponent factorials, making differentiation adjoint to
multiplication by an auxiliary variable.
-/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
variable {K : Type*} [Field K] {ι : Type*}

/-- Diagonal coefficient rescaling is an actual equivalence on a finite
coefficient space whenever every weight is nonzero. -/
def coefficientWeightEquiv [Finite ι] (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    (ι →₀ K) ≃ₗ[K] (ι →₀ K) :=
  (Finsupp.linearEquivFunOnFinite K K ι).trans
    ((LinearEquiv.piCongrRight (fun i => LinearEquiv.smulOfNeZero K K (w i) (hw i))).trans
      (Finsupp.linearEquivFunOnFinite K K ι).symm)

@[simp] theorem coefficientWeightEquiv_apply [Finite ι] (w : ι → K)
    (hw : ∀ i, w i ≠ 0) (p : ι →₀ K) (i : ι) :
    coefficientWeightEquiv w hw p i = w i * p i := rfl

/-- Complementary Laurent coefficient coordinates with a generator-dependent
nonzero coefficient weight. -/
def weightedNegativeCoordinates [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    negativeGrade (K := K) g r ≃ₗ[K] (PositiveIndex g r →₀ K) :=
  (negativeCoordinates g r).trans
    (coefficientWeightEquiv (fun e : PositiveIndex g r => w e.val.1) (fun e => hw e.val.1))

@[simp] theorem weightedNegativeCoordinates_apply [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) (q : negativeGrade (K := K) g r)
    (e : PositiveIndex g r) :
    weightedNegativeCoordinates g r w hw q e = w e.val.1 * q.val (complementIndex g r e).val := rfl

/-- The weighted residue pairing identifies the actual negative Laurent grade
with the full linear dual of its complementary positive polynomial grade. -/
def weightedResidueDualEquiv [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    negativeGrade (K := K) g r ≃ₗ[K] Module.Dual K (positiveGrade (K := K) g r) := by
  classical
  exact (weightedNegativeCoordinates g r w hw).trans
    ((positiveCoordinates g r).symm.trans (positiveBasis g r).toDualEquiv)

def weightedResiduePair [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) :
    negativeGrade (K := K) g r →ₗ[K] positiveGrade (K := K) g r →ₗ[K] K :=
  (weightedResidueDualEquiv g r w hw).toLinearMap

/-- Pairing with an actual positive monomial reads its weighted complementary
Laurent coefficient. -/
@[simp] theorem weightedResiduePair_basis [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0) (q : negativeGrade (K := K) g r)
    (e : PositiveIndex g r) :
    weightedResiduePair g r w hw q (positiveBasis g r e) =
      w e.val.1 * q.val (complementIndex g r e).val := by
  classical
  change (positiveBasis g r).toDualEquiv
    ((positiveCoordinates g r).symm (weightedNegativeCoordinates g r w hw q))
    (positiveBasis g r e) = _
  rw [Basis.toDualEquiv_apply, Basis.toDual_apply_left]
  change positiveCoordinates g r
    ((positiveCoordinates g r).symm (weightedNegativeCoordinates g r w hw q)) e = _
  rw [LinearEquiv.apply_symm_apply]
  exact weightedNegativeCoordinates_apply g r w hw q e

/-- Polynomial coordinate multiplication and projected Laurent coordinate
multiplication remain adjoint under the same generator weight. -/
theorem weightedResiduePair_shift [Finite ι] (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0)
    (q : negativeGrade (K := K) g (r+m.1+m.2)) (p : positiveGrade (K := K) g r) :
    weightedResiduePair g (r+m.1+m.2) w hw q (positiveShift g r m p) =
      weightedResiduePair g r w hw (negativeShift g r m q) p := by
  have h : (weightedResiduePair g (r+m.1+m.2) w hw q).comp (positiveShift g r m) =
      weightedResiduePair g r w hw (negativeShift g r m q) := by
    apply (positiveBasis g r).ext
    intro e
    rw [LinearMap.comp_apply, positiveShift_basis, weightedResiduePair_basis,
      weightedResiduePair_basis, negativeShift_apply]
    have hn : -1 - e.val.2.1 < 0 ∧ -1 - e.val.2.2 < 0 := by
      obtain ⟨ha,hb,hab⟩ := e.property
      omega
    change w e.val.1 * q.val (e.val.1,(-1-(e.val.2.1+m.1),-1-(e.val.2.2+m.2))) =
      w e.val.1 * (if -1-e.val.2.1 < 0 ∧ -1-e.val.2.2 < 0 then
        q.val (e.val.1,((-1-e.val.2.1)-m.1,(-1-e.val.2.2)-m.2)) else 0)
    rw [ite_eq_left hn]
    exact congrArg (fun z : ℤ × ℤ => w e.val.1 * q.val (e.val.1,z))
      (Prod.ext (by omega) (by omega))
  exact LinearMap.congr_fun h p

/-- Under the actual free Laurent module identification, exponent translation
is literal multiplication by its coefficient-one Laurent monomial. -/
theorem freeLaurentEquiv_shift_mul [Finite ι] (m : ℤ × ℤ)
    (p : FreeLaurent K ι) (i : ι) :
    freeLaurentEquiv (shift m p) i =
      AddMonoidAlgebra.single m 1 * freeLaurentEquiv p i := by
  ext e
  simp only [freeLaurentEquiv_coeff, shift_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  exact congrArg (fun z : ℤ × ℤ => p (i,z)) (Prod.ext (by simp; omega) (by simp; omega))

/-- Negative coefficient projection is the actual componentwise negative
Laurent representative map. -/
theorem freeLaurentEquiv_negativePart [Finite ι] (p : FreeLaurent K ι) (i : ι) :
    freeLaurentEquiv (freeNegativePart p) i = negativePart (freeLaurentEquiv p i) := by
  ext e
  simp

variable {J : Type*}

/-- Auxiliary symmetric monomials retain their coefficient-generator shift. -/
def auxiliaryGeneratorWeights (g : J → ℤ) (n : ℕ) : J × Sym (Fin 3) n → ℤ :=
  fun i => g i.1

/-- The factorial weight of one auxiliary symmetric monomial. -/
def auxiliaryFactorialWeight (n : ℕ) : J × Sym (Fin 3) n → K :=
  fun i => ChoppedPlane.factorialWeight K
    (SymmetricDerivative.homogeneousTensorExponent n i.2)

theorem auxiliaryFactorialWeight_ne_zero [CharZero K] (n : ℕ)
    (i : J × Sym (Fin 3) n) : auxiliaryFactorialWeight (K := K) n i ≠ 0 :=
  ChoppedPlane.factorialWeight_ne_zero K _

/-- The actual factorial-weighted finite perfect pairing required by symmetric
powers of the binary free module, including the complementary shifts `2-g`. -/
def auxiliaryResidueDualEquiv [Finite J] [CharZero K] (g : J → ℤ) (r : ℤ) (n : ℕ) :
    negativeGrade (K := K) (auxiliaryGeneratorWeights g n) r ≃ₗ[K]
      Module.Dual K (positiveGrade (K := K) (auxiliaryGeneratorWeights g n) r) :=
  weightedResidueDualEquiv (auxiliaryGeneratorWeights g n) r
    (auxiliaryFactorialWeight n) (auxiliaryFactorialWeight_ne_zero n)

def auxiliaryResiduePair [Finite J] [CharZero K] (g : J → ℤ) (r : ℤ) (n : ℕ) :
    negativeGrade (K := K) (auxiliaryGeneratorWeights g n) r →ₗ[K]
      positiveGrade (K := K) (auxiliaryGeneratorWeights g n) r →ₗ[K] K :=
  (auxiliaryResidueDualEquiv g r n).toLinearMap

@[simp] theorem auxiliaryResiduePair_basis [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (n : ℕ)
    (q : negativeGrade (K := K) (auxiliaryGeneratorWeights g n) r)
    (e : PositiveIndex (auxiliaryGeneratorWeights g n) r) :
    auxiliaryResiduePair g r n q (positiveBasis (auxiliaryGeneratorWeights g n) r e) =
      ChoppedPlane.factorialWeight K (SymmetricDerivative.homogeneousTensorExponent n e.val.1.2) *
        q.val (complementIndex (auxiliaryGeneratorWeights g n) r e).val :=
  weightedResiduePair_basis _ _ _ _ _ _

end ChoppedPlane.LaurentPairing
