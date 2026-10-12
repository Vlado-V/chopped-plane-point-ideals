module

public import ChoppedPlane.SymmetricBaseChange
public import ChoppedPlane.CoprimeDescent
public import Mathlib.Algebra.MvPolynomial.Division
public import ChoppedPlane.QWeylPullback

@[expose] public section

/-! Explicit two-chart coordinate bases for the quadratic syzygies of the
quartic cubic pullback. All matrix identities hold in any commutative ring. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial
open ChoppedPlane.SymmetricDerivative
variable {R : Type*} [CommRing R]

def quarticRow (u v z : R) : Fin 3 → R := ![quarticU u v, quarticV u v, quarticZ u v z]
def quadraticOne (u v z : R) : Fin 3 → R := ![v * z, z * u, u * v]
def quadraticTwo (u v z : R) : Fin 3 → R := ![u ^ 2, v ^ 2, -z ^ 2]

def quarticKernelMatrixU (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  ![![a, 0, 0], quadraticOne u v z, quadraticTwo u v z]

def quarticKernelInverseU (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  ![![quarticU u v, 0, 0],
    ![quarticV u v, z ^ 2 * a, u * v * a],
    ![quarticZ u v z, v ^ 2 * a, -z * u * a]]

def quarticKernelMatrixV (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  ![![0, a, 0], quadraticOne u v z, quadraticTwo u v z]

def quarticKernelInverseV (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  ![![quarticU u v, -z ^ 2 * a, -u * v * a],
    ![quarticV u v, 0, 0],
    ![quarticZ u v z, -u ^ 2 * a, v * z * a]]

/-- The `u`-minor chart supplies a lift and the two quadratic kernel vectors. -/
theorem quarticKernelMatrixU_direction (u v z a : R)
    (hz : z ^ 3 = u ^ 3 + v ^ 3) (ha : quarticU u v * a = 1) :
    ∀ i, ∑ j, quarticRow u v z j * quarticKernelMatrixU u v z a i j =
      if i = 0 then 1 else 0 := by
  intro i
  fin_cases i
  · simpa [Fin.sum_univ_succ, quarticRow, quarticKernelMatrixU] using ha
  · simpa [Fin.sum_univ_succ, quarticRow, quarticKernelMatrixU, quadraticOne, add_assoc] using
      quartic_quadratic_syzygy_one u v z
  · simpa [Fin.sum_univ_succ, quarticRow, quarticKernelMatrixU, quadraticTwo,
      sub_eq_add_neg, add_assoc] using quartic_quadratic_syzygy_two u v z hz

/-- The `v`-minor chart supplies the same quadratic kernel vectors. -/
theorem quarticKernelMatrixV_direction (u v z a : R)
    (hz : z ^ 3 = u ^ 3 + v ^ 3) (ha : quarticV u v * a = 1) :
    ∀ i, ∑ j, quarticRow u v z j * quarticKernelMatrixV u v z a i j =
      if i = 0 then 1 else 0 := by
  intro i
  fin_cases i
  · simpa [Fin.sum_univ_succ, quarticRow, quarticKernelMatrixV] using ha
  · simpa [Fin.sum_univ_succ, quarticRow, quarticKernelMatrixV, quadraticOne, add_assoc] using
      quartic_quadratic_syzygy_one u v z
  · simpa [Fin.sum_univ_succ, quarticRow, quarticKernelMatrixV, quadraticTwo,
      sub_eq_add_neg, add_assoc] using quartic_quadratic_syzygy_two u v z hz

/-- The explicit inverse on the first scalar-minor chart. -/
theorem quarticKernelMatrixU_mul_inverse (u v z a : R)
    (hz : z ^ 3 = u ^ 3 + v ^ 3) (ha : quarticU u v * a = 1) :
    quarticKernelMatrixU u v z a * quarticKernelInverseU u v z a = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, quarticKernelMatrixU,
      quarticKernelInverseU, quadraticOne, quadraticTwo]
  · simpa [mul_comm] using ha
  · simpa [mul_comm, add_assoc] using quartic_quadratic_syzygy_one u v z
  · have h : z * u * (z ^ 2 * a) + u * v * (v ^ 2 * a) = quarticU u v * a := by
      unfold quarticU
      calc
        _ = (u * z ^ 3 + u * v ^ 3) * a := by ring
        _ = _ := by rw [hz]; ring
    exact h.trans ha
  · ring
  · simpa [mul_comm, add_assoc, sub_eq_add_neg] using quartic_quadratic_syzygy_two u v z hz
  · ring
  · have h : v ^ 2 * (u * v * a) + z ^ 2 * (z * u * a) = quarticU u v * a := by
      unfold quarticU
      calc
        _ = (u * z ^ 3 + u * v ^ 3) * a := by ring
        _ = _ := by rw [hz]; ring
    exact h.trans ha

/-- The explicit inverse on the second scalar-minor chart. -/
theorem quarticKernelMatrixV_mul_inverse (u v z a : R)
    (hz : z ^ 3 = u ^ 3 + v ^ 3) (ha : quarticV u v * a = 1) :
    quarticKernelMatrixV u v z a * quarticKernelInverseV u v z a = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, quarticKernelMatrixV,
      quarticKernelInverseV, quadraticOne, quadraticTwo]
  · simpa [mul_comm] using ha
  · simpa [mul_comm, add_assoc] using quartic_quadratic_syzygy_one u v z
  · have h : -(v * z * (z ^ 2 * a)) - u * v * (u ^ 2 * a) = quarticV u v * a := by
      unfold quarticV
      calc
        _ = -(v * z ^ 3 + u ^ 3 * v) * a := by ring
        _ = _ := by rw [hz]; ring
    convert h.trans ha using 1; ring
  · ring
  · simpa [mul_comm, add_assoc, sub_eq_add_neg] using quartic_quadratic_syzygy_two u v z hz
  · ring
  · have h : -(u ^ 2 * (u * v * a)) - z ^ 2 * (v * z * a) = quarticV u v * a := by
      unfold quarticV
      calc
        _ = -(v * z ^ 3 + u ^ 3 * v) * a := by ring
        _ = _ := by rw [hz]; ring
    convert h.trans ha using 1; ring

/-- The integral coordinate substitution obtained by clearing the first minor. -/
def quarticClearU (u v z : R) : Fin 3 → Binary R :=
  ![0, C (z ^ 2) * X 0 + C (u * v) * X 1,
    C (v ^ 2) * X 0 - C (z * u) * X 1]

/-- The integral coordinate substitution obtained by clearing the second minor. -/
def quarticClearV (u v z : R) : Fin 3 → Binary R :=
  ![-C (z ^ 2) * X 0 - C (u * v) * X 1, 0,
    -C (u ^ 2) * X 0 + C (v * z) * X 1]

theorem quarticCoordinatesU_substitution (u v z a : R) :
    binaryRestriction.comp (linearChange (quarticKernelInverseU u v z a)) =
      aeval (fun i => a • quarticClearU u v z i) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearChange_X]
  have h1 : (Fin.cases (0 : Binary R) X (1 : Fin 3)) = X 0 := rfl
  have h2 : (Fin.cases (0 : Binary R) X (2 : Fin 3)) = X 1 := rfl
  fin_cases i <;>
    simp [linearForm, Fin.sum_univ_succ, binaryRestriction, h1, h2,
      quarticKernelInverseU, quarticClearU,
      Algebra.smul_def, algebraMap_eq, map_mul, map_pow, map_neg] <;> ring

theorem quarticCoordinatesV_substitution (u v z a : R) :
    binaryRestriction.comp (linearChange (quarticKernelInverseV u v z a)) =
      aeval (fun i => a • quarticClearV u v z i) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, linearChange_X]
  have h1 : (Fin.cases (0 : Binary R) X (1 : Fin 3)) = X 0 := rfl
  have h2 : (Fin.cases (0 : Binary R) X (2 : Fin 3)) = X 1 := rfl
  fin_cases i <;>
    simp [linearForm, Fin.sum_univ_succ, binaryRestriction, h1, h2,
      quarticKernelInverseV, quarticClearV,
      Algebra.smul_def, algebraMap_eq, map_mul, map_pow, map_neg] <;> ring

open scoped TensorProduct
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The exact denominator exponent on the first scalar-minor chart is the
auxiliary homogeneous degree. -/
theorem quarticCoordinatesU_clear (u v z a : R) (ha : quarticU u v * a = 1)
    {n : ℕ} (P : AuxTensor (R := R) (M := M)) (hP : TensorHomogeneous n P) :
    quarticU u v ^ n • kernelCoordinates (quarticKernelInverseU u v z a) P =
      (aeval (quarticClearU u v z)).toLinearMap.rTensor M P := by
  have hs : kernelCoordinates (quarticKernelInverseU u v z a) P =
      (aeval (fun i => a • quarticClearU u v z i)).toLinearMap.rTensor M P := by
    have h := congrArg (fun T : Aux R →ₐ[R] Binary R => T.toLinearMap.rTensor M)
      (quarticCoordinatesU_substitution u v z a)
    simpa [kernelCoordinates, tensorBinaryRestriction, AlgHom.comp_toLinearMap,
      LinearMap.rTensor_comp] using LinearMap.congr_fun h P
  rw [hs, tensor_substitution_scale a _ P hP, smul_smul, ← mul_pow, ha, one_pow, one_smul]

/-- The second chart has the same exact denominator exponent. -/
theorem quarticCoordinatesV_clear (u v z a : R) (ha : quarticV u v * a = 1)
    {n : ℕ} (P : AuxTensor (R := R) (M := M)) (hP : TensorHomogeneous n P) :
    quarticV u v ^ n • kernelCoordinates (quarticKernelInverseV u v z a) P =
      (aeval (quarticClearV u v z)).toLinearMap.rTensor M P := by
  have hs : kernelCoordinates (quarticKernelInverseV u v z a) P =
      (aeval (fun i => a • quarticClearV u v z i)).toLinearMap.rTensor M P := by
    have h := congrArg (fun T : Aux R →ₐ[R] Binary R => T.toLinearMap.rTensor M)
      (quarticCoordinatesV_substitution u v z a)
    simpa [kernelCoordinates, tensorBinaryRestriction, AlgHom.comp_toLinearMap,
      LinearMap.rTensor_comp] using LinearMap.congr_fun h P
  rw [hs, tensor_substitution_scale a _ P hP, smul_smul, ← mul_pow, ha, one_pow, one_smul]

variable {K : Type*} [Field K] [CharZero K]

/-- The two scalar quartic minors are relatively prime; their explicit Bezout
identities reduce a common divisor to a divisor of both coordinate powers. -/
theorem quartic_binary_relPrime :
    IsRelPrime (quarticU (X 0 : ChoppedPlane.Poly K 2) (X 1))
      (quarticV (X 0 : ChoppedPlane.Poly K 2) (X 1)) := by
  have huv : IsRelPrime (X 0 : ChoppedPlane.Poly K 2) (X 1) := by
    apply (MvPolynomial.X_prime (i := (0 : Fin 2))).irreducible.isRelPrime_iff_not_dvd.mpr
    intro h
    have he := map_dvd (eval ![0,1]) h
    simp at he
  have h3 : IsUnit (3 : ChoppedPlane.Poly K 2) := by
    rw [show (3 : ChoppedPlane.Poly K 2) = C (3 : K) from (map_ofNat C 3).symm]
    exact (isUnit_iff_ne_zero.mpr (by norm_num : (3 : K) ≠ 0)).map
      (C : K →+* ChoppedPlane.Poly K 2)
  intro c hcu hcv
  have hu : c ∣ 3 * (X 0 : ChoppedPlane.Poly K 2) ^ 7 := by
    rw [← quartic_bezout_u (X 0) (X 1)]
    exact dvd_add (dvd_mul_of_dvd_right hcu _) (dvd_mul_of_dvd_right hcv _)
  have hv : c ∣ 3 * (X 1 : ChoppedPlane.Poly K 2) ^ 7 := by
    rw [← quartic_bezout_v (X 0) (X 1)]
    exact dvd_sub (dvd_mul_of_dvd_right hcu _) (dvd_mul_of_dvd_right hcv _)
  exact (huv.pow (m := 7) (n := 7)) ((h3.dvd_mul_left).mp hu) ((h3.dvd_mul_left).mp hv)

end ChoppedPlane.QWeyl

