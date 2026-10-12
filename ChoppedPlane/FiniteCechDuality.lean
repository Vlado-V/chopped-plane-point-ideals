module

public import Mathlib.Tactic
public import Mathlib.Algebra.MvPolynomial.Division
public import ChoppedPlane.SymmetricDerivative

@[expose] public section

/-!
# The linear diagram chase for two-chart duality

For the binary Laurent complex the horizontal arrows below are the two-chart
difference maps, and the vertical arrows are multiplication by the auxiliary
linear form.  Injectivity of the right vertical map and the lower horizontal
map turns vanishing of the kernel on the lower quotients into injectivity on
the upper Laurent quotient.  The statement only uses ranges of linear maps;
it does not assume a sheaf-cohomology or duality theorem.
-/

namespace ChoppedPlane

set_option maxHeartbeats 1000000

section Diagram

variable {R A₁ A₂ B₁ B₂ : Type*} [Semiring R]
variable [AddCommMonoid A₁] [Module R A₁]
variable [AddCommMonoid A₂] [Module R A₂]
variable [AddCommMonoid B₁] [Module R B₁]
variable [AddCommMonoid B₂] [Module R B₂]

/-- A two-chart diagram chase, stated directly in terms of polynomial and
Laurent representatives.  The left side says that the upper quotient map is
injective.  The right side says that a compatible pair of local lower
quotient representatives comes from a local upper representative. -/
theorem linear_cech_vanishing_iff
    (dA : A₁ →ₗ[R] A₂) (dB : B₁ →ₗ[R] B₂)
    (l₁ : A₁ →ₗ[R] B₁) (l₂ : A₂ →ₗ[R] B₂)
    (hcomm : ∀ a, dB (l₁ a) = l₂ (dA a))
    (hdB : Function.Injective dB) (hl₂ : Function.Injective l₂) :
    (∀ a, l₂ a ∈ LinearMap.range dB → a ∈ LinearMap.range dA) ↔
      (∀ b, dB b ∈ LinearMap.range l₂ → b ∈ LinearMap.range l₁) := by
  constructor
  · intro h b hb
    obtain ⟨a, ha⟩ := hb
    have hla : l₂ a ∈ LinearMap.range dB := ⟨b, ha.symm⟩
    obtain ⟨a₁, ha₁⟩ := h a hla
    refine ⟨a₁, hdB ?_⟩
    calc
      dB (l₁ a₁) = l₂ (dA a₁) := hcomm a₁
      _ = l₂ a := congrArg l₂ ha₁
      _ = dB b := ha
  · intro h a ha
    obtain ⟨b, hb⟩ := ha
    have hdb : dB b ∈ LinearMap.range l₂ := ⟨a, hb.symm⟩
    obtain ⟨a₁, ha₁⟩ := h b hdb
    refine ⟨a₁, hl₂ ?_⟩
    calc
      l₂ (dA a₁) = dB (l₁ a₁) := (hcomm a₁).symm
      _ = dB b := congrArg dB ha₁
      _ = l₂ a := hb

end Diagram

section CrossDiagram

variable {R A₁ A₂ B₁ B₂ C₁ C₂ : Type*} [Semiring R]
variable [AddCommMonoid A₁] [Module R A₁]
variable [AddCommMonoid A₂] [Module R A₂]
variable [AddCommMonoid B₁] [Module R B₁]
variable [AddCommMonoid B₂] [Module R B₂]
variable [AddCommMonoid C₁] [Module R C₁]
variable [AddCommMonoid C₂] [Module R C₂]

/-- Apply the two-chart chase to local cross-product maps.  The third
horizontal map is the difference map on directional kernels.  Its
injectivity says that the global directional kernel vanishes. -/
theorem linear_cech_cross_descent
    (dA : A₁ →ₗ[R] A₂) (dB : B₁ →ₗ[R] B₂)
    (l₁ : A₁ →ₗ[R] B₁) (l₂ : A₂ →ₗ[R] B₂)
    (q₁ : B₁ →ₗ[R] C₁) (q₂ : B₂ →ₗ[R] C₂) (dC : C₁ →ₗ[R] C₂)
    (hcomm : ∀ a, dB (l₁ a) = l₂ (dA a))
    (hcross : ∀ b, dC (q₁ b) = q₂ (dB b))
    (hdB : Function.Injective dB) (hl₂ : Function.Injective l₂)
    (hdC : Function.Injective dC)
    (hker₁ : LinearMap.ker q₁ = LinearMap.range l₁)
    (hzero₂ : ∀ a, q₂ (l₂ a) = 0) :
    ∀ a, l₂ a ∈ LinearMap.range dB → a ∈ LinearMap.range dA := by
  apply (linear_cech_vanishing_iff dA dB l₁ l₂ hcomm hdB hl₂).mpr
  intro b hb
  rw [← hker₁, LinearMap.mem_ker]
  apply hdC
  rw [hcross, map_zero]
  obtain ⟨a, ha⟩ := hb
  rw [← ha]
  exact hzero₂ a

end CrossDiagram

namespace FiniteCech

noncomputable section

open MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {R : Type*} [CommRing R]

/-- The skew matrix of the cross product with `(u,v,z)`. -/
def crossMatrix (u v z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, -z, v; z, 0, -u; -v, u, 0]

/-- A coordinate change with first coordinate `uX+vY+zZ`. -/
def quotientCoordinates (u v z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![u, v, z; 0, 1, 0; 0, 0, 1]

def quotientCoordinatesInv (v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, -a * v, -a * z; 0, 1, 0; 0, 0, 1]

/-- A derivative lift followed by the two nonzero cross-product rows. -/
def crossKernelCoordinates (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![a, 0, 0; z, 0, -u; -v, u, 0]

def crossKernelCoordinatesInv (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![u, 0, 0; v, 0, a; z, -a, 0]

theorem quotientCoordinates_inverse (u v z a : R) (hua : u * a = 1) :
    quotientCoordinates u v z * quotientCoordinatesInv v z a = 1 ∧
      quotientCoordinatesInv v z a * quotientCoordinates u v z = 1 := by
  have hau : a * u = 1 := by simpa [mul_comm] using hua
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quotientCoordinates, quotientCoordinatesInv, Matrix.mul_apply,
      Fin.sum_univ_three, ← mul_assoc, hua, hau]

theorem crossKernelCoordinates_inverse (u v z a : R) (hua : u * a = 1) :
    crossKernelCoordinates u v z a * crossKernelCoordinatesInv u v z a = 1 ∧
      crossKernelCoordinatesInv u v z a * crossKernelCoordinates u v z a = 1 := by
  have hau : a * u = 1 := by simpa [mul_comm] using hua
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [crossKernelCoordinates, crossKernelCoordinatesInv, Matrix.mul_apply,
      Fin.sum_univ_three, hua, hau] <;> ring

theorem crossKernelCoordinates_derivative (u v z a : R) (hua : u * a = 1) :
    ∀ i : Fin 3, ∑ j, (![u,v,z] : Fin 3 → R) j *
      crossKernelCoordinates u v z a i j = if i = 0 then 1 else 0 := by
  intro i
  fin_cases i <;> simp [crossKernelCoordinates, Fin.sum_univ_three, hua] <;> ring

@[simp] theorem zeroFirst_X (i : Fin 3) :
    zeroFirst (X i : Aux R) = if i = 0 then 0 else X i := by
  classical
  rw [show (X i : Aux R) = monomial (Finsupp.single i 1) 1 from rfl,
    zeroFirst_monomial]
  by_cases hi : i = 0
  · subst i
    simp
  · simp [hi, Ne.symm hi]

def firstProjectionMatrix : Matrix (Fin 3) (Fin 3) R :=
  !![0, 0, 0; 0, 1, 0; 0, 0, 1]

theorem zeroFirst_asLinearChange :
    (zeroFirst : Aux R →ₗ[R] Aux R) =
      (linearChange firstProjectionMatrix).toLinearMap := by
  have h : binaryEmbedding.comp binaryRestriction =
      (linearChange firstProjectionMatrix : Aux R →ₐ[R] Aux R) := by
    apply MvPolynomial.algHom_ext
    intro i
    change zeroFirst (X i : Aux R) = linearChange firstProjectionMatrix (X i)
    rw [zeroFirst_X, linearChange_X]
    fin_cases i <;> simp [firstProjectionMatrix, linearForm, Fin.sum_univ_three]
  exact congrArg AlgHom.toLinearMap h

/-- Cross-product substitution, after quotient coordinates, is a binary
projection followed by an invertible kernel-coordinate transformation. -/
theorem cross_projection_factorization (u v z a : R) :
    ((linearChange (crossMatrix u v z)).toLinearMap).comp
      (linearChange (quotientCoordinates u v z)).toLinearMap =
    ((linearChange (crossKernelCoordinates u v z a)).toLinearMap).comp
      zeroFirst := by
  have hm : quotientCoordinates u v z * crossMatrix u v z =
      firstProjectionMatrix * crossKernelCoordinates u v z a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quotientCoordinates, crossMatrix, firstProjectionMatrix,
        crossKernelCoordinates, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  rw [zeroFirst_asLinearChange]
  apply LinearMap.ext
  intro P
  change ((linearChange (crossMatrix u v z)).comp
      (linearChange (quotientCoordinates u v z))) P =
    ((linearChange (crossKernelCoordinates u v z a)).comp
      (linearChange firstProjectionMatrix)) P
  rw [linearChange_comp, linearChange_comp, hm]

def quotientCoordinatesV (u v z : R) : Matrix (Fin 3) (Fin 3) R :=
  !![u, v, z; 1, 0, 0; 0, 0, 1]

def quotientCoordinatesVInv (u z a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, 1, 0; a, -a * u, -a * z; 0, 0, 1]

def crossKernelCoordinatesV (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, a, 0; 0, -z, v; -v, u, 0]

def crossKernelCoordinatesVInv (u v z a : R) : Matrix (Fin 3) (Fin 3) R :=
  !![u, 0, -a; v, 0, 0; z, a, 0]

theorem quotientCoordinatesV_inverse (u v z a : R) (hva : v * a = 1) :
    quotientCoordinatesV u v z * quotientCoordinatesVInv u z a = 1 ∧
      quotientCoordinatesVInv u z a * quotientCoordinatesV u v z = 1 := by
  have hav : a * v = 1 := by simpa [mul_comm] using hva
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [quotientCoordinatesV, quotientCoordinatesVInv, Matrix.mul_apply,
      Fin.sum_univ_three, ← mul_assoc, hva, hav]

theorem crossKernelCoordinatesV_inverse (u v z a : R) (hva : v * a = 1) :
    crossKernelCoordinatesV u v z a * crossKernelCoordinatesVInv u v z a = 1 ∧
      crossKernelCoordinatesVInv u v z a * crossKernelCoordinatesV u v z a = 1 := by
  have hav : a * v = 1 := by simpa [mul_comm] using hva
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [crossKernelCoordinatesV, crossKernelCoordinatesVInv, Matrix.mul_apply,
      Fin.sum_univ_three, hva, hav] <;> ring

theorem crossKernelCoordinatesV_derivative (u v z a : R) (hva : v * a = 1) :
    ∀ i : Fin 3, ∑ j, (![u,v,z] : Fin 3 → R) j *
      crossKernelCoordinatesV u v z a i j = if i = 0 then 1 else 0 := by
  intro i
  fin_cases i <;> simp [crossKernelCoordinatesV, Fin.sum_univ_three, hva] <;> ring

theorem cross_projection_factorizationV (u v z a : R) :
    ((linearChange (crossMatrix u v z)).toLinearMap).comp
      (linearChange (quotientCoordinatesV u v z)).toLinearMap =
    ((linearChange (crossKernelCoordinatesV u v z a)).toLinearMap).comp
      zeroFirst := by
  have hm : quotientCoordinatesV u v z * crossMatrix u v z =
      firstProjectionMatrix * crossKernelCoordinatesV u v z a := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [quotientCoordinatesV, crossMatrix, firstProjectionMatrix,
        crossKernelCoordinatesV, Matrix.mul_apply, Fin.sum_univ_three] <;> ring
  rw [zeroFirst_asLinearChange]
  apply LinearMap.ext
  intro P
  change ((linearChange (crossMatrix u v z)).comp
      (linearChange (quotientCoordinatesV u v z))) P =
    ((linearChange (crossKernelCoordinatesV u v z a)).comp
      (linearChange firstProjectionMatrix)) P
  rw [linearChange_comp, linearChange_comp, hm]

/-- Divide by the first auxiliary variable, discarding its constant term. -/
def divideFirst : Aux R →ₗ[R] Aux R where
  toFun P := P.divMonomial (Finsupp.single 0 1)
  map_add' P Q := add_divMonomial P Q _
  map_smul' r P := by
    ext s
    simp [coeff_divMonomial]

def multiplyFirst : Aux R →ₗ[R] Aux R := LinearMap.mulLeft R (X 0)

theorem zeroFirst_coeff (P : Aux R) (s : Fin 3 →₀ ℕ) :
    (zeroFirst P).coeff s = if s 0 = 0 then P.coeff s else 0 := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [map_add]
    change (zeroFirst P).coeff s + (zeroFirst Q).coeff s =
      if s 0 = 0 then P.coeff s + Q.coeff s else 0
    rw [hP, hQ]
    split_ifs <;> simp
  | monomial t r =>
    by_cases hts : t = s
    · subst t
      by_cases hs : s 0 = 0 <;> simp [zeroFirst_monomial, hs]
    · by_cases ht : t 0 = 0 <;> by_cases hs : s 0 = 0 <;>
        simp [zeroFirst_monomial, ht, hs, coeff_monomial, hts]

theorem zeroFirst_eq_modMonomial (P : Aux R) :
    zeroFirst P = P.modMonomial (Finsupp.single 0 1) := by
  ext s
  rw [zeroFirst_coeff]
  by_cases hs : s 0 = 0
  · rw [ite_eq_left hs, coeff_modMonomial_of_not_le]
    simp [Finsupp.single_le_iff, hs]
  · rw [ite_eq_right hs, coeff_modMonomial_of_le]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs)

theorem multiplyFirst_divideFirst_add_zeroFirst (P : Aux R) :
    multiplyFirst (divideFirst P) + zeroFirst P = P := by
  rw [zeroFirst_eq_modMonomial]
  exact P.divMonomial_add_modMonomial_single 0

@[simp] theorem divideFirst_multiplyFirst (P : Aux R) :
    divideFirst (multiplyFirst P) = P := by
  change (X 0 * P).divMonomial (Finsupp.single 0 1) = P
  simpa only [X] using divMonomial_monomial_mul (Finsupp.single 0 1) P

@[simp] theorem zeroFirst_multiplyFirst (P : Aux R) :
    zeroFirst (multiplyFirst P) = 0 := by
  change binaryEmbedding (R := R)
    (binaryRestriction (R := R) ((X (0 : Fin 3) : Aux R) * P)) = 0
  rw [map_mul]
  have hx : binaryRestriction (X (0 : Fin 3) : Aux R) = 0 := by
    simp [binaryRestriction]
  rw [hx, zero_mul, map_zero]

theorem divideFirst_homogeneousComponent (n : ℕ) (P : Aux R) :
    homogeneousComponent n (divideFirst P) =
      divideFirst (homogeneousComponent (n + 1) P) := by
  ext s
  change (homogeneousComponent n
      (P.divMonomial (Finsupp.single 0 1))).coeff s =
    ((homogeneousComponent (n + 1) P).divMonomial (Finsupp.single 0 1)).coeff s
  simp only [coeff_homogeneousComponent, coeff_divMonomial]
  have hd : (Finsupp.single (0 : Fin 3) 1 + s).degree = s.degree + 1 := by
    simp [add_comm]
  simp [hd]

section Tensor

variable {M : Type*} [AddCommGroup M] [Module R M]

def tensorZeroFirst : AuxTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  zeroFirst.rTensor M

def tensorMultiplyFirst : AuxTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  multiplyFirst.rTensor M

def tensorDivideFirst : AuxTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  divideFirst.rTensor M

theorem tensor_first_variable_split (P : AuxTensor (R := R) (M := M)) :
    tensorMultiplyFirst (tensorDivideFirst P) + tensorZeroFirst P = P := by
  have hs : multiplyFirst.comp divideFirst + (zeroFirst : Aux R →ₗ[R] Aux R) =
      LinearMap.id := by
    apply LinearMap.ext
    intro P
    exact multiplyFirst_divideFirst_add_zeroFirst P
  have ht := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M) hs
  simp only [LinearMap.rTensor_add, LinearMap.rTensor_comp, LinearMap.rTensor_id] at ht
  exact LinearMap.congr_fun ht P

@[simp] theorem tensor_divideFirst_multiplyFirst (P : AuxTensor (R := R) (M := M)) :
    tensorDivideFirst (tensorMultiplyFirst P) = P := by
  have hs : divideFirst.comp (multiplyFirst : Aux R →ₗ[R] Aux R) = LinearMap.id := by
    apply LinearMap.ext
    intro P
    exact divideFirst_multiplyFirst P
  have ht := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M) hs
  simp only [LinearMap.rTensor_comp, LinearMap.rTensor_id] at ht
  exact LinearMap.congr_fun ht P

@[simp] theorem tensor_zeroFirst_multiplyFirst (P : AuxTensor (R := R) (M := M)) :
    tensorZeroFirst (tensorMultiplyFirst P) = 0 := by
  have hs : zeroFirst.comp (multiplyFirst : Aux R →ₗ[R] Aux R) = 0 := by
    apply LinearMap.ext
    intro P
    exact zeroFirst_multiplyFirst P
  have ht := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M) hs
  simp only [LinearMap.rTensor_comp, LinearMap.rTensor_zero] at ht
  exact LinearMap.congr_fun ht P

/-- The zero-first-coordinate projection has exactly the first-coordinate
multiple kernel, even with arbitrary coefficient modules. -/
theorem tensor_zeroFirst_kernel (P : AuxTensor (R := R) (M := M)) :
    tensorZeroFirst P = 0 ↔ P ∈ LinearMap.range tensorMultiplyFirst := by
  constructor
  · intro hP
    refine ⟨tensorDivideFirst P, ?_⟩
    simpa [hP] using tensor_first_variable_split P
  · rintro ⟨Q, rfl⟩
    exact tensor_zeroFirst_multiplyFirst Q

theorem tensor_multiplyFirst_injective :
    Function.Injective (tensorMultiplyFirst (R := R) (M := M)) := by
  intro P Q h
  simpa using congrArg (tensorDivideFirst (R := R) (M := M)) h

/-- Linear auxiliary substitution with module coefficients. -/
def tensorChange (A : Matrix (Fin 3) (Fin 3) R) :
    AuxTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  (linearChange A).toLinearMap.rTensor M

def tensorMultiplyLinear (f : Fin 3 → R) :
    AuxTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  (LinearMap.mulLeft R (linearForm f)).rTensor M

theorem tensor_cross_projection_factorization (u v z a : R) :
    (tensorChange (M := M) (crossMatrix u v z)).comp
      (tensorChange (quotientCoordinates u v z)) =
    (tensorChange (crossKernelCoordinates u v z a)).comp tensorZeroFirst := by
  have h := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M)
    (cross_projection_factorization u v z a)
  simpa [tensorChange, tensorZeroFirst, LinearMap.rTensor_comp] using h

theorem tensor_quotientCoordinates_multiplyFirst (u v z : R) :
    (tensorChange (M := M) (quotientCoordinates u v z)).comp tensorMultiplyFirst =
      (tensorMultiplyLinear ![u,v,z]).comp
        (tensorChange (quotientCoordinates u v z)) := by
  have h : (linearChange (quotientCoordinates u v z)).toLinearMap.comp multiplyFirst =
      (LinearMap.mulLeft R (linearForm ![u,v,z])).comp
        (linearChange (quotientCoordinates u v z)).toLinearMap := by
    apply LinearMap.ext
    intro P
    change linearChange (quotientCoordinates u v z) ((X (0 : Fin 3) : Aux R) * P) =
      linearForm ![u,v,z] * linearChange (quotientCoordinates u v z) P
    rw [map_mul, linearChange_X]
    rfl
  have ht := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M) h
  simpa [tensorChange, tensorMultiplyFirst, tensorMultiplyLinear,
    LinearMap.rTensor_comp] using ht

theorem tensorZeroFirst_eq_binaryProjection (P : AuxTensor (R := R) (M := M)) :
    tensorZeroFirst P = tensorBinaryEmbedding (tensorBinaryRestriction P) := by
  have h := LinearMap.rTensor_comp M binaryEmbedding.toLinearMap
    (binaryRestriction.toLinearMap : Aux R →ₗ[R] Binary R)
  exact LinearMap.congr_fun h P

theorem tensorDivideFirst_homogeneous {n : ℕ}
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous (n + 1) P) :
    TensorHomogeneous n (tensorDivideFirst P) := by
  have h : (homogeneousComponent n).comp (divideFirst : Aux R →ₗ[R] Aux R) =
      divideFirst.comp (homogeneousComponent (n + 1)) := by
    apply LinearMap.ext
    intro Q
    exact divideFirst_homogeneousComponent n Q
  have ht := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M) h
  simp only [LinearMap.rTensor_comp] at ht
  have htP := LinearMap.congr_fun ht P
  dsimp only [TensorHomogeneous, tensorDivideFirst, LinearMap.comp_apply] at hP ⊢
  simpa only [LinearMap.comp_apply, hP] using htP

theorem tensorChange_homogeneous (A : Matrix (Fin 3) (Fin 3) R) {n : ℕ}
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous n P) :
    TensorHomogeneous n (tensorChange A P) := by
  exact tensor_linearSubstitution_homogeneous (linearChange A) (by intro i; simp) hP

/-- On a chart on which `u` is a unit, the cross-product kernel is exactly
the auxiliary linear-form multiples.  This remains true for every module. -/
theorem tensor_cross_kernel (u v z a : R) (hua : u * a = 1)
    (P : AuxTensor (R := R) (M := M)) :
    tensorChange (crossMatrix u v z) P = 0 ↔
      P ∈ LinearMap.range (tensorMultiplyLinear ![u,v,z]) := by
  obtain ⟨hDD', hD'D⟩ := quotientCoordinates_inverse u v z a hua
  obtain ⟨hHH', hH'H⟩ := crossKernelCoordinates_inverse u v z a hua
  let ED := (linearChangeEquiv (quotientCoordinates u v z)
    (quotientCoordinatesInv v z a) hDD' hD'D).toLinearEquiv.rTensor M
  let EH := (linearChangeEquiv (crossKernelCoordinates u v z a)
    (crossKernelCoordinatesInv u v z a) hHH' hH'H).toLinearEquiv.rTensor M
  have hcross : ∀ Q, tensorChange (crossMatrix u v z) (ED Q) = EH (tensorZeroFirst Q) :=
    fun Q => LinearMap.congr_fun (tensor_cross_projection_factorization u v z a) Q
  have hmul : ∀ Q, ED (tensorMultiplyFirst Q) = tensorMultiplyLinear ![u,v,z] (ED Q) :=
    fun Q => LinearMap.congr_fun (tensor_quotientCoordinates_multiplyFirst u v z) Q
  constructor
  · intro hP
    have hz : tensorZeroFirst (ED.symm P) = 0 := by
      apply EH.injective
      rw [← hcross, ED.apply_symm_apply, hP, map_zero]
    obtain ⟨Q, hQ⟩ := (tensor_zeroFirst_kernel (ED.symm P)).mp hz
    refine ⟨ED Q, ?_⟩
    rw [← hmul, hQ, ED.apply_symm_apply]
  · rintro ⟨Q, rfl⟩
    have heq : tensorMultiplyLinear ![u,v,z] Q =
        ED (tensorMultiplyFirst (ED.symm Q)) := by
      rw [hmul, ED.apply_symm_apply]
    rw [heq, hcross, tensor_zeroFirst_multiplyFirst, map_zero]

/-- Multiplication by the auxiliary linear form is injective when one
coefficient is a unit; the proof tensors an explicit polynomial division. -/
theorem tensorMultiplyLinear_injective (u v z a : R) (hua : u * a = 1) :
    Function.Injective (tensorMultiplyLinear (M := M) ![u,v,z]) := by
  obtain ⟨hDD', hD'D⟩ := quotientCoordinates_inverse u v z a hua
  let ED := (linearChangeEquiv (quotientCoordinates u v z)
    (quotientCoordinatesInv v z a) hDD' hD'D).toLinearEquiv.rTensor M
  have hmul : ∀ Q, ED (tensorMultiplyFirst Q) = tensorMultiplyLinear ![u,v,z] (ED Q) :=
    fun Q => LinearMap.congr_fun (tensor_quotientCoordinates_multiplyFirst u v z) Q
  intro P Q h
  apply ED.symm.injective
  apply tensor_multiplyFirst_injective
  apply ED.injective
  rw [hmul, hmul, ED.apply_symm_apply, ED.apply_symm_apply]
  exact h

/-- Data for an explicit unit-chart presentation of the cross quotient. -/
structure CrossPresentation (u v z : R) where
  quotient : Matrix (Fin 3) (Fin 3) R
  quotientInv : Matrix (Fin 3) (Fin 3) R
  kernel : Matrix (Fin 3) (Fin 3) R
  kernelInv : Matrix (Fin 3) (Fin 3) R
  quotient_mul_inv : quotient * quotientInv = 1
  quotient_inv_mul : quotientInv * quotient = 1
  kernel_mul_inv : kernel * kernelInv = 1
  kernel_inv_mul : kernelInv * kernel = 1
  quotient_first : quotient 0 = ![u,v,z]
  kernel_derivative : ∀ i : Fin 3, ∑ j, (![u,v,z] : Fin 3 → R) j *
    kernel i j = if i = 0 then 1 else 0
  projection_factorization :
    ((linearChange (crossMatrix u v z)).toLinearMap).comp
      (linearChange quotient).toLinearMap =
    ((linearChange kernel).toLinearMap).comp zeroFirst

def crossPresentationU (u v z a : R) (hua : u * a = 1) :
    CrossPresentation u v z where
  quotient := quotientCoordinates u v z
  quotientInv := quotientCoordinatesInv v z a
  kernel := crossKernelCoordinates u v z a
  kernelInv := crossKernelCoordinatesInv u v z a
  quotient_mul_inv := (quotientCoordinates_inverse u v z a hua).1
  quotient_inv_mul := (quotientCoordinates_inverse u v z a hua).2
  kernel_mul_inv := (crossKernelCoordinates_inverse u v z a hua).1
  kernel_inv_mul := (crossKernelCoordinates_inverse u v z a hua).2
  quotient_first := rfl
  kernel_derivative := crossKernelCoordinates_derivative u v z a hua
  projection_factorization := cross_projection_factorization u v z a

def crossPresentationV (u v z a : R) (hva : v * a = 1) :
    CrossPresentation u v z where
  quotient := quotientCoordinatesV u v z
  quotientInv := quotientCoordinatesVInv u z a
  kernel := crossKernelCoordinatesV u v z a
  kernelInv := crossKernelCoordinatesVInv u v z a
  quotient_mul_inv := (quotientCoordinatesV_inverse u v z a hva).1
  quotient_inv_mul := (quotientCoordinatesV_inverse u v z a hva).2
  kernel_mul_inv := (crossKernelCoordinatesV_inverse u v z a hva).1
  kernel_inv_mul := (crossKernelCoordinatesV_inverse u v z a hva).2
  quotient_first := rfl
  kernel_derivative := crossKernelCoordinatesV_derivative u v z a hva
  projection_factorization := cross_projection_factorizationV u v z a

namespace CrossPresentation

variable {u v z : R} (T : CrossPresentation u v z)
include T

/-- Quotient coordinates on a unit chart, also for module coefficients. -/
def quotientEquiv : AuxTensor (R := R) (M := M) ≃ₗ[R] AuxTensor (R := R) (M := M) :=
  (linearChangeEquiv T.quotient T.quotientInv
    T.quotient_mul_inv T.quotient_inv_mul).toLinearEquiv.rTensor M

/-- Directional kernel coordinates on a unit chart. -/
def kernelEquiv : AuxTensor (R := R) (M := M) ≃ₗ[R] AuxTensor (R := R) (M := M) :=
  (linearChangeEquiv T.kernel T.kernelInv
    T.kernel_mul_inv T.kernel_inv_mul).toLinearEquiv.rTensor M

theorem cross_projection (P : AuxTensor (R := R) (M := M)) :
    tensorChange (crossMatrix u v z) (T.quotientEquiv P) =
      T.kernelEquiv (tensorZeroFirst P) := by
  have h := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M)
    T.projection_factorization
  simp only [LinearMap.rTensor_comp] at h
  exact LinearMap.congr_fun h P

theorem quotient_multiplyFirst (P : AuxTensor (R := R) (M := M)) :
    T.quotientEquiv (tensorMultiplyFirst P) =
      tensorMultiplyLinear ![u,v,z] (T.quotientEquiv P) := by
  have h : (linearChange T.quotient).toLinearMap.comp multiplyFirst =
      (LinearMap.mulLeft R (linearForm ![u,v,z])).comp
        (linearChange T.quotient).toLinearMap := by
    apply LinearMap.ext
    intro Q
    change linearChange T.quotient ((X (0 : Fin 3) : Aux R) * Q) =
      linearForm ![u,v,z] * linearChange T.quotient Q
    rw [map_mul, linearChange_X, T.quotient_first]
  have ht := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M) h
  simp only [LinearMap.rTensor_comp] at ht
  exact LinearMap.congr_fun ht P

theorem quotient_homogeneous {n : ℕ} {P : AuxTensor (R := R) (M := M)}
    (hP : TensorHomogeneous n P) : TensorHomogeneous n (T.quotientEquiv P) :=
  tensorChange_homogeneous T.quotient hP

theorem quotient_symm_homogeneous {n : ℕ} {P : AuxTensor (R := R) (M := M)}
    (hP : TensorHomogeneous n P) : TensorHomogeneous n (T.quotientEquiv.symm P) :=
  tensorChange_homogeneous T.quotientInv hP

theorem cross_kernel (P : AuxTensor (R := R) (M := M)) :
    tensorChange (crossMatrix u v z) P = 0 ↔
      P ∈ LinearMap.range (tensorMultiplyLinear ![u,v,z]) := by
  constructor
  · intro hP
    have hz : tensorZeroFirst (T.quotientEquiv.symm P) = 0 := by
      apply T.kernelEquiv.injective
      rw [← T.cross_projection, T.quotientEquiv.apply_symm_apply, hP, map_zero]
    obtain ⟨Q, hQ⟩ := (tensor_zeroFirst_kernel (T.quotientEquiv.symm P)).mp hz
    refine ⟨T.quotientEquiv Q, ?_⟩
    rw [← T.quotient_multiplyFirst, hQ, T.quotientEquiv.apply_symm_apply]
  · rintro ⟨Q, rfl⟩
    have heq : tensorMultiplyLinear ![u,v,z] Q =
        T.quotientEquiv (tensorMultiplyFirst (T.quotientEquiv.symm Q)) := by
      rw [T.quotient_multiplyFirst, T.quotientEquiv.apply_symm_apply]
    rw [heq, T.cross_projection, tensor_zeroFirst_multiplyFirst, map_zero]

/-- The local exact sequence respects the auxiliary degree. -/
theorem cross_kernel_homogeneous {n : ℕ}
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous (n + 1) P)
    (hcross : tensorChange (crossMatrix u v z) P = 0) :
    ∃ Q, TensorHomogeneous n Q ∧ tensorMultiplyLinear ![u,v,z] Q = P := by
  have hz : tensorZeroFirst (T.quotientEquiv.symm P) = 0 := by
    apply T.kernelEquiv.injective
    rw [← T.cross_projection, T.quotientEquiv.apply_symm_apply, hcross, map_zero]
  refine ⟨T.quotientEquiv (tensorDivideFirst (T.quotientEquiv.symm P)),
    T.quotient_homogeneous (tensorDivideFirst_homogeneous
      (T.quotient_symm_homogeneous hP)), ?_⟩
  rw [← T.quotient_multiplyFirst]
  have hsplit := tensor_first_variable_split (T.quotientEquiv.symm P)
  rw [hz, add_zero] at hsplit
  rw [hsplit, T.quotientEquiv.apply_symm_apply]

theorem multiply_injective :
    Function.Injective (tensorMultiplyLinear (M := M) ![u,v,z]) := by
  intro P Q h
  apply T.quotientEquiv.symm.injective
  apply tensor_multiplyFirst_injective
  apply T.quotientEquiv.injective
  rw [T.quotient_multiplyFirst, T.quotient_multiplyFirst,
    T.quotientEquiv.apply_symm_apply, T.quotientEquiv.apply_symm_apply]
  exact h

section CharacteristicZero
variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
include K

/-- Every homogeneous directional kernel element has a homogeneous cross
representative on either unit chart. -/
theorem cross_range_homogeneous {n : ℕ}
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous n P)
    (hdP : tensorDirectional ![u,v,z] P = 0) :
    ∃ Q, TensorHomogeneous n Q ∧ tensorChange (crossMatrix u v z) Q = P := by
  obtain ⟨Q, hQ, huniq⟩ := tensor_directional_homogeneous_kernel
    (K := K) (M := M) ![u,v,z] T.kernel T.kernelInv
    T.kernel_mul_inv T.kernel_inv_mul T.kernel_derivative P hP |>.mp hdP
  refine ⟨T.quotientEquiv (tensorBinaryEmbedding Q),
    T.quotient_homogeneous (tensor_linearSubstitution_homogeneous binaryEmbedding
      binaryEmbedding_X_homogeneous hQ.1), ?_⟩
  rw [T.cross_projection, tensorZeroFirst_eq_binaryProjection,
    tensorBinaryRestriction_embedding]
  exact hQ.2

end CharacteristicZero
end CrossPresentation

section CharacteristicZero
variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
include K

/-- The cross-product quotient is the directional-derivative kernel on a
unit chart.  Together with `tensor_cross_kernel` this is the local exact
sequence used in the two-chart coefficient proof. -/
theorem tensor_cross_range (u v z a : R) (hua : u * a = 1)
    (P : AuxTensor (R := R) (M := M)) :
    P ∈ LinearMap.range (tensorChange (crossMatrix u v z)) ↔
      tensorDirectional ![u,v,z] P = 0 := by
  obtain ⟨hDD', hD'D⟩ := quotientCoordinates_inverse u v z a hua
  obtain ⟨hHH', hH'H⟩ := crossKernelCoordinates_inverse u v z a hua
  let ED := (linearChangeEquiv (quotientCoordinates u v z)
    (quotientCoordinatesInv v z a) hDD' hD'D).toLinearEquiv.rTensor M
  have hcross : ∀ Q, tensorChange (crossMatrix u v z) (ED Q) =
      tensorChange (crossKernelCoordinates u v z a) (tensorZeroFirst Q) :=
    fun Q => LinearMap.congr_fun (tensor_cross_projection_factorization u v z a) Q
  have hker := tensor_directional_kernel (K := K) (M := M) ![u,v,z]
    (crossKernelCoordinates u v z a) (crossKernelCoordinatesInv u v z a)
    hHH' hH'H (crossKernelCoordinates_derivative u v z a hua)
  constructor
  · rintro ⟨Q, rfl⟩
    apply (hker _).mpr
    refine ⟨tensorBinaryRestriction (ED.symm Q), ?_, ?_⟩
    · change tensorChange (crossKernelCoordinates u v z a)
          (tensorBinaryEmbedding (tensorBinaryRestriction (ED.symm Q))) = _
      rw [← tensorZeroFirst_eq_binaryProjection, ← hcross, ED.apply_symm_apply]
    · intro Q' hQ'
      have hHinj : Function.Injective
          (tensorChange (crossKernelCoordinates u v z a) (M := M)) :=
        ((linearChangeEquiv (crossKernelCoordinates u v z a)
          (crossKernelCoordinatesInv u v z a) hHH' hH'H).toLinearEquiv.rTensor M).injective
      apply tensorBinaryEmbedding_injective
      apply hHinj
      change kernelEmbedding (crossKernelCoordinates u v z a) Q' = _
      rw [hQ']
      rw [← ED.apply_symm_apply Q, hcross, tensorZeroFirst_eq_binaryProjection]
      simp only [ED.symm_apply_apply]
  · intro hP
    obtain ⟨Q, hQ, huniq⟩ := (hker P).mp hP
    refine ⟨ED (tensorBinaryEmbedding Q), ?_⟩
    rw [hcross, tensorZeroFirst_eq_binaryProjection, tensorBinaryRestriction_embedding]
    exact hQ

end CharacteristicZero

end Tensor

end

end FiniteCech

end ChoppedPlane
