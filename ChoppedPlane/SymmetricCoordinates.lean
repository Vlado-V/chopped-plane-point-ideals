module

public import ChoppedPlane.SymmetricDerivative
public import Mathlib.LinearAlgebra.DirectSum.Finsupp

@[expose] public section

/-!
# Coefficients of module-valued symmetric powers

The tensor description of the directional kernel has unique, finite module
coefficients. In auxiliary degree `n` these are indexed by the `n + 1` binary
monomials. No freeness assumption on the coefficient module is required.
-/

noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {σ : Type*}

/-- Coefficient identification for module-valued multivariate polynomials. -/
def tensorCoefficients : (MvPolynomial σ R ⊗[R] M) ≃ₗ[R] ((σ →₀ ℕ) →₀ M) := by
  classical
  exact (basisMonomials σ R).repr.rTensor M ≪≫ₗ
    TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ)

@[simp] theorem tensorCoefficients_tmul (P : MvPolynomial σ R) (m : M) (s : σ →₀ ℕ) :
    tensorCoefficients (P ⊗ₜ[R] m) s = P.coeff s • m := by
  classical
  change TensorProduct.finsuppScalarLeft R M (σ →₀ ℕ)
    ((basisMonomials σ R).repr P ⊗ₜ[R] m) s = _
  rw [TensorProduct.finsuppScalarLeft_apply_tmul_apply]
  rfl

@[simp] theorem tensorCoefficients_monomial (s : σ →₀ ℕ) (m : M) :
    tensorCoefficients ((monomial s 1 : MvPolynomial σ R) ⊗ₜ[R] m) =
      Finsupp.single s m := by
  classical
  ext t
  simp [coeff_monomial, Finsupp.single_apply, ite_smul]

@[simp] theorem tensorCoefficients_symm_single (s : σ →₀ ℕ) (m : M) :
    tensorCoefficients.symm (Finsupp.single s m) =
      (monomial s 1 : MvPolynomial σ R) ⊗ₜ[R] m := by
  apply tensorCoefficients.injective
  simp

/-- Finite tensor sums are read coefficientwise. -/
@[simp] theorem tensorCoefficients_sum {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ R ⊗[R] M) (α : σ →₀ ℕ) :
    tensorCoefficients (∑ j ∈ s, P j) α = ∑ j ∈ s, tensorCoefficients (P j) α := by
  simp only [map_sum, Finsupp.finsetSum_apply]

/-- Every module-valued polynomial is its finite sum of coefficient monomials. -/
theorem tensor_as_sum_monomials (P : MvPolynomial σ R ⊗[R] M) :
    P = (tensorCoefficients P).sum (fun s m => (monomial s 1) ⊗ₜ[R] m) := by
  have h : (tensorCoefficients P).sum (fun s m => Finsupp.single s m) =
      tensorCoefficients P := Finsupp.sum_single _
  apply_fun (tensorCoefficients (R := R) (M := M) (σ := σ)).symm at h
  simp only [Finsupp.sum, map_sum, tensorCoefficients_symm_single,
    LinearEquiv.symm_apply_apply] at h
  exact h.symm

/-- Homogeneous extraction keeps exactly the module coefficients of that degree. -/
theorem tensorCoefficients_component (n : ℕ) (P : MvPolynomial σ R ⊗[R] M)
    (s : σ →₀ ℕ) :
    tensorCoefficients ((homogeneousComponent n).rTensor M P) s =
      if s.degree = n then tensorCoefficients P s else 0 := by
  classical
  induction P using TensorProduct.inductionOn with
  | tmul P m => simp [coeff_homogeneousComponent, ite_smul]
  | add P Q hP hQ => simp [hP, hQ, ite_add_ite]

/-- Module-valued homogeneity is equivalently the expected support condition. -/
theorem tensorHomogeneous_iff_coefficients (n : ℕ) (P : MvPolynomial σ R ⊗[R] M) :
    TensorHomogeneous n P ↔ ∀ s : σ →₀ ℕ, s.degree ≠ n → tensorCoefficients P s = 0 := by
  constructor
  · intro hP s hs
    have h := congrArg (fun Q => tensorCoefficients Q s) hP
    rw [tensorCoefficients_component, ite_eq_right hs] at h
    exact h.symm
  · intro h
    apply tensorCoefficients.injective
    ext s
    rw [tensorCoefficients_component]
    split_ifs with hs
    · rfl
    · exact (h s hs).symm

/-- The exponent of the `j`th degree-`n` binary monomial. -/
def binaryExponent (n : ℕ) (j : Fin (n + 1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 j.val + Finsupp.single 1 (n - j.val)

@[simp] theorem binaryExponent_zero (n : ℕ) (j : Fin (n + 1)) :
    binaryExponent n j 0 = j.val := by simp [binaryExponent]

@[simp] theorem binaryExponent_one (n : ℕ) (j : Fin (n + 1)) :
    binaryExponent n j 1 = n - j.val := by simp [binaryExponent]

@[simp] theorem binaryExponent_degree (n : ℕ) (j : Fin (n + 1)) :
    (binaryExponent n j).degree = n := by
  simp only [binaryExponent, map_add, Finsupp.degree_single]
  omega

theorem binaryExponent_injective (n : ℕ) : Function.Injective (binaryExponent n) := by
  intro i j h
  apply Fin.ext
  simpa using congrArg (fun s : Fin 2 →₀ ℕ => s 0) h

theorem binary_degree (s : Fin 2 →₀ ℕ) : s.degree = s 0 + s 1 := by
  change s.sum (fun _ n => n) = _
  rw [Finsupp.sum_fintype]
  · simp [Fin.sum_univ_two]
  · simp

/-- Every degree-`n` binary exponent has a unique index between zero and `n`. -/
theorem exists_binaryExponent (n : ℕ) (s : Fin 2 →₀ ℕ) (hs : s.degree = n) :
    ∃ j : Fin (n + 1), binaryExponent n j = s := by
  have hsum : s 0 + s 1 = n := (binary_degree s).symm.trans hs
  refine ⟨⟨s 0, by omega⟩, ?_⟩
  ext i
  fin_cases i
  · simp
  · change binaryExponent n ⟨s 0, _⟩ (1 : Fin 2) = s 1
    rw [binaryExponent_one]
    change n - s 0 = s 1
    omega

/-- The finite coefficient vector of a degree-`n` binary module polynomial. -/
def binaryCoefficients (n : ℕ) (P : BinaryTensor (R := R) (M := M)) : Fin (n + 1) → M :=
  fun j => tensorCoefficients P (binaryExponent n j)

/-- Synthesize a binary symmetric tensor from its finite coefficient vector. -/
def binarySynthesis (n : ℕ) (c : Fin (n + 1) → M) : BinaryTensor (R := R) (M := M) :=
  ∑ j, monomial (binaryExponent n j) 1 ⊗ₜ[R] c j

@[simp] theorem binaryCoefficients_synthesis (n : ℕ) (c : Fin (n + 1) → M) :
    binaryCoefficients n (binarySynthesis (R := R) n c) = c := by
  classical
  funext j
  simp only [binaryCoefficients, binarySynthesis, map_sum, Finsupp.finsetSum_apply,
    tensorCoefficients_monomial, Finsupp.single_apply]
  simp only [(binaryExponent_injective n).eq_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

/-- The synthesized binary tensor is homogeneous of the intended degree. -/
theorem binarySynthesis_homogeneous (n : ℕ) (c : Fin (n + 1) → M) :
    TensorHomogeneous n (binarySynthesis (R := R) n c) := by
  apply (tensorHomogeneous_iff_coefficients n _).mpr
  intro s hs
  classical
  simp only [binarySynthesis, map_sum, Finsupp.finsetSum_apply,
    tensorCoefficients_monomial, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have h : binaryExponent n j ≠ s := by
    intro heq
    exact hs (heq ▸ binaryExponent_degree n j)
  simp [h]

/-- Homogeneous binary tensors are recovered from their finite coefficient vectors. -/
theorem binarySynthesis_coefficients (n : ℕ) (P : BinaryTensor (R := R) (M := M))
    (hP : TensorHomogeneous n P) :
    binarySynthesis n (binaryCoefficients n P) = P := by
  classical
  apply tensorCoefficients.injective
  ext s
  by_cases hs : s.degree = n
  · obtain ⟨j, rfl⟩ := exists_binaryExponent n s hs
    exact congrFun (binaryCoefficients_synthesis n (binaryCoefficients n P)) j
  · rw [(tensorHomogeneous_iff_coefficients n _).mp
      (binarySynthesis_homogeneous n _) s hs,
      (tensorHomogeneous_iff_coefficients n _).mp hP s hs]


/-- A directional derivative acts as the sum of its weighted coordinate derivatives. -/
theorem directional_apply (f : Fin 3 → R) (P : Aux R) :
    directional f P = ∑ i, f i • pderiv i P := by
  have hlin := congrArg Derivation.toLinearMap (directional_eq_sum f)
  rw [Derivation.coe_sum_linearMap] at hlin
  simp only [Derivation.coe_smul_linearMap] at hlin
  have h := LinearMap.congr_fun hlin P
  simpa only [LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe] using h

/-- The actual coefficient recurrence of the directional derivative. -/
theorem coeff_directional (f : Fin 3 → R) (P : Aux R) (s : Fin 3 →₀ ℕ) :
    (directional f P).coeff s =
      ∑ i, (f i * (s i + 1 : ℕ)) * P.coeff (s + Finsupp.single i 1) := by
  rw [directional_apply, coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [coeff_smul, coeff_pderiv]
  simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

/-- The same coefficient recurrence for arbitrary module-valued polynomials. -/
theorem tensorCoefficients_directional (f : Fin 3 → R)
    (P : AuxTensor (R := R) (M := M)) (s : Fin 3 →₀ ℕ) :
    tensorCoefficients (tensorDirectional f P) s =
      ∑ i, (f i * (s i + 1 : ℕ)) • tensorCoefficients P (s + Finsupp.single i 1) := by
  induction P using TensorProduct.inductionOn with
  | tmul P m =>
    simp only [tensorDirectional, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
      tensorCoefficients_tmul, coeff_directional, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_smul _ _ _
  | add P Q hP hQ =>
    simp only [map_add, Finsupp.add_apply, hP, hQ, smul_add, Finset.sum_add_distrib]

/-- The binary monomial corresponding to its finite index is the expected product of powers. -/
theorem binaryExponent_monomial (n : ℕ) (j : Fin (n + 1)) :
    (monomial (binaryExponent n j) 1 : Binary R) = X 0 ^ j.val * X 1 ^ (n - j.val) := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul_monomial, one_mul]
  rfl

/-- A degree-`n` symmetric expression in the two kernel linear forms. -/
def kernelSynthesis (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ) (c : Fin (n + 1) → M) :
    AuxTensor (R := R) (M := M) :=
  ∑ j, (linearForm (A 1) ^ j.val * linearForm (A 2) ^ (n - j.val)) ⊗ₜ[R] c j

/-- The abstract binary kernel embedding is the explicit finite symmetric expression. -/
theorem kernelEmbedding_synthesis (A : Matrix (Fin 3) (Fin 3) R)
    (n : ℕ) (c : Fin (n + 1) → M) :
    kernelEmbedding A (binarySynthesis n c) = kernelSynthesis A n c := by
  simp only [binarySynthesis, kernelSynthesis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change linearChange A (binaryEmbedding (monomial (binaryExponent n j) 1)) ⊗ₜ[R] c j = _
  rw [binaryExponent_monomial, map_mul, map_pow, map_pow]
  have hx0 : binaryEmbedding (X 0 : Binary R) = (X 1 : Aux R) := by simp [binaryEmbedding]
  have hx1 : binaryEmbedding (X 1 : Binary R) = (X 2 : Aux R) := by simp [binaryEmbedding]
  rw [hx0, hx1, map_mul, map_pow, map_pow, linearChange_X, linearChange_X]

/-- The finite symmetric coefficient vector is unique. -/
theorem kernelSynthesis_injective (A B : Matrix (Fin 3) (Fin 3) R) (hAB : A * B = 1)
    (n : ℕ) : Function.Injective (kernelSynthesis (M := M) A n) := by
  intro c c' h
  have h' := congrArg (kernelCoordinates (M := M) B) h
  rw [← kernelEmbedding_synthesis, ← kernelEmbedding_synthesis,
    kernelCoordinates_embedding A B hAB, kernelCoordinates_embedding A B hAB] at h'
  have hc := congrArg (binaryCoefficients (R := R) n) h'
  simpa using hc

variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
include K

/-- A homogeneous directional kernel has a unique vector of `n + 1` module coefficients.
These are the coefficients of the powers of its two split kernel linear forms. -/
theorem tensor_directional_finite_kernel
    (f : Fin 3 → R) (A B : Matrix (Fin 3) (Fin 3) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    {n : ℕ} (P : AuxTensor (R := R) (M := M)) (hP : TensorHomogeneous n P) :
    tensorDirectional f P = 0 ↔
      ∃! c : Fin (n + 1) → M, kernelSynthesis A n c = P := by
  constructor
  · intro hD
    obtain ⟨Q, ⟨hhom, hQ⟩, huniq⟩ :=
      (tensor_directional_homogeneous_kernel (K := K) f A B hAB hBA hA P hP).mp hD
    refine ⟨binaryCoefficients n Q, ?_, ?_⟩
    · change kernelSynthesis A n (binaryCoefficients n Q) = P
      rw [← kernelEmbedding_synthesis, binarySynthesis_coefficients n Q hhom]
      exact hQ
    · intro c hc
      exact kernelSynthesis_injective A B hAB n (hc.trans (by
        rw [← kernelEmbedding_synthesis, binarySynthesis_coefficients n Q hhom]
        exact hQ.symm))
  · rintro ⟨c, hc, huniq⟩
    apply (tensor_directional_homogeneous_kernel (K := K) f A B hAB hBA hA P hP).mpr
    refine ⟨binarySynthesis n c, ⟨binarySynthesis_homogeneous n c, ?_⟩, ?_⟩
    · rw [kernelEmbedding_synthesis]
      exact hc
    · intro Q hQ
      have hcoord := congrArg (kernelCoordinates (M := M) B) hQ.2
      rw [kernelCoordinates_embedding A B hAB] at hcoord
      rw [← hc, ← kernelEmbedding_synthesis, kernelCoordinates_embedding A B hAB] at hcoord
      exact hcoord

end ChoppedPlane.SymmetricDerivative

