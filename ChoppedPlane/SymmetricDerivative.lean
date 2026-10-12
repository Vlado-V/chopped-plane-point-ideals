module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.TensorProduct.Map
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Tactic

@[expose] public section

/-!
# Symmetric powers of a split directional derivative kernel

An invertible linear change of auxiliary variables sends a unimodular directional
partial derivative to one coordinate derivative. Its kernel is the binary
polynomial module, including after tensoring with an arbitrary coefficient module.
The integration identity is explicit, so no flatness assumption is involved.
-/

noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct

variable {R : Type*} [CommRing R]
abbrev Aux (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R
abbrev Binary (R : Type*) [CommRing R] := MvPolynomial (Fin 2) R

/-- The linear auxiliary polynomial with coefficient vector `v`. -/
def linearForm (v : Fin 3 → R) : Aux R := ∑ i, C (v i) * X i

/-- Substitution by the rows of a matrix. -/
def linearChange (A : Matrix (Fin 3) (Fin 3) R) : Aux R →ₐ[R] Aux R :=
  aeval (fun i => linearForm (A i))

@[simp] theorem linearChange_X (A : Matrix (Fin 3) (Fin 3) R) (i : Fin 3) :
    linearChange A (X i) = linearForm (A i) := by simp [linearChange]

@[simp] theorem linearChange_C (A : Matrix (Fin 3) (Fin 3) R) (r : R) :
    linearChange A (C r) = C r := by simp [linearChange]

@[simp] theorem linearForm_one_row (i : Fin 3) :
    linearForm ((1 : Matrix (Fin 3) (Fin 3) R) i) = X i := by
  classical
  simp [linearForm, Matrix.one_apply]

theorem linearChange_linearForm (A : Matrix (Fin 3) (Fin 3) R) (v : Fin 3 → R) :
    linearChange A (linearForm v) = linearForm (fun k => ∑ j, v j * A j k) := by
  classical
  simp only [linearForm, map_sum, map_mul, linearChange_C, linearChange_X,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext k
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem linearChange_comp (A B : Matrix (Fin 3) (Fin 3) R) :
    (linearChange A).comp (linearChange B) = linearChange (B * A) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, linearChange_X, linearChange_linearForm]
  rfl

@[simp] theorem linearChange_one :
    linearChange (1 : Matrix (Fin 3) (Fin 3) R) = AlgHom.id R (Aux R) := by
  ext i
  simp

/-- An invertible linear auxiliary coordinate transformation. -/
def linearChangeEquiv (A B : Matrix (Fin 3) (Fin 3) R)
    (hAB : A * B = 1) (hBA : B * A = 1) : Aux R ≃ₐ[R] Aux R :=
  AlgEquiv.ofAlgHom (linearChange A) (linearChange B)
    (by rw [linearChange_comp, hBA, linearChange_one])
    (by rw [linearChange_comp, hAB, linearChange_one])

/-- Directional differentiation with coefficient vector `f`. -/
def directional (f : Fin 3 → R) : Derivation R (Aux R) (Aux R) :=
  mkDerivation R (fun i => C (f i))

@[simp] theorem directional_X (f : Fin 3 → R) (i : Fin 3) :
    directional f (X i) = C (f i) := by simp [directional]

@[simp] theorem directional_C (f : Fin 3 → R) (r : R) :
    directional f (C r) = 0 := by simp

theorem directional_eq_sum (f : Fin 3 → R) :
    directional f = ∑ i, f i • pderiv i := by
  classical
  apply derivation_ext
  intro j
  simp [directional, Pi.single_apply]
  exact C_eq_smul_one


@[simp] theorem directional_linearForm (f v : Fin 3 → R) :
    directional f (linearForm v) = C (∑ i, f i * v i) := by
  calc
    directional f (linearForm v) = ∑ i, C (v i) * C (f i) := by
      simp [linearForm, Derivation.leibniz, smul_eq_mul]
    _ = C (∑ i, f i * v i) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← map_mul, mul_comm]

/-- Chain rule in coordinates whose first row is a lift and other rows lie in the kernel. -/
theorem directional_linearChange (f : Fin 3 → R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (P : Aux R) :
    directional f (linearChange A P) = linearChange A (pderiv 0 P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, Derivation.leibniz, linearChange_X, directional_linearForm,
      hA, pderiv_X, Pi.single_apply, map_add, smul_eq_mul, hP]
    split_ifs <;> simp [mul_comm]

/-- Set the first variable to zero and retain the two remaining variables. -/
def binaryRestriction : Aux R →ₐ[R] Binary R :=
  aeval (Fin.cases 0 X)

/-- Include the two binary auxiliary variables as the last two ternary variables. -/
def binaryEmbedding : Binary R →ₐ[R] Aux R := rename Fin.succ

@[simp] theorem binaryRestriction_embedding (P : Binary R) :
    binaryRestriction (binaryEmbedding P) = P := by
  have h : binaryRestriction.comp binaryEmbedding = AlgHom.id R (Binary R) := by
    ext i
    simp [binaryRestriction, binaryEmbedding]
  exact congrArg (fun h : Binary R →ₐ[R] Binary R => h P) h

/-- The projection onto polynomials independent of the first variable. -/
def zeroFirst : Aux R →ₗ[R] Aux R :=
  binaryEmbedding.toLinearMap.comp binaryRestriction.toLinearMap

@[simp] theorem zeroFirst_monomial (s : Fin 3 →₀ ℕ) (r : R) :
    zeroFirst (monomial s r) = if s 0 = 0 then monomial s r else 0 := by
  classical
  have hcomp : binaryEmbedding.comp binaryRestriction =
      (aeval (fun i : Fin 3 => if i = 0 then 0 else X i) : Aux R →ₐ[R] Aux R) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [binaryEmbedding, binaryRestriction]
    · simp only [AlgHom.comp_apply, binaryRestriction, aeval_X]
      change rename Fin.succ (X (0 : Fin 2) : Binary R) = X (1 : Fin 3)
      simp
    · simp only [AlgHom.comp_apply, binaryRestriction, aeval_X]
      change rename Fin.succ (X (1 : Fin 2) : Binary R) = X (2 : Fin 3)
      simp
  change (binaryEmbedding.comp binaryRestriction) (monomial s r) = _
  rw [hcomp]
  rw [aeval_def, eval₂_monomial, Finsupp.prod_fintype]
  swap
  · simp
  change C r * (∏ i : Fin 3, (if i = 0 then 0 else X i) ^ s i) = _
  by_cases hs : s 0 = 0
  · rw [ite_eq_left hs, MvPolynomial.monomial_eq, Finsupp.prod_fintype]
    swap
    · simp
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      simp [hs]
    · simp [hi0]
  · rw [ite_eq_right hs]
    have hz : (∏ i : Fin 3, (if i = 0 then 0 else (X i : Aux R)) ^ s i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 3))
      simp [zero_pow hs]
    rw [hz, mul_zero]

section Integration
variable {K : Type*} [Field K] [CharZero K] [Algebra K R]

/-- Formal integration in the first variable, with zero constant term. -/
def integrateFirst : Aux R →ₗ[R] Aux R :=
  (basisMonomials (Fin 3) R).constr R (fun s =>
    algebraMap K R (((s 0 + 1 : ℕ) : K)⁻¹) • monomial (s + Finsupp.single 0 1) 1)

omit [CharZero K] in
@[simp] theorem integrateFirst_monomial (s : Fin 3 →₀ ℕ) (r : R) :
    integrateFirst (K := K) (monomial s r) =
      monomial (s + Finsupp.single 0 1)
        (r * algebraMap K R (((s 0 + 1 : ℕ) : K)⁻¹)) := by
  have hb := (basisMonomials (Fin 3) R).constr_basis R
    (fun t => algebraMap K R (((t 0 + 1 : ℕ) : K)⁻¹) •
      (monomial (t + Finsupp.single 0 1) 1 : Aux R)) s
  change integrateFirst (K := K) (monomial s 1) = _ at hb
  have hr : monomial s r = r • (monomial s 1 : Aux R) := by simp [smul_monomial]
  rw [hr, map_smul, hb, smul_smul, smul_monomial]
  simp

/-- Integration splits the derivative: the only missing term is the binary projection. -/
theorem integrateFirst_pderiv_add_zeroFirst (P : Aux R) :
    integrateFirst (K := K) (pderiv 0 P) + zeroFirst P = P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add]
    rw [add_add_add_comm, hP, hQ]
  | monomial s r =>
    rw [pderiv_monomial, integrateFirst_monomial, zeroFirst_monomial]
    by_cases hs : s 0 = 0
    · simp [hs]
    · rw [ite_eq_right hs, add_zero]
      have hle : Finsupp.single (0 : Fin 3) 1 ≤ s :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hs)
      have hexp : s - Finsupp.single 0 1 + Finsupp.single 0 1 = s :=
        tsub_add_cancel_of_le hle
      have hn : (s - Finsupp.single (0 : Fin 3) 1 : Fin 3 →₀ ℕ) 0 + 1 = s 0 := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      rw [hexp, hn]
      congr 1
      have hcast : (s 0 : K) ≠ 0 := Nat.cast_ne_zero.mpr hs
      calc
        (r * (s 0 : R)) * algebraMap K R ((s 0 : K)⁻¹) =
            r * algebraMap K R ((s 0 : K) * (s 0 : K)⁻¹) := by
          rw [map_mul, map_natCast]
          ring
        _ = r := by rw [mul_inv_cancel₀ hcast, map_one, mul_one]

/-- The scalar splitting identity as an equality of linear maps. -/
theorem first_derivative_split :
    (integrateFirst (K := K)).comp (pderiv (R := R) (0 : Fin 3)).toLinearMap +
      zeroFirst = LinearMap.id := by
  apply LinearMap.ext
  intro P
  exact integrateFirst_pderiv_add_zeroFirst (K := K) P

end Integration

/-- The embedded binary polynomials have zero first partial derivative. -/
@[simp] theorem pderiv_binaryEmbedding (P : Binary R) :
    pderiv (0 : Fin 3) (binaryEmbedding P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [binaryEmbedding]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    have hx : binaryEmbedding (X i : Binary R) = (X i.succ : Aux R) := by simp [binaryEmbedding]
    rw [map_mul, pderiv_mul, hP, hx, zero_mul, zero_add,
      pderiv_X_of_ne (Fin.succ_ne_zero i), mul_zero]

section Tensor
variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Auxiliary polynomials with arbitrary module coefficients. -/
abbrev AuxTensor := Aux R ⊗[R] M
/-- Binary auxiliary polynomials with arbitrary module coefficients. -/
abbrev BinaryTensor := Binary R ⊗[R] M

/-- A directional partial derivative on module-valued auxiliary polynomials. -/
def tensorDirectional (f : Fin 3 → R) : AuxTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  (directional f).toLinearMap.rTensor M

def tensorBinaryEmbedding : BinaryTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  binaryEmbedding.toLinearMap.rTensor M

def tensorBinaryRestriction : AuxTensor (R := R) (M := M) →ₗ[R] BinaryTensor (R := R) (M := M) :=
  binaryRestriction.toLinearMap.rTensor M

@[simp] theorem tensorBinaryRestriction_embedding (P : BinaryTensor (R := R) (M := M)) :
    tensorBinaryRestriction (tensorBinaryEmbedding P) = P := by
  have h : tensorBinaryRestriction.comp tensorBinaryEmbedding =
      (LinearMap.id : BinaryTensor (R := R) (M := M) →ₗ[R] BinaryTensor (R := R) (M := M)) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro m
    simp [tensorBinaryRestriction, tensorBinaryEmbedding]
  exact LinearMap.congr_fun h P

theorem tensorBinaryEmbedding_injective :
    Function.Injective (tensorBinaryEmbedding (R := R) (M := M)) := by
  intro P Q h
  simpa using congrArg (tensorBinaryRestriction (R := R) (M := M)) h

/-- Tensoring the explicit integration splitting requires no flatness assumption. -/
theorem tensor_first_derivative_split (P : AuxTensor (R := R) (M := M)) :
    (integrateFirst (K := K)).rTensor M ((pderiv (R := R) (0 : Fin 3)).toLinearMap.rTensor M P) +
      tensorBinaryEmbedding (tensorBinaryRestriction P) = P := by
  have h := congrArg (fun L : Aux R →ₗ[R] Aux R => L.rTensor M)
    (first_derivative_split (K := K) (R := R))
  simp only [LinearMap.rTensor_add, LinearMap.rTensor_comp, LinearMap.rTensor_id] at h
  have hP := LinearMap.congr_fun h P
  simpa [zeroFirst, tensorBinaryEmbedding, tensorBinaryRestriction,
    LinearMap.rTensor_comp] using hP

include K

/-- The kernel of the first derivative is exactly the binary module, with unique coordinates. -/
theorem tensor_pderiv_kernel (P : AuxTensor (R := R) (M := M)) :
    (pderiv (R := R) (0 : Fin 3)).toLinearMap.rTensor M P = 0 ↔
      ∃! Q : BinaryTensor (R := R) (M := M), tensorBinaryEmbedding Q = P := by
  have hz : ((pderiv (R := R) (0 : Fin 3)).toLinearMap.rTensor M).comp
      tensorBinaryEmbedding = 0 := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro Q
    apply LinearMap.ext
    intro m
    simp [tensorBinaryEmbedding]
  constructor
  · intro hP
    have hsplit := tensor_first_derivative_split (K := K) P
    rw [hP, map_zero, zero_add] at hsplit
    exact ⟨tensorBinaryRestriction P, hsplit, fun Q hQ =>
      tensorBinaryEmbedding_injective (hQ.trans hsplit.symm)⟩
  · rintro ⟨Q, rfl, hQ⟩
    exact LinearMap.congr_fun hz Q

/-- The binary kernel embedding after an invertible coordinate transformation. -/
def kernelEmbedding (A : Matrix (Fin 3) (Fin 3) R) :
    BinaryTensor (R := R) (M := M) →ₗ[R] AuxTensor (R := R) (M := M) :=
  ((linearChange A).toLinearMap.rTensor M).comp tensorBinaryEmbedding

/-- The directional kernel is the symmetric algebra on the two kernel coordinates.
The first row of `A` is a unimodular lift, the last two rows are the kernel basis. -/
theorem tensor_directional_kernel
    (f : Fin 3 → R) (A B : Matrix (Fin 3) (Fin 3) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    (P : AuxTensor (R := R) (M := M)) :
    tensorDirectional f P = 0 ↔
      ∃! Q : BinaryTensor (R := R) (M := M), kernelEmbedding A Q = P := by
  let E := (linearChangeEquiv A B hAB hBA).toLinearEquiv.rTensor M
  have hchain : (tensorDirectional f).comp E.toLinearMap =
      E.toLinearMap.comp ((pderiv (R := R) (0 : Fin 3)).toLinearMap.rTensor M) := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro Q
    apply LinearMap.ext
    intro m
    change directional f (linearChange A Q) ⊗ₜ[R] m =
      linearChange A (pderiv 0 Q) ⊗ₜ[R] m
    rw [directional_linearChange f A hA]
  have hemb : ∀ Q, kernelEmbedding A Q = E (tensorBinaryEmbedding Q) := by
    intro Q
    rfl
  have hker : tensorDirectional f P = 0 ↔
      (pderiv (R := R) (0 : Fin 3)).toLinearMap.rTensor M (E.symm P) = 0 := by
    have hc := LinearMap.congr_fun hchain (E.symm P)
    simp only [LinearMap.comp_apply] at hc
    change tensorDirectional f (E (E.symm P)) =
      E ((pderiv (R := R) (0 : Fin 3)).toLinearMap.rTensor M (E.symm P)) at hc
    rw [E.apply_symm_apply] at hc
    rw [hc]
    exact E.map_eq_zero_iff
  rw [hker, tensor_pderiv_kernel (K := K)]
  constructor
  · rintro ⟨Q, hQ, huniq⟩
    dsimp only at hQ huniq ⊢
    refine ⟨Q, ?_, ?_⟩
    · change kernelEmbedding A Q = P
      rw [hemb, hQ, E.apply_symm_apply]
    · intro Q' hQ'
      apply huniq
      apply E.injective
      rw [← hemb, hQ', E.apply_symm_apply]
  · rintro ⟨Q, hQ, huniq⟩
    dsimp only at hQ huniq ⊢
    refine ⟨Q, ?_, ?_⟩
    · apply E.injective
      rw [← hemb, hQ, E.apply_symm_apply]
    · intro Q' hQ'
      apply huniq
      rw [hemb, hQ', E.apply_symm_apply]

end Tensor

section Homogeneous
variable {σ τ : Type*}

/-- Any substitution by linear forms preserves homogeneous degree. -/
theorem linearSubstitution_homogeneous
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    {n : ℕ} {P : MvPolynomial σ R} (hP : P.IsHomogeneous n) :
    (φ P).IsHomogeneous n := by
  rw [aeval_unique φ]
  simpa only [one_mul] using hP.aeval (φ ∘ X) hφ

/-- Linear substitution commutes with extraction of every homogeneous component. -/
theorem linearSubstitution_homogeneousComponent
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    (n : ℕ) (P : MvPolynomial σ R) :
    homogeneousComponent n (φ P) = φ (homogeneousComponent n P) := by
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | monomial s r =>
    have hp : (monomial s r : MvPolynomial σ R).IsHomogeneous s.degree :=
      isHomogeneous_monomial r rfl
    rw [homogeneousComponent_of_mem (linearSubstitution_homogeneous φ hφ hp),
      homogeneousComponent_of_mem hp]
    split_ifs <;> simp

@[simp] theorem linearForm_homogeneous (v : Fin 3 → R) :
    (linearForm v).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ (fun _i _ => isHomogeneous_C_mul_X _ _)

@[simp] theorem linearChange_homogeneous (A : Matrix (Fin 3) (Fin 3) R)
    {n : ℕ} {P : Aux R} (hP : P.IsHomogeneous n) :
    (linearChange A P).IsHomogeneous n :=
  linearSubstitution_homogeneous (linearChange A) (by intro i; simp) hP

theorem binaryRestriction_X_homogeneous (i : Fin 3) :
    (binaryRestriction (R := R) (X i)).IsHomogeneous 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [binaryRestriction] using (isHomogeneous_zero (σ := Fin 2) R 1)
  · simpa [binaryRestriction] using (isHomogeneous_X R j)

theorem binaryEmbedding_X_homogeneous (i : Fin 2) :
    (binaryEmbedding (R := R) (X i)).IsHomogeneous 1 := by
  simpa [binaryEmbedding] using (isHomogeneous_X R i.succ)

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Homogeneous module-valued polynomials, expressed by the homogeneous projector. -/
def TensorHomogeneous (n : ℕ) (P : MvPolynomial σ R ⊗[R] M) : Prop :=
  (homogeneousComponent n).rTensor M P = P

/-- Linear auxiliary substitutions also preserve homogeneous degree for module coefficients. -/
theorem tensor_linearSubstitution_homogeneous
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ i, (φ (X i)).IsHomogeneous 1)
    {n : ℕ} {P : MvPolynomial σ R ⊗[R] M} (hP : TensorHomogeneous n P) :
    TensorHomogeneous n (φ.toLinearMap.rTensor M P) := by
  have hc : (homogeneousComponent n).comp φ.toLinearMap =
      φ.toLinearMap.comp (homogeneousComponent n) := by
    apply LinearMap.ext
    intro Q
    exact linearSubstitution_homogeneousComponent φ hφ n Q
  have ht := congrArg (fun L : MvPolynomial σ R →ₗ[R] MvPolynomial τ R => L.rTensor M) hc
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp] at ht
  have htP := LinearMap.congr_fun ht P
  dsimp only [TensorHomogeneous, LinearMap.comp_apply] at hP ⊢
  simpa only [LinearMap.comp_apply, hP] using htP

/-- Read the binary coordinates using the inverse matrix. -/
def kernelCoordinates (B : Matrix (Fin 3) (Fin 3) R) :
    AuxTensor (R := R) (M := M) →ₗ[R] BinaryTensor (R := R) (M := M) :=
  tensorBinaryRestriction.comp ((linearChange B).toLinearMap.rTensor M)

/-- The coordinates are unique because this map is a left inverse to the kernel embedding. -/
theorem kernelCoordinates_embedding (A B : Matrix (Fin 3) (Fin 3) R)
    (hAB : A * B = 1) (Q : BinaryTensor (R := R) (M := M)) :
    kernelCoordinates B (kernelEmbedding A Q) = Q := by
  have hs : (kernelCoordinates (M := M) B).comp (kernelEmbedding A) = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro P
    apply LinearMap.ext
    intro m
    change binaryRestriction (linearChange B (linearChange A (binaryEmbedding P))) ⊗ₜ[R] m =
      P ⊗ₜ[R] m
    have hab : linearChange B (linearChange A (binaryEmbedding P)) = binaryEmbedding P := by
      have h := congrArg (fun L : Aux R →ₐ[R] Aux R => L (binaryEmbedding P))
        (linearChange_comp B A)
      simpa only [AlgHom.comp_apply, hAB, linearChange_one, AlgHom.id_apply] using h
    rw [hab, binaryRestriction_embedding]
  exact LinearMap.congr_fun hs Q

/-- The inverse-coordinate map preserves auxiliary homogeneous degree. -/
theorem kernelCoordinates_homogeneous (B : Matrix (Fin 3) (Fin 3) R)
    {n : ℕ} {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous n P) :
    TensorHomogeneous n (kernelCoordinates B P) := by
  exact tensor_linearSubstitution_homogeneous binaryRestriction
    binaryRestriction_X_homogeneous
    (tensor_linearSubstitution_homogeneous (linearChange B) (by intro i; simp) hP)

variable {K : Type*} [Field K] [CharZero K] [Algebra K R]
include K

/-- In each homogeneous degree the directional kernel is the symmetric power of
its two split kernel coordinates, with unique module-valued binary coefficients. -/
theorem tensor_directional_homogeneous_kernel
    (f : Fin 3 → R) (A B : Matrix (Fin 3) (Fin 3) R)
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hA : ∀ i, ∑ j, f j * A i j = if i = 0 then 1 else 0)
    {n : ℕ} (P : AuxTensor (R := R) (M := M)) (hP : TensorHomogeneous n P) :
    tensorDirectional f P = 0 ↔
      ∃! Q : BinaryTensor (R := R) (M := M),
        TensorHomogeneous n Q ∧ kernelEmbedding A Q = P := by
  constructor
  · intro hD
    obtain ⟨Q, hQ, huniq⟩ := (tensor_directional_kernel (K := K) f A B hAB hBA hA P).mp hD
    dsimp only at hQ huniq
    have hcoord : kernelCoordinates B P = Q := by
      rw [← hQ]
      exact kernelCoordinates_embedding A B hAB Q
    refine ⟨Q, ⟨?_, hQ⟩, ?_⟩
    · rw [← hcoord]
      exact kernelCoordinates_homogeneous B hP
    · intro Q' hQ'
      exact huniq Q' hQ'.2
  · rintro ⟨Q, hQ, huniq⟩
    apply (tensor_directional_kernel (K := K) f A B hAB hBA hA P).mpr
    refine ⟨Q, hQ.2, ?_⟩
    intro Q' hQ'
    have hcoord : kernelCoordinates B P = Q' := by
      rw [← hQ']
      exact kernelCoordinates_embedding A B hAB Q'
    have hhom : TensorHomogeneous n Q' := by
      rw [← hcoord]
      exact kernelCoordinates_homogeneous B hP
    exact huniq Q' ⟨hhom, hQ'⟩

end Homogeneous

end ChoppedPlane.SymmetricDerivative
