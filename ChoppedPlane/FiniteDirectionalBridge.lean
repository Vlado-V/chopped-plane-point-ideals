module

public import ChoppedPlane.PolynomialOperatorDuality
public import ChoppedPlane.HomogeneousTensorCoordinates

@[expose] public section

/-! The finite coefficient differential and the actual cubic tensor
directional derivative agree coefficient by coefficient. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
open SymmetricDerivative
variable {K : Type*} [Field K]
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module K M]
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Finite graded coefficients are synthesized as genuine auxiliary
polynomials with coefficients in the cubic module. -/
def finiteDirectionalSynthesis (ν : V →ₗ[K] M) (n : ℕ)
    (c : Sym (Fin 3) n → V) : AuxTensor (R := R) (M := M) :=
  homogeneousTensorSynthesis n (fun s => ν (c s))

theorem finiteDirectionalSynthesis_homogeneous (ν : V →ₗ[K] M) (n : ℕ)
    (c : Sym (Fin 3) n → V) :
    TensorHomogeneous n (finiteDirectionalSynthesis (R := R) ν n c) :=
  homogeneousTensorSynthesis_homogeneous n _

@[simp] theorem finiteDirectionalSynthesis_coefficient (ν : V →ₗ[K] M) (n : ℕ)
    (c : Sym (Fin 3) n → V) (s : Sym (Fin 3) n) :
    tensorCoefficients (finiteDirectionalSynthesis (R := R) ν n c)
      (homogeneousTensorExponent n s) = ν (c s) :=
  congrFun (homogeneousTensorCoefficientVector_synthesis n (fun s => ν (c s))) s

theorem finiteDirectionalSynthesis_injective (ν : V →ₗ[K] M)
    (hν : Function.Injective ν) (n : ℕ) :
    Function.Injective (finiteDirectionalSynthesis (R := R) ν n) := by
  intro c d h
  funext s
  apply hν
  simpa using congrArg (fun P => tensorCoefficients P (homogeneousTensorExponent n s)) h

@[simp] theorem finiteDirectionalSynthesis_zero (ν : V →ₗ[K] M) (n : ℕ) :
    finiteDirectionalSynthesis (R := R) ν n 0 = 0 := by
  simp [finiteDirectionalSynthesis, homogeneousTensorSynthesis]

/-- A directional derivative lowers actual auxiliary degree by one. -/
theorem tensorDirectional_homogeneous_succ (f : Fin 3 → R) (t : ℕ)
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous (t+1) P) :
    TensorHomogeneous t (tensorDirectional f P) := by
  apply (tensorHomogeneous_iff_coefficients t _).mpr
  intro s hs
  rw [tensorCoefficients_directional]
  apply Finset.sum_eq_zero
  intro i _
  have hraise : (s + Finsupp.single i 1).degree ≠ t+1 := by
    simp only [map_add, Finsupp.degree_single]
    omega
  rw [(tensorHomogeneous_iff_coefficients (t+1) P).mp hP _ hraise, smul_zero]

/-- The concrete finite differential has precisely the coefficients of the
actual tensor derivative. Only natural scalar actions occur in this identity. -/
theorem finiteDirectionalSynthesis_derivative_coefficient
    (ν : V →ₗ[K] M) (μ : W →ₗ[K] M) (f : Fin 3 → R)
    (T : Fin 3 → V →ₗ[K] W) (hT : ∀ i v, μ (T i v) = f i • ν v)
    (t : ℕ) (c : Sym (Fin 3) (t+1) → V) (s : Sym (Fin 3) t) :
    tensorCoefficients (tensorDirectional f (finiteDirectionalSynthesis (R := R) ν (t+1) c))
      (homogeneousTensorExponent t s) = μ (operatorDifferential T t c s) := by
  rw [tensorCoefficients_directional, operatorDifferential_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← operatorRaisedIndex_exponent, finiteDirectionalSynthesis_coefficient,
    map_smul, hT]
  rw [mul_comm, mul_smul]
  simp only [Nat.cast_smul_eq_nsmul]

/-- Synthesis intertwines the actual finite map and the actual tensor map. -/
theorem finiteDirectionalSynthesis_derivative
    (ν : V →ₗ[K] M) (μ : W →ₗ[K] M) (f : Fin 3 → R)
    (T : Fin 3 → V →ₗ[K] W) (hT : ∀ i v, μ (T i v) = f i • ν v)
    (t : ℕ) (c : Sym (Fin 3) (t+1) → V) :
    tensorDirectional f (finiteDirectionalSynthesis (R := R) ν (t+1) c) =
      finiteDirectionalSynthesis (R := R) μ t (operatorDifferential T t c) := by
  apply tensorCoefficients.injective
  ext e
  by_cases he : e.degree = t
  · obtain ⟨s,rfl⟩ := exists_homogeneousTensorExponent t e he
    rw [finiteDirectionalSynthesis_coefficient]
    exact finiteDirectionalSynthesis_derivative_coefficient ν μ f T hT t c s
  · rw [(tensorHomogeneous_iff_coefficients t _).mp
      (tensorDirectional_homogeneous_succ f t (finiteDirectionalSynthesis_homogeneous ν (t+1) c)) e he,
      (tensorHomogeneous_iff_coefficients t _).mp
        (finiteDirectionalSynthesis_homogeneous μ t _) e he]

theorem finiteDirectionalSynthesis_derivative_eq_zero_iff
    (ν : V →ₗ[K] M) (μ : W →ₗ[K] M) (hμ : Function.Injective μ) (f : Fin 3 → R)
    (T : Fin 3 → V →ₗ[K] W) (hT : ∀ i v, μ (T i v) = f i • ν v)
    (t : ℕ) (c : Sym (Fin 3) (t+1) → V) :
    tensorDirectional f (finiteDirectionalSynthesis (R := R) ν (t+1) c) = 0 ↔
      operatorDifferential T t c = 0 := by
  rw [finiteDirectionalSynthesis_derivative ν μ f T hT t c]
  constructor
  · intro h
    apply finiteDirectionalSynthesis_injective (R := R) μ hμ t
    simpa using h
  · intro h
    simp [h]

/-- A proved zero-kernel statement for genuine synthesized tensor
polynomials gives injectivity of the concrete finite differential. -/
theorem operatorDifferential_injective_of_tensor_kernel
    (ν : V →ₗ[K] M) (μ : W →ₗ[K] M) (f : Fin 3 → R)
    (T : Fin 3 → V →ₗ[K] W) (hT : ∀ i v, μ (T i v) = f i • ν v)
    (t : ℕ)
    (hkernel : ∀ c : Sym (Fin 3) (t+1) → V,
      tensorDirectional f (finiteDirectionalSynthesis (R := R) ν (t+1) c) = 0 → c = 0) :
    Function.Injective (operatorDifferential T t) := by
  intro c d h
  have hd : operatorDifferential T t (c-d) = 0 := by rw [map_sub, h, sub_self]
  have hzero : tensorDirectional f (finiteDirectionalSynthesis (R := R) ν (t+1) (c-d)) = 0 := by
    rw [finiteDirectionalSynthesis_derivative ν μ f T hT t, hd]
    simp
  exact sub_eq_zero.mp (hkernel (c-d) hzero)

end ChoppedPlane
