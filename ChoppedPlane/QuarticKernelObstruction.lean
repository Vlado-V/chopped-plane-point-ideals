module

public import ChoppedPlane.QWeylModule
public import ChoppedPlane.SymmetricCoordinates
public import ChoppedPlane.ShiftedDegreeObstruction

@[expose] public section

/-! The signed degree obstruction applied coefficientwise to the actual
module-valued symmetric kernel expression. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
open scoped TensorProduct
variable {K : Type*} [Field K]
variable (F : BinaryRing K) (Z : End (BinaryRing K) (BinaryVector K))
  (hZ : Z ^ 3 = F • 1)
local notation "Cubic" => CyclicCubicRing (BinaryRing K) F

/-- The cubic quotient acts by binary-linear maps on the free coefficient module. -/
theorem cubic_scalar_free_expansion :
    let := cyclicModuleStructure F Z hZ
    ∀ (r : Cubic) (m : BinaryVector K) (i : Fin 3),
      (r • m) i = ∑ k : Fin 3, (r • (Pi.single k 1 : BinaryVector K)) i * m k := by
  dsimp only
  let := cyclicModuleStructure F Z hZ
  intro r m i
  classical
  let T := cyclicActionHom F Z hZ r
  have hm : m = ∑ k : Fin 3, m k • Pi.single k 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  change T m i = _
  conv_lhs => rw [hm]
  simp only [map_sum, LinearMap.map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

/-- A symmetric expression whose actual columns start at degree `2n` cannot
contain a homogeneous coefficient vector of smaller weighted degree. -/
theorem symmetric_kernel_zero_of_weighted_columns :
    let := cyclicModuleStructure F Z hZ
    ∀ (w : Fin 3 → ℕ) (t : ℤ) (n : ℕ)
    (A : Matrix (Fin 3) (Fin 3) Cubic)
    (_hcolumn : ∀ (j : Fin (n + 1)) (k : Fin 3) (α : Fin 3 →₀ ℕ) (i : Fin 3),
      tensorCoefficients
        ((linearForm (A 1) ^ j.val * linearForm (A 2) ^ (n - j.val)) ⊗ₜ[Cubic]
          (Pi.single k 1 : BinaryVector K)) α i ∈
        signedForms K 2 (2 * (n : ℤ) + (w k : ℤ) - w i))
    (_ht : ∀ k : Fin 3, t < 2 * (n : ℤ) + (w k : ℤ))
    (P : AuxTensor (R := Cubic) (M := BinaryVector K))
    (_hP : ∀ (α : Fin 3 →₀ ℕ) (i : Fin 3),
      tensorCoefficients P α i ∈ signedForms K 2 (t - w i))
    (c : Fin (n + 1) → BinaryVector K), kernelSynthesis A n c = P → P = 0 := by
  dsimp only
  let := cyclicModuleStructure F Z hZ
  intro w t n A hcolumn ht P hP c hc
  classical
  apply tensorCoefficients.injective
  rw [LinearEquiv.map_zero]
  apply Finsupp.ext
  intro α
  funext i
  let Bα : Matrix (Fin 3) (Fin (n + 1) × Fin 3) (BinaryRing K) :=
    fun i jk => tensorCoefficients
      ((linearForm (A 1) ^ jk.1.val * linearForm (A 2) ^ (n - jk.1.val)) ⊗ₜ[Cubic]
        (Pi.single jk.2 1 : BinaryVector K)) α i
  have heq : Bα.mulVec (fun jk => c jk.1 jk.2) = tensorCoefficients P α := by
    funext i
    rw [← hc]
    simp only [kernelSynthesis]
    simp only [tensorCoefficients_sum, Finset.sum_apply, tensorCoefficients_tmul]
    dsimp only [Matrix.mulVec, dotProduct, Bα]
    simp only [tensorCoefficients_tmul]
    change ∑ jk : Fin (n + 1) × Fin 3,
      _ = ∑ j : Fin (n + 1), _
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro j _
    exact (cubic_scalar_free_expansion F Z hZ
      ((linearForm (A 1) ^ j.val * linearForm (A 2) ^ (n - j.val)).coeff α) (c j) i).symm
  have hz : tensorCoefficients P α = 0 :=
    ChoppedPlane.weighted_homogeneous_vector_zero_of_lower_degree
      Bα (fun i => (w i : ℤ)) (fun jk => 2 * (n : ℤ) + (w jk.2 : ℤ)) t
      (fun i jk => hcolumn jk.1 jk.2 α i)
      (fun jk => ht jk.2)
      (tensorCoefficients P α) (hP α) (fun jk => c jk.1 jk.2) heq
  exact congrFun hz i

end ChoppedPlane.QWeyl
