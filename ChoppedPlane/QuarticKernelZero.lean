module

public import ChoppedPlane.QuarticKernelBinary
public import ChoppedPlane.QuarticKernelGrading
public import ChoppedPlane.QuarticKernelObstruction

@[expose] public section

/-! The actual quartic directional kernel vanishes below twice its auxiliary
homogeneous degree in every primal and dual cyclic binary profile. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K] [CharZero K]

/-- Either cyclic orientation uses its literal prescribed generator shifts. -/
def quarticProfileWeights (dual : Bool) (s : CubicProfile) : Fin 3 → ℕ :=
  if dual then dualGeneratorWeights s else generatorWeights s

/-- Polynomial descent plus the actual quadratic-column degree obstruction,
including every prescribed source shift. -/
theorem quartic_cyclic_kernel_zero
    (dual : Bool) (γ : Fin 3 → BinaryRing K)
    (hγ : γ 0 * γ 1 * γ 2 = binaryCubic K) (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (quarticCyclicZ dual γ m))
    (n : ℕ) (t : ℤ) (ht : ∀ k : Fin 3, t < 2 * (n : ℤ) + (w k : ℤ)) :
    let Z := quarticCyclicZ dual γ
    let hZ : Z ^ 3 = binaryCubic K • 1 :=
      (quarticCyclicZ_cube dual γ).trans (by rw [hγ])
    let := cyclicModuleStructure (binaryCubic K) Z hZ
    ∀ (P : AuxTensor (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
        (M := BinaryVector K)), TensorHomogeneous n P →
      (∀ (α : Fin 3 →₀ ℕ) (i : Fin 3), tensorCoefficients P α i ∈
        signedForms K 2 (t - w i)) →
      tensorDirectional (quarticRow
        (cyclicCoefficientHom (binaryCubic K) (binaryU K))
        (cyclicCoefficientHom (binaryCubic K) (binaryV K))
        (cyclicRoot (binaryCubic K))) P = 0 → P = 0 := by
  dsimp only
  let Z := quarticCyclicZ dual γ
  have hZ : Z ^ 3 = binaryCubic K • 1 :=
    (quarticCyclicZ_cube dual γ).trans (by rw [hγ])
  let := cyclicModuleStructure (binaryCubic K) Z hZ
  intro P haux hweighted hδ
  obtain ⟨c, hc⟩ := quartic_cyclic_kernel_descends dual γ hγ P haux hδ
  apply symmetric_kernel_zero_of_weighted_columns (binaryCubic K) Z hZ w t n
    (quarticKernelMatrixU
      (cyclicCoefficientHom (binaryCubic K) (binaryU K))
      (cyclicCoefficientHom (binaryCubic K) (binaryV K))
      (cyclicRoot (binaryCubic K)) 0) _ ht P hweighted c hc
  intro j k α i
  rw [tensorCoefficients_tmul]
  change (((quadraticSymmetricPolynomial (binaryCubic K) n j).coeff α •
    (Pi.single k (1 : BinaryRing K) : BinaryVector K)) : BinaryVector K) i ∈
      signedForms K 2 (2 * (n : ℤ) + (w k : ℤ) - w i)
  exact cyclic_quadraticSymmetric_coefficient_degree (binaryCubic K) Z hZ w hgraded n j α i k

/-- The six literal modules of the cubic construction satisfy the negative
critical-degree vanishing, uniformly in every auxiliary degree. -/
theorem quartic_profile_kernel_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (dual : Bool) (n : ℕ) (t : ℤ)
    (ht : ∀ k : Fin 3, t < 2 * (n : ℤ) + (quarticProfileWeights dual s k : ℤ)) :
    let Z := quarticCyclicZ dual (profileFactors q s)
    let hZ : Z ^ 3 = binaryCubic K • 1 :=
      (quarticCyclicZ_cube dual (profileFactors q s)).trans (by
        rw [profileFactors_product q hq])
    let := cyclicModuleStructure (binaryCubic K) Z hZ
    ∀ (P : AuxTensor (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
        (M := BinaryVector K)), TensorHomogeneous n P →
      (∀ (α : Fin 3 →₀ ℕ) (i : Fin 3), tensorCoefficients P α i ∈
        signedForms K 2 (t - quarticProfileWeights dual s i)) →
      tensorDirectional (quarticRow
        (cyclicCoefficientHom (binaryCubic K) (binaryU K))
        (cyclicCoefficientHom (binaryCubic K) (binaryV K))
        (cyclicRoot (binaryCubic K))) P = 0 → P = 0 := by
  dsimp only
  apply quartic_cyclic_kernel_zero dual (profileFactors q s)
    (profileFactors_product q hq s) (quarticProfileWeights dual s) _ n t ht
  intro a m hm
  cases dual
  · exact weightedVector_profileZ q s hm
  · exact weightedVector_profileZDual q s hm

end ChoppedPlane.QWeyl
