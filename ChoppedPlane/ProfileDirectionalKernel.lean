module

public import ChoppedPlane.ProfileDirectional
public import ChoppedPlane.QuarticKernelZero

@[expose] public section

/-! The actual quartic pullback proves vanishing of the original cubic
directional kernels in each primal and dual weighted profile. -/

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K]
set_option maxHeartbeats 1200000

/-- The ring pullback carries the literal cubic direction to the quartic row. -/
theorem quarticCubicHom_profileDirection :
    (fun i => quarticCubicHom (K := K) (profileDirection (K := K) i)) =
      quarticRow (cyclicCoefficientHom (binaryCubic K) (binaryU K))
        (cyclicCoefficientHom (binaryCubic K) (binaryV K)) (cyclicRoot (binaryCubic K)) := by
  funext i
  fin_cases i
  · simp [profileDirection, quarticCubicHom, quarticRow, quarticU, map_ofNat]
  · simp [profileDirection, quarticCubicHom, quarticRow, quarticV, map_ofNat]
    ring
  · simp [profileDirection, quarticCubicHom, quarticRow, quarticZ, quarticRootMultiplier]
    ring

theorem weightedVector_profilePullback (q : K) (s : CubicProfile) {t : ℤ}
    {m : BinaryVector K} (hm : WeightedVector (generatorWeights s) t m) :
    WeightedVector (generatorWeights s) (4 * t + profileMultiplicity s)
      (profilePullback q s m) := by
  let m' : GradedBinaryVector (K := K) (generatorWeights s) t := fun i => ⟨m i, hm i⟩
  intro i
  exact (gradedProfilePullback q s t m' i).property

theorem weightedVector_profileDualPullback (q : K) (s : CubicProfile) {t : ℤ}
    {m : BinaryVector K} (hm : WeightedVector (dualGeneratorWeights s) t m) :
    WeightedVector (dualGeneratorWeights s) (4 * t - profileMultiplicity s)
      (profileDualPullback q s m) := by
  let m' : GradedBinaryVector (K := K) (dualGeneratorWeights s) t := fun i => ⟨m i, hm i⟩
  intro i
  exact (gradedProfileDualPullback q s t m' i).property

variable [CharZero K]

/-- The original directional kernel vanishes in the three primal profiles,
using the literal injective quartic pullback. -/
theorem profile_directional_kernel_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (t : ℤ)
    (ht : ∀ k : Fin 3, 4 * t + profileMultiplicity s <
      2 * (n : ℤ) + (generatorWeights s k : ℤ)) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s)
    ∀ (P : AuxTensor (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
        (M := BinaryVector K)), TensorHomogeneous n P →
      (∀ (α : Fin 3 →₀ ℕ) (i : Fin 3), tensorCoefficients P α i ∈
        signedForms K 2 (t - generatorWeights s i)) →
      tensorDirectional (profileDirection (K := K)) P = 0 → P = 0 := by
  let _ := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
    (profileZ_cube q hq s)
  intro P haux hweighted hδ
  let ψ := profileModulePullback q hq s
  let P' := tensorBaseChange ψ P
  have haux' : TensorHomogeneous n P' := tensorBaseChange_homogeneous ψ haux
  have hweighted' : ∀ (α : Fin 3 →₀ ℕ) (i : Fin 3), tensorCoefficients P' α i ∈
      signedForms K 2 (4 * t + profileMultiplicity s - generatorWeights s i) := by
    intro α i
    rw [tensorCoefficients_baseChange]
    exact weightedVector_profilePullback q s (hweighted α) i
  have hδ' : tensorDirectional (quarticRow
        (cyclicCoefficientHom (binaryCubic K) (binaryU K))
        (cyclicCoefficientHom (binaryCubic K) (binaryV K))
        (cyclicRoot (binaryCubic K))) P' = 0 := by
    have h := tensorBaseChange_directional ψ (profileDirection (K := K)) P
    rw [hδ, (tensorBaseChange ψ).map_zero, quarticCubicHom_profileDirection] at h
    exact h.symm
  have hzero : P' = 0 := quartic_profile_kernel_zero q hq s false n
    (4 * t + profileMultiplicity s) ht P' haux' hweighted' hδ'
  apply tensorBaseChange_injective ψ (profilePullback_injective q s)
  exact hzero.trans (tensorBaseChange ψ).map_zero.symm

/-- The original transposed directional kernel vanishes in the three dual
profiles with the exact dual pullback shift. -/
theorem profileDual_directional_kernel_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (t : ℤ)
    (ht : ∀ k : Fin 3, 4 * t - profileMultiplicity s <
      2 * (n : ℤ) + (dualGeneratorWeights s k : ℤ)) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s)
    ∀ (P : AuxTensor (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
        (M := BinaryVector K)), TensorHomogeneous n P →
      (∀ (α : Fin 3 →₀ ℕ) (i : Fin 3), tensorCoefficients P α i ∈
        signedForms K 2 (t - dualGeneratorWeights s i)) →
      tensorDirectional (profileDirection (K := K)) P = 0 → P = 0 := by
  let _ := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
    (profileZDual_cube q hq s)
  intro P haux hweighted hδ
  let ψ := profileDualModulePullback q hq s
  let P' := tensorBaseChange ψ P
  have haux' : TensorHomogeneous n P' := tensorBaseChange_homogeneous ψ haux
  have hweighted' : ∀ (α : Fin 3 →₀ ℕ) (i : Fin 3), tensorCoefficients P' α i ∈
      signedForms K 2 (4 * t - profileMultiplicity s - dualGeneratorWeights s i) := by
    intro α i
    rw [tensorCoefficients_baseChange]
    exact weightedVector_profileDualPullback q s (hweighted α) i
  have hδ' : tensorDirectional (quarticRow
        (cyclicCoefficientHom (binaryCubic K) (binaryU K))
        (cyclicCoefficientHom (binaryCubic K) (binaryV K))
        (cyclicRoot (binaryCubic K))) P' = 0 := by
    have h := tensorBaseChange_directional ψ (profileDirection (K := K)) P
    rw [hδ, (tensorBaseChange ψ).map_zero, quarticCubicHom_profileDirection] at h
    exact h.symm
  have hzero : P' = 0 := quartic_profile_kernel_zero q hq s true n
    (4 * t - profileMultiplicity s) ht P' haux' hweighted' hδ'
  apply tensorBaseChange_injective ψ (profileDualPullback_injective q s)
  exact hzero.trans (tensorBaseChange ψ).map_zero.symm

end ChoppedPlane.QWeyl
