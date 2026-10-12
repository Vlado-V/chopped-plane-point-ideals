module

public import ChoppedPlane.ProfileDirectionalKernel

@[expose] public section

/-! The actual cubic tensor zero-kernel theorem gives injectivity of each
concrete finite coefficient differential. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K] [CharZero K]

theorem profileDifferential_injective (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (t : ℕ)
    (ht : ∀ k : Fin 3, 4*r+profileMultiplicity s <
      2 * ((t+1 : ℕ) : ℤ) + (generatorWeights s k : ℤ)) :
    Function.Injective (operatorDifferential (gradedProfileOperators q s r) t) := by
  letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
    (profileZ_cube q hq s)
  apply operatorDifferential_injective_of_tensor_kernel
    (gradedBinaryVectorVal (generatorWeights s) r)
    (gradedBinaryVectorVal (generatorWeights s) (r+1))
    (profileDirection (K := K)) (gradedProfileOperators q s r)
    (gradedProfileOperators_direction q hq s r) t
  intro c hδ
  have hzero := profile_directional_kernel_zero q hq s (t+1) r ht
    (finiteDirectionalSynthesis (gradedBinaryVectorVal (generatorWeights s) r) (t+1) c)
    (finiteDirectionalSynthesis_homogeneous _ _ _)
    (finiteDirectionalSynthesis_weighted (generatorWeights s) r (t+1) c) hδ
  apply finiteDirectionalSynthesis_injective
    (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
    (gradedBinaryVectorVal (generatorWeights s) r)
    (gradedBinaryVectorVal_injective (generatorWeights s) r) (t+1)
  simpa using hzero

theorem profileDualDifferential_injective (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (t : ℕ)
    (ht : ∀ k : Fin 3, 4*r-profileMultiplicity s <
      2 * ((t+1 : ℕ) : ℤ) + (dualGeneratorWeights s k : ℤ)) :
    Function.Injective (operatorDifferential (gradedProfileDualOperators q s r) t) := by
  letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
    (profileZDual_cube q hq s)
  apply operatorDifferential_injective_of_tensor_kernel
    (gradedBinaryVectorVal (dualGeneratorWeights s) r)
    (gradedBinaryVectorVal (dualGeneratorWeights s) (r+1))
    (profileDirection (K := K)) (gradedProfileDualOperators q s r)
    (gradedProfileDualOperators_direction q hq s r) t
  intro c hδ
  have hzero := profileDual_directional_kernel_zero q hq s (t+1) r ht
    (finiteDirectionalSynthesis (gradedBinaryVectorVal (dualGeneratorWeights s) r) (t+1) c)
    (finiteDirectionalSynthesis_homogeneous _ _ _)
    (finiteDirectionalSynthesis_weighted (dualGeneratorWeights s) r (t+1) c) hδ
  apply finiteDirectionalSynthesis_injective
    (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
    (gradedBinaryVectorVal (dualGeneratorWeights s) r)
    (gradedBinaryVectorVal_injective (dualGeneratorWeights s) r) (t+1)
  simpa using hzero

end ChoppedPlane.QWeyl
