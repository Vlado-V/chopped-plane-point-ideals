module

public import ChoppedPlane.ProfileOperators
public import ChoppedPlane.QWeylGradedPullback
public import ChoppedPlane.FiniteDirectionalBridge
public import ChoppedPlane.SymmetricBaseChange
public import ChoppedPlane.CyclicScalarTower

@[expose] public section

/-! The finite profile operators are the genuine cubic-ring directional
derivative on synthesized module-valued homogeneous polynomials. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K]

def profileDirection : Fin 3 → CyclicCubicRing (BinaryRing K) (binaryCubic K) :=
  ![cyclicCoefficientHom (binaryCubic K) (binaryU K),
    cyclicCoefficientHom (binaryCubic K) (binaryV K), cyclicRoot (binaryCubic K)]

theorem finiteDirectionalSynthesis_weighted
    {R : Type*} [CommRing R] [Module R (BinaryVector K)]
    (w : Fin 3 → ℕ) (r : ℤ) (n : ℕ)
    (c : Sym (Fin 3) n → GradedBinaryVector (K := K) w r)
    (α : Fin 3 →₀ ℕ) (i : Fin 3) :
    tensorCoefficients (finiteDirectionalSynthesis (R := R)
      (gradedBinaryVectorVal w r) n c) α i ∈ signedForms K 2 (r-w i) := by
  by_cases hα : α.degree = n
  · obtain ⟨b,rfl⟩ := exists_homogeneousTensorExponent n α hα
    rw [finiteDirectionalSynthesis_coefficient]
    exact (c b i).property
  · rw [(tensorHomogeneous_iff_coefficients n _).mp
      (finiteDirectionalSynthesis_homogeneous (R := R) (gradedBinaryVectorVal w r) n c) α hα]
    exact (signedForms K 2 (r-w i)).zero_mem

theorem gradedProfileOperators_direction (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (t : ℤ) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s)
    ∀ (i : Fin 3) (m : GradedBinaryVector (K := K) (generatorWeights s) t),
      gradedBinaryVectorVal (generatorWeights s) (t+1) (gradedProfileOperators q s t i m) =
        profileDirection (K := K) i • gradedBinaryVectorVal (generatorWeights s) t m := by
  letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
    (profileZ_cube q hq s)
  intro i m
  fin_cases i
  · change binaryU K • gradedBinaryVectorVal (generatorWeights s) t m =
      cyclicCoefficientHom (binaryCubic K) (binaryU K) • gradedBinaryVectorVal (generatorWeights s) t m
    exact (cyclicModule_coefficient_smul (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s) (binaryU K) _).symm
  · change binaryV K • gradedBinaryVectorVal (generatorWeights s) t m =
      cyclicCoefficientHom (binaryCubic K) (binaryV K) • gradedBinaryVectorVal (generatorWeights s) t m
    exact (cyclicModule_coefficient_smul (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s) (binaryV K) _).symm
  · change cyclicZ (profileFactors q s) (gradedBinaryVectorVal (generatorWeights s) t m) =
      cyclicRoot (binaryCubic K) • gradedBinaryVectorVal (generatorWeights s) t m
    exact (cyclicModule_root_smul (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s) _).symm

theorem gradedProfileDualOperators_direction (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (t : ℤ) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s)
    ∀ (i : Fin 3) (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t),
      gradedBinaryVectorVal (dualGeneratorWeights s) (t+1) (gradedProfileDualOperators q s t i m) =
        profileDirection (K := K) i • gradedBinaryVectorVal (dualGeneratorWeights s) t m := by
  letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
    (profileZDual_cube q hq s)
  intro i m
  fin_cases i
  · change binaryU K • gradedBinaryVectorVal (dualGeneratorWeights s) t m =
      cyclicCoefficientHom (binaryCubic K) (binaryU K) • gradedBinaryVectorVal (dualGeneratorWeights s) t m
    exact (cyclicModule_coefficient_smul (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s) (binaryU K) _).symm
  · change binaryV K • gradedBinaryVectorVal (dualGeneratorWeights s) t m =
      cyclicCoefficientHom (binaryCubic K) (binaryV K) • gradedBinaryVectorVal (dualGeneratorWeights s) t m
    exact (cyclicModule_coefficient_smul (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s) (binaryV K) _).symm
  · change cyclicZDual (profileFactors q s) (gradedBinaryVectorVal (dualGeneratorWeights s) t m) =
      cyclicRoot (binaryCubic K) • gradedBinaryVectorVal (dualGeneratorWeights s) t m
    exact (cyclicModule_root_smul (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s) _).symm

theorem profileDifferential_tensor_eq (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (t : ℕ) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s)
    ∀ c : Sym (Fin 3) (t+1) → GradedBinaryVector (K := K) (generatorWeights s) r,
      tensorDirectional (profileDirection (K := K))
        (finiteDirectionalSynthesis (gradedBinaryVectorVal (generatorWeights s) r) (t+1) c) =
      finiteDirectionalSynthesis (gradedBinaryVectorVal (generatorWeights s) (r+1)) t
        (operatorDifferential (gradedProfileOperators q s r) t c) := by
  letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
    (profileZ_cube q hq s)
  intro c
  exact finiteDirectionalSynthesis_derivative _ _ _ _
    (gradedProfileOperators_direction q hq s r) t c

theorem profileDualDifferential_tensor_eq (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (t : ℕ) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s)
    ∀ c : Sym (Fin 3) (t+1) → GradedBinaryVector (K := K) (dualGeneratorWeights s) r,
      tensorDirectional (profileDirection (K := K))
        (finiteDirectionalSynthesis (gradedBinaryVectorVal (dualGeneratorWeights s) r) (t+1) c) =
      finiteDirectionalSynthesis (gradedBinaryVectorVal (dualGeneratorWeights s) (r+1)) t
        (operatorDifferential (gradedProfileDualOperators q s r) t c) := by
  letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
    (profileZDual_cube q hq s)
  intro c
  exact finiteDirectionalSynthesis_derivative _ _ _ _
    (gradedProfileDualOperators_direction q hq s r) t c

end ChoppedPlane.QWeyl
