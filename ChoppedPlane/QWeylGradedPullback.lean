module

public import ChoppedPlane.QWeylQuartic
public import ChoppedPlane.QWeylGrading
public import ChoppedPlane.QuarticSubstitution

@[expose] public section

/-! Actual quartic semilinear pullback, with its exact weighted degrees. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial
variable {K : Type*} [Field K]
set_option maxHeartbeats 1200000

def profileMultiplicity : CubicProfile → ℕ
  | .degreeThree => 3
  | .degreeTwo => 2
  | .degreeOne => 1

def quarticRootMultiplier : BinaryRing K := binaryU K ^ 3 - binaryV K ^ 3

theorem quarticSubstitution_cubic :
    quarticSubstitution K (binaryCubic K) =
      binaryCubic K * quarticRootMultiplier (K := K) ^ 3 := by
  simpa [binaryCubic, quarticRootMultiplier] using
    quartic_binary_cubic (binaryU K) (binaryV K)

def quarticCubicHom :
    CyclicCubicRing (BinaryRing K) (binaryCubic K) →+*
      CyclicCubicRing (BinaryRing K) (binaryCubic K) :=
  cyclicScaledBaseChangeHom (quarticSubstitution K).toRingHom
    (binaryCubic K) (binaryCubic K) quarticRootMultiplier quarticSubstitution_cubic

@[simp] theorem quarticCubicHom_root :
    quarticCubicHom (K := K) (cyclicRoot (binaryCubic K)) =
      cyclicCoefficientHom (binaryCubic K) quarticRootMultiplier * cyclicRoot (binaryCubic K) :=
  cyclicScaledBaseChangeHom_root _ _ _ _ _

@[simp] theorem quarticCubicHom_coefficient (b : BinaryRing K) :
    quarticCubicHom (K := K) (cyclicCoefficientHom (binaryCubic K) b) =
      cyclicCoefficientHom (binaryCubic K) (quarticSubstitution K b) :=
  cyclicScaledBaseChangeHom_coefficient _ _ _ _ _ b

def binaryProfilePullbackWeights (q : K) (s : CubicProfile) : Fin 3 → BinaryRing K :=
  profilePullbackWeights (binaryU K) (binaryV K) (C q) s

def binaryProfileDualPullbackWeights (q : K) (s : CubicProfile) : Fin 3 → BinaryRing K :=
  profileDualPullbackWeights (binaryU K) (binaryV K) (C q) s

def profilePullback (q : K) (s : CubicProfile) :
    BinaryVector K →ₛₗ[(quarticSubstitution K).toRingHom] BinaryVector K :=
  weightedVectorBaseChange (quarticSubstitution K).toRingHom
    (binaryProfilePullbackWeights q s)

def profileDualPullback (q : K) (s : CubicProfile) :
    BinaryVector K →ₛₗ[(quarticSubstitution K).toRingHom] BinaryVector K :=
  weightedVectorBaseChange (quarticSubstitution K).toRingHom
    (binaryProfileDualPullbackWeights q s)

theorem profileFactors_eq_cyclicCoefficients (q : K) (s : CubicProfile) :
    profileFactors q s = cyclicProfileCoefficients (binaryU K) (binaryV K) (C q) s := by
  funext i
  cases s <;> fin_cases i <;>
    simp [profileFactors, cubicLinearFactors, cyclicProfileCoefficients, map_pow]

theorem quarticSubstitution_profileFactors (q : K) (s : CubicProfile) (i : Fin 3) :
    quarticSubstitution K (profileFactors q s i) =
      cyclicProfileCoefficients (quarticU (binaryU K) (binaryV K))
        (quarticV (binaryU K) (binaryV K)) (C q) s i := by
  cases s <;> fin_cases i <;>
    simp [profileFactors, cubicLinearFactors, cyclicProfileCoefficients, map_pow]

theorem profilePullback_intertwines (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profilePullback q s (cyclicZ (profileFactors q s) m) =
      quarticRootMultiplier (K := K) • cyclicZ (profileFactors q s) (profilePullback q s m) := by
  refine weightedVectorBaseChange_cyclicZ (quarticSubstitution K).toRingHom
    (profileFactors q s) (profileFactors q s) (binaryProfilePullbackWeights q s)
    (quarticRootMultiplier (K := K)) ?_ m
  intro i
  have hq' : (C q : BinaryRing K) ^ 2 + C q + 1 = 0 := by
    simpa using congrArg (C : K →+* BinaryRing K) hq
  change quarticSubstitution K (profileFactors q s i) *
    binaryProfilePullbackWeights q s (cyclicNext i) = _
  rw [quarticSubstitution_profileFactors, profileFactors_eq_cyclicCoefficients]
  simpa only [binaryProfilePullbackWeights, quarticRootMultiplier] using
    profilePullbackWeights_intertwine (binaryU K) (binaryV K) (C q) hq' s i

theorem profileDualPullback_intertwines (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profileDualPullback q s (cyclicZDual (profileFactors q s) m) =
      quarticRootMultiplier (K := K) • cyclicZDual (profileFactors q s) (profileDualPullback q s m) := by
  refine weightedVectorBaseChange_cyclicZDual (quarticSubstitution K).toRingHom
    (profileFactors q s) (profileFactors q s) (binaryProfileDualPullbackWeights q s)
    (quarticRootMultiplier (K := K)) ?_ m
  intro i
  have hq' : (C q : BinaryRing K) ^ 2 + C q + 1 = 0 := by
    simpa using congrArg (C : K →+* BinaryRing K) hq
  change quarticSubstitution K (profileFactors q s i) *
    binaryProfileDualPullbackWeights q s i = _
  rw [quarticSubstitution_profileFactors, profileFactors_eq_cyclicCoefficients]
  simpa only [binaryProfileDualPullbackWeights, quarticRootMultiplier] using
    profileDualPullbackWeights_intertwine (binaryU K) (binaryV K) (C q) hq' s i

def profileModulePullback (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s)
    BinaryVector K →ₛₗ[quarticCubicHom (K := K)] BinaryVector K :=
  cyclicModuleScaledBaseChange (quarticSubstitution K).toRingHom
    (binaryCubic K) (binaryCubic K) quarticRootMultiplier quarticSubstitution_cubic
    (profilePullback q s) (cyclicZ (profileFactors q s)) (cyclicZ (profileFactors q s))
    (profileZ_cube q hq s) (profileZ_cube q hq s) (profilePullback_intertwines q hq s)

def profileDualModulePullback (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s)
    BinaryVector K →ₛₗ[quarticCubicHom (K := K)] BinaryVector K :=
  cyclicModuleScaledBaseChange (quarticSubstitution K).toRingHom
    (binaryCubic K) (binaryCubic K) quarticRootMultiplier quarticSubstitution_cubic
    (profileDualPullback q s) (cyclicZDual (profileFactors q s)) (cyclicZDual (profileFactors q s))
    (profileZDual_cube q hq s) (profileZDual_cube q hq s) (profileDualPullback_intertwines q hq s)

@[simp] theorem profileModulePullback_apply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profileModulePullback q hq s m = profilePullback q s m := rfl

@[simp] theorem profileDualModulePullback_apply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profileDualModulePullback q hq s m = profileDualPullback q s m := rfl

theorem binaryLinearDifference_ne_zero (q : K) :
    binaryU K - C q * binaryV K ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval ![(1 : K), 0]) h
  simp [binaryU, binaryV] at he

theorem binaryProfilePullbackWeights_ne_zero (q : K) (s : CubicProfile) (i : Fin 3) :
    binaryProfilePullbackWeights q s i ≠ 0 := by
  have h0 := binaryLinearDifference_ne_zero (K := K) 1
  have h1 := binaryLinearDifference_ne_zero (K := K) q
  have h2 := binaryLinearDifference_ne_zero (K := K) (q ^ 2)
  simp only [map_one, one_mul] at h0
  rw [map_pow] at h2
  cases s <;> fin_cases i <;>
    simp [binaryProfilePullbackWeights, profilePullbackWeights, weightZero, weightOne,
      weightTwo, h0, h1, h2]

theorem binaryProfileDualPullbackWeights_ne_zero (q : K) (s : CubicProfile) (i : Fin 3) :
    binaryProfileDualPullbackWeights q s i ≠ 0 := by
  have h0 := binaryLinearDifference_ne_zero (K := K) 1
  have h1 := binaryLinearDifference_ne_zero (K := K) q
  have h2 := binaryLinearDifference_ne_zero (K := K) (q ^ 2)
  simp only [map_one, one_mul] at h0
  rw [map_pow] at h2
  cases s <;> fin_cases i <;>
    simp [binaryProfileDualPullbackWeights, profileDualPullbackWeights, h0, h1, h2]

theorem profilePullback_injective [CharZero K] (q : K) (s : CubicProfile) :
    Function.Injective (profilePullback q s) :=
  weightedVectorBaseChange_injective _ quarticSubstitution_injective _
    (binaryProfilePullbackWeights_ne_zero q s)

theorem profileDualPullback_injective [CharZero K] (q : K) (s : CubicProfile) :
    Function.Injective (profileDualPullback q s) :=
  weightedVectorBaseChange_injective _ quarticSubstitution_injective _
    (binaryProfileDualPullbackWeights_ne_zero q s)

def pullbackWeightDegrees (s : CubicProfile) (i : Fin 3) : ℕ :=
  profileMultiplicity s + 3 * generatorWeights s i

def dualPullbackWeightDegrees (s : CubicProfile) (i : Fin 3) : ℕ :=
  3 * dualGeneratorWeights s i - profileMultiplicity s

theorem binaryLinearDifference_homogeneous (q : K) :
    (binaryU K - C q * binaryV K).IsHomogeneous 1 :=
  (isHomogeneous_X K 0).sub ((isHomogeneous_X K 1).C_mul q)

theorem binaryProfilePullbackWeights_homogeneous (q : K) (s : CubicProfile) (i : Fin 3) :
    (binaryProfilePullbackWeights q s i).IsHomogeneous (pullbackWeightDegrees s i) := by
  have h0 : (binaryU K - binaryV K).IsHomogeneous 1 :=
    (isHomogeneous_X K 0).sub (isHomogeneous_X K 1)
  have h1 := binaryLinearDifference_homogeneous (K := K) q
  have h2 := binaryLinearDifference_homogeneous (K := K) (q ^ 2)
  rw [map_pow] at h2
  cases s <;> fin_cases i
  · exact (h0.pow 2).mul h1
  · exact (h1.pow 2).mul h2
  · exact (h2.pow 2).mul h0
  · exact h0.pow 2
  · exact h1.mul h2
  · exact ((h2.pow 2).mul h0).mul (h1.pow 2)
  · exact h1
  · exact (h0.mul (h1.pow 2)).mul h2
  · exact (h0.pow 2).mul (h2.pow 2)

theorem binaryProfileDualPullbackWeights_homogeneous (q : K) (s : CubicProfile) (i : Fin 3) :
    (binaryProfileDualPullbackWeights q s i).IsHomogeneous (dualPullbackWeightDegrees s i) := by
  have h0 : (binaryU K - binaryV K).IsHomogeneous 1 :=
    (isHomogeneous_X K 0).sub (isHomogeneous_X K 1)
  have h1 := binaryLinearDifference_homogeneous (K := K) q
  have h2 := binaryLinearDifference_homogeneous (K := K) (q ^ 2)
  rw [map_pow] at h2
  cases s <;> fin_cases i
  · exact h1.mul (h2.pow 2)
  · exact h2.mul (h0.pow 2)
  · exact h0.mul (h1.pow 2)
  · exact (h1.pow 2).mul (h2.pow 2)
  · exact (h1.mul h2).mul (h0.pow 2)
  · exact h0
  · exact ((h0.pow 2).mul h1).mul (h2.pow 2)
  · exact h0.mul h2
  · exact h1.pow 2

/-- Signed components, including negative degrees, pull back to four times
their original degree. -/
theorem quarticSubstitution_mem_signedForms {t : ℤ} {p : BinaryRing K}
    (hp : p ∈ signedForms K 2 t) :
    quarticSubstitution K p ∈ signedForms K 2 (4 * t) := by
  by_cases ht : 0 ≤ t
  · have h4 : 0 ≤ 4 * t := by omega
    have hf : p.IsHomogeneous t.toNat := by simpa [signedForms, ht] using hp
    have hnat : (4 * t).toNat = 4 * t.toNat := by omega
    simpa [signedForms, h4, hnat] using quarticSubstitution_homogeneous hf
  · have hp0 : p = 0 := by simpa [signedForms, ht] using hp
    simp [hp0]

/-- The quartic coefficient map with fixed component multipliers is linear
for the original coefficient field. -/
def weightedQuarticLinear (ρ : Fin 3 → BinaryRing K) : BinaryVector K →ₗ[K] BinaryVector K :=
  LinearMap.pi fun i => (LinearMap.mulRight K (ρ i)).comp
    ((quarticSubstitution K).toLinearMap.comp (LinearMap.proj i))

@[simp] theorem weightedQuarticLinear_apply (ρ : Fin 3 → BinaryRing K)
    (m : BinaryVector K) (i : Fin 3) :
    weightedQuarticLinear ρ m i = quarticSubstitution K (m i) * ρ i := rfl

/-- The actual forward pullback has weighted degree `4*t+s`. -/
def gradedProfilePullback (q : K) (s : CubicProfile) (t : ℤ) :
    GradedBinaryVector (K := K) (generatorWeights s) t →ₗ[K]
      GradedBinaryVector (K := K) (generatorWeights s) (4 * t + profileMultiplicity s) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp (weightedQuarticLinear (binaryProfilePullbackWeights q s))).comp
      (gradedBinaryVectorVal (generatorWeights s) t)).codRestrict
      (signedForms K 2 (4*t+profileMultiplicity s-generatorWeights s i)) (fun m => by
        change quarticSubstitution K (m i).val * binaryProfilePullbackWeights q s i ∈ _
        have hm := quarticSubstitution_mem_signedForms (m i).property
        have h := homogeneous_mul_mem_signedForms
          (binaryProfilePullbackWeights_homogeneous q s i) hm
        have he : 4 * (t - (generatorWeights s i : ℤ)) + (pullbackWeightDegrees s i : ℤ) =
            4 * t + profileMultiplicity s - generatorWeights s i := by
          simp only [pullbackWeightDegrees, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [he] at h
        simpa only [mul_comm] using h)

/-- The actual dual pullback has weighted degree `4*t-s`. -/
def gradedProfileDualPullback (q : K) (s : CubicProfile) (t : ℤ) :
    GradedBinaryVector (K := K) (dualGeneratorWeights s) t →ₗ[K]
      GradedBinaryVector (K := K) (dualGeneratorWeights s) (4 * t - profileMultiplicity s) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp (weightedQuarticLinear (binaryProfileDualPullbackWeights q s))).comp
      (gradedBinaryVectorVal (dualGeneratorWeights s) t)).codRestrict
      (signedForms K 2 (4*t-profileMultiplicity s-dualGeneratorWeights s i)) (fun m => by
        change quarticSubstitution K (m i).val * binaryProfileDualPullbackWeights q s i ∈ _
        have hm := quarticSubstitution_mem_signedForms (m i).property
        have h := homogeneous_mul_mem_signedForms
          (binaryProfileDualPullbackWeights_homogeneous q s i) hm
        have hd : (dualPullbackWeightDegrees s i : ℤ) =
            3 * (dualGeneratorWeights s i : ℤ) - profileMultiplicity s := by
          cases s <;> fin_cases i <;>
            norm_num [dualPullbackWeightDegrees, dualGeneratorWeights,
              generatorWeights, profileMultiplicity]
        have he : 4 * (t - (dualGeneratorWeights s i : ℤ)) +
            (dualPullbackWeightDegrees s i : ℤ) =
            4 * t - profileMultiplicity s - dualGeneratorWeights s i := by rw [hd]; ring
        rw [he] at h
        simpa only [mul_comm] using h)

@[simp] theorem gradedProfilePullback_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (generatorWeights s) t) :
    gradedBinaryVectorVal (generatorWeights s) (4*t+profileMultiplicity s)
      (gradedProfilePullback q s t m) =
    profilePullback q s (gradedBinaryVectorVal (generatorWeights s) t m) := rfl

@[simp] theorem gradedProfileDualPullback_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t) :
    gradedBinaryVectorVal (dualGeneratorWeights s) (4*t-profileMultiplicity s)
      (gradedProfileDualPullback q s t m) =
    profileDualPullback q s (gradedBinaryVectorVal (dualGeneratorWeights s) t m) := rfl

theorem gradedProfilePullback_injective [CharZero K] (q : K) (s : CubicProfile) (t : ℤ) :
    Function.Injective (gradedProfilePullback (K := K) q s t) := by
  intro m n h
  apply gradedBinaryVectorVal_injective (generatorWeights s) t
  apply profilePullback_injective q s
  simpa using congrArg (gradedBinaryVectorVal (K := K) (generatorWeights s)
    (4*t+profileMultiplicity s)) h

theorem gradedProfileDualPullback_injective [CharZero K] (q : K) (s : CubicProfile) (t : ℤ) :
    Function.Injective (gradedProfileDualPullback (K := K) q s t) := by
  intro m n h
  apply gradedBinaryVectorVal_injective (dualGeneratorWeights s) t
  apply profileDualPullback_injective q s
  simpa using congrArg (gradedBinaryVectorVal (K := K) (dualGeneratorWeights s)
    (4*t-profileMultiplicity s)) h

end ChoppedPlane.QWeyl
