module

public import ChoppedPlane.ProfileCrossing

@[expose] public section

/-! The three actual graded coefficient operators for cubic matrix witnesses. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- Multiplication by a binary linear form on a genuinely shifted component. -/
def gradedBinaryMultiply (f : Forms K 2 1) (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t →ₗ[K]
      GradedBinaryVector (K := K) w (t+1) where
  toFun m i := ⟨f.val * (m i).val, by
    exact weighted_mul_mem_signedForms f.property (m i).property (by norm_num)⟩
  map_add' m n := by
    ext i
    simp [mul_add]
  map_smul' a m := by
    ext i
    simp

@[simp] theorem gradedBinaryMultiply_val (f : Forms K 2 1) (w : Fin 3 → ℕ)
    (t : ℤ) (m : GradedBinaryVector (K := K) w t) :
    gradedBinaryVectorVal w (t+1) (gradedBinaryMultiply f w t m) =
      f.val • gradedBinaryVectorVal w t m := rfl

/-- Multiplication by one binary coordinate on the genuine shifted pieces. -/
def gradedBinaryCoordinate (j : Fin 2) (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t →ₗ[K]
      GradedBinaryVector (K := K) w (t+1) :=
  gradedBinaryMultiply ⟨X j, isHomogeneous_X K j⟩ w t

@[simp] theorem gradedBinaryCoordinate_val (j : Fin 2) (w : Fin 3 → ℕ)
    (t : ℤ) (m : GradedBinaryVector (K := K) w t) :
    gradedBinaryVectorVal w (t+1) (gradedBinaryCoordinate j w t m) =
      (X j : BinaryRing K) • gradedBinaryVectorVal w t m := rfl

/-- The actual `u`, `v`, and forward cyclic `z` actions, in that order. -/
def gradedProfileOperators (q : K) (s : CubicProfile) (t : ℤ) :
    Fin 3 → (GradedBinaryVector (K := K) (generatorWeights s) t →ₗ[K]
      GradedBinaryVector (K := K) (generatorWeights s) (t+1)) :=
  ![gradedBinaryMultiply ⟨binaryU K, isHomogeneous_X K 0⟩ (generatorWeights s) t,
    gradedBinaryMultiply ⟨binaryV K, isHomogeneous_X K 1⟩ (generatorWeights s) t,
    gradedProfileZ q s t]

/-- The actual `u`, `v`, and transposed cyclic `z` actions on dual shifts. -/
def gradedProfileDualOperators (q : K) (s : CubicProfile) (t : ℤ) :
    Fin 3 → (GradedBinaryVector (K := K) (dualGeneratorWeights s) t →ₗ[K]
      GradedBinaryVector (K := K) (dualGeneratorWeights s) (t+1)) :=
  ![gradedBinaryMultiply ⟨binaryU K, isHomogeneous_X K 0⟩ (dualGeneratorWeights s) t,
    gradedBinaryMultiply ⟨binaryV K, isHomogeneous_X K 1⟩ (dualGeneratorWeights s) t,
    gradedProfileZDual q s t]

@[simp] theorem gradedProfileOperators_zero_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (generatorWeights s) t) :
    gradedBinaryVectorVal (generatorWeights s) (t+1) (gradedProfileOperators q s t 0 m) =
      binaryU K • gradedBinaryVectorVal (generatorWeights s) t m := rfl

@[simp] theorem gradedProfileOperators_one_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (generatorWeights s) t) :
    gradedBinaryVectorVal (generatorWeights s) (t+1) (gradedProfileOperators q s t 1 m) =
      binaryV K • gradedBinaryVectorVal (generatorWeights s) t m := rfl

@[simp] theorem gradedProfileOperators_two_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (generatorWeights s) t) :
    gradedBinaryVectorVal (generatorWeights s) (t+1) (gradedProfileOperators q s t 2 m) =
      cyclicZ (profileFactors q s) (gradedBinaryVectorVal (generatorWeights s) t m) := rfl

@[simp] theorem gradedProfileDualOperators_zero_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t) :
    gradedBinaryVectorVal (dualGeneratorWeights s) (t+1) (gradedProfileDualOperators q s t 0 m) =
      binaryU K • gradedBinaryVectorVal (dualGeneratorWeights s) t m := rfl

@[simp] theorem gradedProfileDualOperators_one_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t) :
    gradedBinaryVectorVal (dualGeneratorWeights s) (t+1) (gradedProfileDualOperators q s t 1 m) =
      binaryV K • gradedBinaryVectorVal (dualGeneratorWeights s) t m := rfl

@[simp] theorem gradedProfileDualOperators_two_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t) :
    gradedBinaryVectorVal (dualGeneratorWeights s) (t+1) (gradedProfileDualOperators q s t 2 m) =
      cyclicZDual (profileFactors q s) (gradedBinaryVectorVal (dualGeneratorWeights s) t m) := rfl

/-- A concrete finite basis with exactly the advertised number of rows. -/
def profileSourceBasis (s : CubicProfile) (r : ℕ) :
    Basis (Fin (profileRows s r)) K
      (GradedBinaryVector (K := K) (generatorWeights s) (r : ℤ)) :=
  finBasisOfFinrankEq K _ (finrank_gradedProfile_eq_rows s r)

/-- The next graded component has exactly three additional basis vectors. -/
def profileTargetBasis (s : CubicProfile) (r : ℕ) :
    Basis (Fin (profileRows s r+3)) K
      (GradedBinaryVector (K := K) (generatorWeights s) ((r : ℤ)+1)) :=
  finBasisOfFinrankEq K _ (by
    rw [show (r : ℤ)+1 = ((r+1 : ℕ) : ℤ) by omega,
      finrank_gradedProfile_eq_rows, profileRows_succ])

end ChoppedPlane.QWeyl
