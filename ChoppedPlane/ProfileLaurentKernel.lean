module

public import ChoppedPlane.GradedBinaryLaurentOperators
public import ChoppedPlane.QWeylLaurentOperators
public import ChoppedPlane.QWeylActualChartMaps
public import ChoppedPlane.LaurentAuxiliaryScalarOperators
public import ChoppedPlane.ProfileCriticalChecks

@[expose] public section

/-! Actual transport of the global cubic differential kernel to the
nonnegative Laurent coefficient component. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open Module MvPolynomial LaurentPairing LaurentChartComplex
open FiniteCech SymmetricDerivative
variable {K : Type*} [Field K]
set_option maxHeartbeats 1000000

def gradedChartEmbedding (w : Fin 3 → ℕ) (r : ℤ) :
    GradedBinaryVector (K := K) w r →ₗ[K] (Fin 3 → BinaryLaurent K) :=
  (freeLaurentEquiv (K := K) (ι := Fin 3)).toLinearMap.comp
    ((binaryVectorLaurent (K := K)).comp (gradedBinaryVectorVal w r))

@[simp] theorem gradedChartEmbedding_apply (w : Fin 3 → ℕ) (r : ℤ)
    (m : GradedBinaryVector (K := K) w r) (i : Fin 3) :
    gradedChartEmbedding w r m i = binaryLaurentEmbedding (m i).val := by
  exact freeLaurentEquiv_binaryVectorLaurent (gradedBinaryVectorVal w r m) i

theorem gradedChartEmbedding_injective (w : Fin 3 → ℕ) (r : ℤ) :
    Function.Injective (gradedChartEmbedding (K := K) w r) :=
  freeLaurentEquiv.injective.comp
    (binaryVectorLaurent_injective.comp (gradedBinaryVectorVal_injective w r))

theorem chartDirectional_gradedDual (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (n : ℕ)
    (c : Sym (Fin 3) (n+1) → GradedBinaryVector (K := K) (dualGeneratorWeights s) r) :
    chartFiniteDirectional binaryChartLaurentMap q hq s n
      (fun b => gradedChartEmbedding (dualGeneratorWeights s) r (c b)) =
    fun b => gradedChartEmbedding (dualGeneratorWeights s) (r+1)
      (operatorDifferential (gradedProfileDualOperators q s r) n c b) := by
  letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  letI := cyclicModuleScalarTower (K := K)
    (binaryChartLaurentMap (binaryCubic K))
    (chartDualZ binaryChartLaurentMap q s)
    (chartDualZ_cube binaryChartLaurentMap q hq s)
  have hact (i : Fin 3)
      (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) r) :
      scalarAction (K := K) (chartLinearForm (binaryChartLaurentMap (K := K)) i)
        (gradedChartEmbedding (dualGeneratorWeights s) r m) =
      gradedChartEmbedding (dualGeneratorWeights s) (r+1)
        (gradedProfileDualOperators q s r i m) := by
    rw [scalarAction_apply]
    fin_cases i
    · change cyclicCoefficientHom _ (binaryChartLaurentMap (binaryU K)) • _ = _
      rw [cyclicModule_coefficient_smul]
      funext j
      simp [gradedChartEmbedding_apply, gradedProfileDualOperators,
        gradedBinaryMultiply, Pi.smul_apply, smul_eq_mul,
        binaryChartLaurentMap_eq_binaryLaurentEmbedding]
    · change cyclicCoefficientHom _ (binaryChartLaurentMap (binaryV K)) • _ = _
      rw [cyclicModule_coefficient_smul]
      funext j
      simp [gradedChartEmbedding_apply, gradedProfileDualOperators,
        gradedBinaryMultiply, Pi.smul_apply, smul_eq_mul,
        binaryChartLaurentMap_eq_binaryLaurentEmbedding]
    · change cyclicRoot _ • _ = _
      rw [cyclicModule_root_smul]
      funext j
      fin_cases j <;>
        simp [chartDualZ, cyclicZDual, gradedChartEmbedding_apply,
          gradedProfileDualOperators, gradedProfileZDual,
          gradedBinaryVectorVal, binaryChartLaurentMap_eq_binaryLaurentEmbedding]
  change finiteDirectional (chartLinearForm binaryChartLaurentMap) n
      (fun b => gradedChartEmbedding (dualGeneratorWeights s) r (c b)) = _
  rw [finiteDirectional_eq_operatorDifferential (K := K)]
  funext b
  simp only [operatorDifferential_coeff, map_sum, map_smul, hact]

theorem profileLaurentDirectional_positive_kernel_zero
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (n : ℕ)
    (hinj : Function.Injective (operatorDifferential (gradedProfileDualOperators q s r) n))
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n+1)))
    (hp : p ∈ positiveGrade (auxiliaryDualWeights s (n+1)) r)
    (hd : profileLaurentDirectional q hq s n p = 0) : p = 0 := by
  let p' : positiveGrade (K := K)
      (fun i : Fin 3 × Sym (Fin 3) (n+1) => (dualGeneratorWeights s i.1 : ℤ)) r := ⟨p,hp⟩
  let c := fun b => (gradedBinaryLaurentEquiv (K := K) (dualGeneratorWeights s) r).symm
    (positiveGradeSplit (fun i => (dualGeneratorWeights s i : ℤ)) r p' b)
  have hemb : auxiliaryLaurentVectorEquiv p =
      fun b => gradedChartEmbedding (dualGeneratorWeights s) r (c b) := by
    funext b
    apply (freeLaurentEquiv (K := K) (ι := Fin 3)).symm.injective
    have hc := (gradedBinaryLaurentEquiv (K := K) (dualGeneratorWeights s) r).apply_symm_apply
      (positiveGradeSplit (fun i => (dualGeneratorWeights s i : ℤ)) r p' b)
    have hcval := congrArg Subtype.val hc
    change binaryVectorLaurent (gradedBinaryVectorVal (dualGeneratorWeights s) r (c b)) =
      splitFreeLaurentEquiv p b at hcval
    simp only [gradedChartEmbedding, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rw [hcval]
    ext e
    rw [auxiliaryLaurentVectorEquiv_component_coeff, splitFreeLaurentEquiv_apply]
  have hcder : operatorDifferential (gradedProfileDualOperators q s r) n c = 0 := by
    have hraw := congrArg auxiliaryLaurentVectorEquiv hd
    rw [auxiliaryLaurentVectorEquiv_profileLaurentDirectional, hemb,
      chartDirectional_gradedDual] at hraw
    funext b
    apply gradedChartEmbedding_injective (dualGeneratorWeights s) (r+1)
    simpa only [map_zero, Pi.zero_apply] using congrFun hraw b
  have hc0 : c = 0 := hinj (hcder.trans (map_zero _).symm)
  apply auxiliaryLaurentVectorEquiv.injective
  rw [hemb, hc0]
  simp only [Pi.zero_apply, map_zero]
  rfl

theorem profileLaurentDirectional_critical_kernel_zero [CharZero K]
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r n : ℕ)
    (hn : profileCriticalDegree s r = n+1)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n+1)))
    (hp : p ∈ positiveGrade (auxiliaryDualWeights s (n+1))
      (((n+1 : ℕ) : ℤ) - (r : ℤ)))
    (hd : profileLaurentDirectional q hq s n p = 0) : p = 0 := by
  apply profileLaurentDirectional_positive_kernel_zero q hq s _ n _ p hp hd
  apply profileDualDifferential_injective q hq s
    (((n+1 : ℕ) : ℤ) - (r : ℤ)) n
  intro i
  have hm : (profileMultiplicity s : ℤ) = 3 - (profileIndex s : ℤ) := by
    cases s <;> rfl
  simpa only [hm, hn] using profile_left_dual_degree_bound s r i

end ChoppedPlane.QWeyl
