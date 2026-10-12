module

public import ChoppedPlane.GradedBinaryLaurentOperators
public import ChoppedPlane.LaurentProjectedResidueOperators
public import ChoppedPlane.LaurentAuxiliaryScalarOperators
public import ChoppedPlane.QWeylActualChartMaps
public import ChoppedPlane.CyclicScalarTower

@[expose] public section

/-! The concrete polynomial profile operators and their projected Laurent
adjoints, on the actual weighted homogeneous coefficient spaces. -/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
variable {K : Type*} [Field K] {ι : Type*}

theorem vectorResidueFunctional_scalar_transpose [Fintype ι] (w : ι → K)
    (c : BinaryLaurent K) (q p : ι → BinaryLaurent K) :
    vectorResidueFunctional w q (fun i => c * p i) =
      vectorResidueFunctional w (fun i => c * q i) p := by
  rw [vectorResidueFunctional_apply, vectorResidueFunctional_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← mul_assoc, mul_comm (q i) c]

theorem freeNegativePart_mem_negativeGrade_of_overlap (g : ι → ℤ) (r : ℤ)
    (p : FreeLaurent K ι)
    (hp : p ∈ LaurentChartComplex.overlapGrade (fun i => 2 - g i) (-r)) :
    freeNegativePart p ∈ negativeGrade (K := K) g r := by
  classical
  apply (Finsupp.mem_supported K _).mpr
  rintro ⟨i,e⟩ he
  have hn : freeNegativePart p (i,e) ≠ 0 := Finsupp.mem_support_iff.mp he
  rw [freeNegativePart_apply] at hn
  split_ifs at hn with hneg
  · have hdeg := (Finsupp.mem_supported K p).mp hp (Finsupp.mem_support_iff.mpr hn)
    exact ⟨hneg.1,hneg.2,hdeg⟩
  · exact False.elim (hn rfl)

theorem negativeGrade_mem_overlap (g : ι → ℤ) (r : ℤ)
    (p : negativeGrade (K := K) g r) :
    p.val ∈ LaurentChartComplex.overlapGrade (fun i => 2 - g i) (-r) := by
  apply (Finsupp.mem_supported K p.val).mpr
  intro e he
  exact ((Finsupp.mem_supported K p.val).mp p.property he).2.2

end ChoppedPlane.LaurentPairing

namespace ChoppedPlane.QWeyl
open MvPolynomial Module LaurentPairing LaurentChartComplex
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K]

/-- The actual `u`, `v`, and forward cyclic actions on free Laurent vectors. -/
def rawLaurentProfileOperators (q : K) (s : CubicProfile) :
    Fin 3 → (FreeLaurent K (Fin 3) →ₗ[K] FreeLaurent K (Fin 3)) :=
  ![laurentScalar U, laurentScalar V, laurentCyclicZ q s]

/-- The actual coefficientwise dual actions before top-Laurent projection. -/
def rawLaurentProfileDualOperators (q : K) (s : CubicProfile) :
    Fin 3 → (FreeLaurent K (Fin 3) →ₗ[K] FreeLaurent K (Fin 3)) :=
  ![laurentScalar U, laurentScalar V, laurentCyclicZDual q s]

/-- The profile's actual graded polynomial operators in Laurent coefficients. -/
def profilePositiveOperators (q : K) (s : CubicProfile) (r : ℤ) :
    Fin 3 → (positiveGrade (K := K) (fun i => (generatorWeights s i : ℤ)) r →ₗ[K]
      positiveGrade (K := K) (fun i => (generatorWeights s i : ℤ)) (r+1)) :=
  fun i => ((gradedBinaryLaurentEquiv (generatorWeights s) (r+1)).toLinearMap.comp
    (gradedProfileOperators q s r i)).comp
      (gradedBinaryLaurentEquiv (generatorWeights s) r).symm.toLinearMap

@[simp] theorem profilePositiveOperators_val (q : K) (s : CubicProfile) (r : ℤ)
    (i : Fin 3) (p : positiveGrade (K := K) (fun j => (generatorWeights s j : ℤ)) r) :
    (profilePositiveOperators q s r i p).val = rawLaurentProfileOperators q s i p.val := by
  let m := (gradedBinaryLaurentEquiv (generatorWeights s) r).symm p
  have hm : gradedBinaryLaurentEquiv (generatorWeights s) r m = p :=
    LinearEquiv.apply_symm_apply _ _
  change (gradedBinaryLaurentEquiv (generatorWeights s) (r+1)
    (gradedProfileOperators q s r i m)).val = _
  fin_cases i
  · change (gradedBinaryLaurentEquiv (generatorWeights s) (r+1)
      (gradedBinaryCoordinate 0 (generatorWeights s) r m)).val = laurentScalar U p.val
    rw [gradedBinaryLaurentEquiv_coordinate, binaryLaurentEmbedding_X_zero, hm]
  · change (gradedBinaryLaurentEquiv (generatorWeights s) (r+1)
      (gradedBinaryCoordinate 1 (generatorWeights s) r m)).val = laurentScalar V p.val
    rw [gradedBinaryLaurentEquiv_coordinate, binaryLaurentEmbedding_X_one, hm]
  · change (gradedBinaryLaurentEquiv (generatorWeights s) (r+1)
      (gradedProfileZ q s r m)).val = laurentCyclicZ q s p.val
    rw [gradedBinaryLaurentEquiv_Z, hm]

theorem dualGeneratorWeights_int (s : CubicProfile) :
    (fun i => (dualGeneratorWeights s i : ℤ)) =
      (fun i => 2 - (generatorWeights s i : ℤ)) := by
  funext i
  cases s <;> fin_cases i <;> norm_num [dualGeneratorWeights, generatorWeights]

theorem rawLaurentProfileDualOperators_mem_overlapGrade (q : K) (s : CubicProfile)
    (k : ℤ) (i : Fin 3) (p : FreeLaurent K (Fin 3))
    (hp : p ∈ overlapGrade (fun j => 2 - (generatorWeights s j : ℤ)) k) :
    rawLaurentProfileDualOperators q s i p ∈
      overlapGrade (fun j => 2 - (generatorWeights s j : ℤ)) (k+1) := by
  fin_cases i
  · exact laurentScalar_mem_overlapGrade U 1 U_mem_polynomialLaurentGrade _ k p hp
  · exact laurentScalar_mem_overlapGrade V 1 V_mem_polynomialLaurentGrade _ k p hp
  · rw [← dualGeneratorWeights_int] at hp ⊢
    exact laurentCyclicZDual_mem_overlapGrade q s k p hp

/-- The actual dual profile actions followed by strictly negative projection. -/
def profileNegativeOperators (q : K) (_hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) :
    Fin 3 → (negativeGrade (K := K) (fun i => (generatorWeights s i : ℤ)) (r+1) →ₗ[K]
      negativeGrade (K := K) (fun i => (generatorWeights s i : ℤ)) r) :=
  fun i => (freeNegativePart.comp (rawLaurentProfileDualOperators q s i)).restrict
    (p := negativeGrade (fun j => (generatorWeights s j : ℤ)) (r+1))
    (q := negativeGrade (fun j => (generatorWeights s j : ℤ)) r) (by
      intro p hp
      apply freeNegativePart_mem_negativeGrade_of_overlap
      have hn := negativeGrade_mem_overlap (fun j => (generatorWeights s j : ℤ)) (r+1)
        ⟨p,hp⟩
      have h := rawLaurentProfileDualOperators_mem_overlapGrade q s (-(r+1)) i p hn
      simpa only [show -(r+1)+1 = -r by omega] using h)

@[simp] theorem profileNegativeOperators_val (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (i : Fin 3)
    (p : negativeGrade (K := K) (fun j => (generatorWeights s j : ℤ)) (r+1)) :
    (profileNegativeOperators q hq s r i p).val =
      freeNegativePart (rawLaurentProfileDualOperators q s i p.val) := rfl

/-- Each actual polynomial profile operator is adjoint to its projected
literal dual operator; no rank or matrix-invertibility premise is required. -/
theorem profileOperators_residue_adjoint (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (i : Fin 3)
    (d : negativeGrade (K := K) (fun j => (generatorWeights s j : ℤ)) (r+1))
    (p : positiveGrade (K := K) (fun j => (generatorWeights s j : ℤ)) r) :
    residuePair (fun j => (generatorWeights s j : ℤ)) (r+1) d
        (profilePositiveOperators q s r i p) =
      residuePair (fun j => (generatorWeights s j : ℤ)) r
        (profileNegativeOperators q hq s r i d) p := by
  rw [residuePair_eq_vectorResidue, residuePair_eq_vectorResidue,
    profilePositiveOperators_val, profileNegativeOperators_val,
    vectorResidueFunctional_freeNegativePart]
  fin_cases i
  · change vectorResidueFunctional (fun _ => (1 : K)) (freeLaurentEquiv d.val)
        (freeLaurentEquiv (laurentScalar U p.val)) =
      vectorResidueFunctional (fun _ => (1 : K)) (freeLaurentEquiv (laurentScalar U d.val))
        (freeLaurentEquiv p.val)
    have hscalar (a : FreeLaurent K (Fin 3)) :
        freeLaurentEquiv (laurentScalar U a) = fun j => U * freeLaurentEquiv a j :=
      funext (freeLaurentEquiv_laurentScalar U a)
    rw [hscalar, hscalar]
    exact vectorResidueFunctional_scalar_transpose (fun _ : Fin 3 => (1 : K)) U _ _
  · change vectorResidueFunctional (fun _ => (1 : K)) (freeLaurentEquiv d.val)
        (freeLaurentEquiv (laurentScalar V p.val)) =
      vectorResidueFunctional (fun _ => (1 : K)) (freeLaurentEquiv (laurentScalar V d.val))
        (freeLaurentEquiv p.val)
    have hscalar (a : FreeLaurent K (Fin 3)) :
        freeLaurentEquiv (laurentScalar V a) = fun j => V * freeLaurentEquiv a j :=
      funext (freeLaurentEquiv_laurentScalar V a)
    rw [hscalar, hscalar]
    exact vectorResidueFunctional_scalar_transpose (fun _ : Fin 3 => (1 : K)) V _ _
  · change vectorResidueFunctional (fun _ => (1 : K)) (freeLaurentEquiv d.val)
        (freeLaurentEquiv (laurentCyclicZ q s p.val)) =
      vectorResidueFunctional (fun _ => (1 : K))
        (freeLaurentEquiv (laurentCyclicZDual q s d.val)) (freeLaurentEquiv p.val)
    rw [freeLaurentEquiv_laurentCyclicZ, freeLaurentEquiv_laurentCyclicZDual]
    exact vectorResidueFunctional_cyclic_transpose (1 : K) _ _ _

/-- The raw dual Laurent operators are precisely the three actions of the
actual chart cubic quotient ring. -/
theorem rawLaurentProfileDualOperators_chart_action
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    letI := cyclicModuleScalarTower (K := K)
      (binaryChartLaurentMap (binaryCubic K))
      (chartDualZ binaryChartLaurentMap q s)
      (chartDualZ_cube binaryChartLaurentMap q hq s)
    ∀ (i : Fin 3) (p : FreeLaurent K (Fin 3)),
      freeLaurentEquiv (rawLaurentProfileDualOperators q s i p) =
        scalarAction (K := K) (chartLinearForm (binaryChartLaurentMap (K := K)) i)
          (freeLaurentEquiv p) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  let := cyclicModuleScalarTower (K := K)
    (binaryChartLaurentMap (binaryCubic K))
    (chartDualZ binaryChartLaurentMap q s)
    (chartDualZ_cube binaryChartLaurentMap q hq s)
  intro i p
  rw [scalarAction_apply]
  fin_cases i
  · change freeLaurentEquiv (laurentScalar U p) =
      cyclicCoefficientHom _ (binaryChartLaurentMap (binaryU K)) • freeLaurentEquiv p
    rw [cyclicModule_coefficient_smul, binaryChartLaurentMap_binaryU]
    funext j
    simp only [freeLaurentEquiv_laurentScalar, Pi.smul_apply, smul_eq_mul]
  · change freeLaurentEquiv (laurentScalar V p) =
      cyclicCoefficientHom _ (binaryChartLaurentMap (binaryV K)) • freeLaurentEquiv p
    rw [cyclicModule_coefficient_smul, binaryChartLaurentMap_binaryV]
    funext j
    simp only [freeLaurentEquiv_laurentScalar, Pi.smul_apply, smul_eq_mul]
  · change freeLaurentEquiv (laurentCyclicZDual q s p) = cyclicRoot _ • freeLaurentEquiv p
    rw [cyclicModule_root_smul, freeLaurentEquiv_laurentCyclicZDual]
    rfl

/-- The graded dual action is the literal chart-ring scalar action followed
componentwise by the actual negative Laurent projection. -/
theorem profileNegativeOperators_chart_action
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    letI := cyclicModuleScalarTower (K := K)
      (binaryChartLaurentMap (binaryCubic K))
      (chartDualZ binaryChartLaurentMap q s)
      (chartDualZ_cube binaryChartLaurentMap q hq s)
    ∀ (i : Fin 3)
      (p : negativeGrade (K := K) (fun j => (generatorWeights s j : ℤ)) (r+1)),
      freeLaurentEquiv (profileNegativeOperators q hq s r i p).val =
        fun j => negativePart
          (scalarAction (K := K) (chartLinearForm (binaryChartLaurentMap (K := K)) i)
            (freeLaurentEquiv p.val) j) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  let := cyclicModuleScalarTower (K := K)
    (binaryChartLaurentMap (binaryCubic K))
    (chartDualZ binaryChartLaurentMap q s)
    (chartDualZ_cube binaryChartLaurentMap q hq s)
  intro i p
  rw [profileNegativeOperators_val]
  funext j
  rw [freeLaurentEquiv_negativePart, rawLaurentProfileDualOperators_chart_action q hq s]

end ChoppedPlane.QWeyl
