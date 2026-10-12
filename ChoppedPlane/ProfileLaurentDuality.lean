module

public import ChoppedPlane.OperatorDifferentialNaturality
public import ChoppedPlane.GradedBinaryLaurent
public import ChoppedPlane.LaurentAuxiliaryDuality
public import ChoppedPlane.LaurentChartComplex
public import ChoppedPlane.ProfileResidueOperators
public import ChoppedPlane.QWeylLaurentOperators
public import ChoppedPlane.LaurentAuxiliaryProjection
public import ChoppedPlane.QWeylLaurentTop

@[expose] public section

/-! Actual graded coefficient transport for the residue dual of the cubic
profile differential. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace ChoppedPlane.QWeyl
open LaurentPairing LaurentChartComplex Module
variable {K : Type*} [Field K]

/-- The primal profile's original generator shifts, in Laurent coordinates. -/
abbrev profileLaurentWeights (s : CubicProfile) : Fin 3 → ℤ :=
  fun i => (generatorWeights s i : ℤ)

/-- Flattened primal shifts retain the original coefficient generator. -/
abbrev profileAuxiliaryWeights (s : CubicProfile) (t : ℕ) : Fin 3 × Sym (Fin 3) t → ℤ :=
  auxiliaryGeneratorWeights (profileLaurentWeights s) t

theorem profile_dual_weight_eq (s : CubicProfile) (i : Fin 3) :
    (dualGeneratorWeights s i : ℤ) = 2-profileLaurentWeights s i := by
  cases s <;> fin_cases i <;> norm_num [dualGeneratorWeights,
    profileLaurentWeights, generatorWeights]

/-- The genuine top Laurent component of a dual profile is exactly the
negative component in the primal residue pairing. -/
def profileTopNegativeEquiv (s : CubicProfile) (r : ℤ) (t : ℕ) :
    topGrade (K := K) (fun i : Fin 3 × Sym (Fin 3) t =>
      (dualGeneratorWeights s i.1 : ℤ)) (-r) ≃ₗ[K]
      negativeGrade (K := K) (profileAuxiliaryWeights s t) r := by
  have hw : (fun i : Fin 3 × Sym (Fin 3) t => (dualGeneratorWeights s i.1 : ℤ)) =
      (fun i => 2-profileAuxiliaryWeights s t i) := by
    funext i
    exact profile_dual_weight_eq s i.1
  exact LinearEquiv.ofEq _ _ (by
    rw [hw]
    exact topGrade_dual_shift_eq (profileAuxiliaryWeights s t) r)

/-- Actual finite coefficient flattening of the profile top Laurent grade. -/
def profileTopCoefficientEquiv (s : CubicProfile) (r : ℤ) (t : ℕ) :
    topGrade (K := K) (fun i : Fin 3 × Sym (Fin 3) t =>
      (dualGeneratorWeights s i.1 : ℤ)) (-r) ≃ₗ[K]
      (Sym (Fin 3) t → negativeGrade (K := K) (profileLaurentWeights s) r) :=
  (profileTopNegativeEquiv s r t).trans
    (negativeGradeSplit (profileLaurentWeights s) r)

@[simp] theorem profileTopCoefficientEquiv_coeff
    (s : CubicProfile) (r : ℤ) (t : ℕ)
    (p : topGrade (K := K) (fun i : Fin 3 × Sym (Fin 3) t =>
      (dualGeneratorWeights s i.1 : ℤ)) (-r))
    (j : Sym (Fin 3) t) (i : Fin 3) (e : ℤ × ℤ) :
    (profileTopCoefficientEquiv s r t p j).val (i,e) = p.val ((i,j),e) := by
  rfl

@[simp] theorem profileTopCoefficientEquiv_vector
    (s : CubicProfile) (r : ℤ) (t : ℕ)
    (p : topGrade (K := K) (fun i : Fin 3 × Sym (Fin 3) t =>
      (dualGeneratorWeights s i.1 : ℤ)) (-r))
    (j : Sym (Fin 3) t) :
    freeLaurentEquiv (profileTopCoefficientEquiv s r t p j).val =
      auxiliaryLaurentVectorEquiv p.val j := by
  funext i
  ext e
  simp only [freeLaurentEquiv_coeff, profileTopCoefficientEquiv_coeff,
    auxiliaryLaurentVectorEquiv_coeff]

theorem auxiliaryLaurentVectorEquiv_freeNegativePart
    {S : Type*} [Finite S] (p : FreeLaurent K (Fin 3 × S)) (j : S) :
    freeLaurentEquiv.symm (auxiliaryLaurentVectorEquiv (freeNegativePart p) j) =
      freeNegativePart (freeLaurentEquiv.symm (auxiliaryLaurentVectorEquiv p j)) := by
  ext ie
  obtain ⟨i,e⟩ := ie
  simp only [auxiliaryLaurentVectorEquiv_component_coeff, freeNegativePart_apply]

/-- The finite polynomial differential is the actual positive Laurent
differential after coefficient-preserving graded coordinate transport. -/
theorem profileDifferential_surjective_iff_positiveDifferential
    (q : K) (s : CubicProfile) (r : ℤ) (t : ℕ) :
    Function.Surjective (operatorDifferential (gradedProfileOperators q s r) t) ↔
      Function.Surjective (operatorDifferential (K := K)
        (V := positiveGrade (K := K) (profileLaurentWeights s) r)
        (W := positiveGrade (K := K) (profileLaurentWeights s) (r+1))
        (profilePositiveOperators q s r) t) := by
  apply operatorDifferential_surjective_iff_of_equiv (K := K)
    (V := GradedBinaryVector (K := K) (generatorWeights s) r)
    (W := GradedBinaryVector (K := K) (generatorWeights s) (r+1))
    (V' := positiveGrade (K := K) (profileLaurentWeights s) r)
    (W' := positiveGrade (K := K) (profileLaurentWeights s) (r+1))
    (gradedBinaryLaurentEquiv (generatorWeights s) r)
    (gradedBinaryLaurentEquiv (generatorWeights s) (r+1))
  intro i v
  simp [profilePositiveOperators]

/-- The actual finite polynomial differential is surjective precisely when
the actual auxiliary multiplication by the projected dual actions is
injective. -/
theorem profileDifferential_surjective_iff_negativeMultiply_injective [CharZero K]
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (t : ℕ) :
    Function.Surjective (operatorDifferential (gradedProfileOperators q s r) t) ↔
      Function.Injective (auxiliaryOperatorMultiply (K := K)
      (W' := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
      (V' := negativeGrade (K := K) (profileLaurentWeights s) r)
      (profileNegativeOperators q hq s r) t) := by
  rw [profileDifferential_surjective_iff_positiveDifferential]
  exact operatorDifferential_surjective_iff_auxiliaryMultiply_injective (K := K)
    (fun i => (generatorWeights s i : ℤ)) r
    (profilePositiveOperators q s r) (profileNegativeOperators q hq s r)
    (profileOperators_residue_adjoint q hq s r) t

/-- The projected auxiliary coefficient multiplication is literally the
actual chart tensor multiplication followed by negative Laurent projection. -/
theorem profileNegativeMultiply_chart_formula
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (t : ℕ)
    (c : Sym (Fin 3) t → negativeGrade (K := K) (profileLaurentWeights s) (r+1)) :
    (fun b => (auxiliaryOperatorMultiply (K := K)
      (W' := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
      (V' := negativeGrade (K := K) (profileLaurentWeights s) r)
      (profileNegativeOperators q hq s r) t c b).val) =
      fun b => freeNegativePart (freeLaurentEquiv.symm
        (chartFiniteMultiply binaryChartLaurentMap q hq s t
          (fun j => freeLaurentEquiv (c j).val) b)) := by
  letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  letI := cyclicModuleScalarTower (K := K)
    (binaryChartLaurentMap (binaryCubic K))
    (chartDualZ binaryChartLaurentMap q s)
    (chartDualZ_cube binaryChartLaurentMap q hq s)
  let ι : negativeGrade (K := K) (profileLaurentWeights s) (r+1) →ₗ[K]
      (Fin 3 → BinaryLaurent K) :=
    freeLaurentEquiv.toLinearMap.comp (negativeGrade (K := K) (profileLaurentWeights s) (r+1)).subtype
  let ρ : (Fin 3 → BinaryLaurent K) →ₗ[K] FreeLaurent K (Fin 3) :=
    freeNegativePart.comp freeLaurentEquiv.symm.toLinearMap
  have hL : (fun i : Fin 3 => (negativeGrade (K := K) (profileLaurentWeights s) r).subtype.comp
        (profileNegativeOperators q hq s r i)) =
      (fun i : Fin 3 => ρ.comp ((scalarAction (K := K) (chartLinearForm (binaryChartLaurentMap (K := K)) i)).comp ι)) := by
    funext i
    apply LinearMap.ext
    intro p
    change freeNegativePart (rawLaurentProfileDualOperators q s i p.val) =
      freeNegativePart (freeLaurentEquiv.symm
        (scalarAction (K := K) (chartLinearForm (binaryChartLaurentMap (K := K)) i)
          (freeLaurentEquiv p.val)))
    rw [← rawLaurentProfileDualOperators_chart_action q hq s i p.val,
      LinearEquiv.symm_apply_apply]
  have hpost := auxiliaryOperatorMultiply_project (K := K)
    (V := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
    (W := negativeGrade (K := K) (profileLaurentWeights s) r)
    (P := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
    (Q := FreeLaurent K (Fin 3))
    (profileNegativeOperators q hq s r)
    (LinearMap.id : negativeGrade (K := K) (profileLaurentWeights s) (r+1) →ₗ[K] _)
    (negativeGrade (K := K) (profileLaurentWeights s) r).subtype t c
  have hpost' : (fun b => (auxiliaryOperatorMultiply (K := K)
      (W' := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
      (V' := negativeGrade (K := K) (profileLaurentWeights s) r)
      (profileNegativeOperators q hq s r) t c b).val) =
      auxiliaryOperatorMultiply (fun i : Fin 3 => (negativeGrade (K := K) (profileLaurentWeights s) r).subtype.comp
        (profileNegativeOperators q hq s r i)) t c := by
    simpa using hpost.symm
  rw [hpost', hL]
  have hproj := finiteMultiply_project (K := K)
    (R := ChartCubicRing (binaryChartLaurentMap (K := K)))
    (M := Fin 3 → BinaryLaurent K)
    (P := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
    (Q := FreeLaurent K (Fin 3)) (chartLinearForm (binaryChartLaurentMap (K := K))) ι ρ t c
  simpa only [ι, ρ, chartFiniteMultiply, LinearMap.restrictScalars_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply] using hproj

/-- The concrete top Laurent map is the same projected multiplication as
the one in the finite perfect residue pairing, coefficient for coefficient. -/
theorem profileTopCoefficientEquiv_multiply
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (t : ℕ)
    (p : topGrade (K := K) (auxiliaryDualWeights s t) (-(r+1))) :
    profileTopCoefficientEquiv s r (t+1) (profileLaurentTopMultiply q hq s r t p) =
      auxiliaryOperatorMultiply (K := K)
      (W' := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
      (V' := negativeGrade (K := K) (profileLaurentWeights s) r)
      (profileNegativeOperators q hq s r) t
        (profileTopCoefficientEquiv s (r+1) t p) := by
  funext b
  apply Subtype.ext
  have hr := congrFun (profileNegativeMultiply_chart_formula q hq s r t
    (profileTopCoefficientEquiv s (r+1) t p)) b
  rw [hr]
  have hc : (fun j => freeLaurentEquiv
      (profileTopCoefficientEquiv s (r+1) t p j).val) =
      auxiliaryLaurentVectorEquiv p.val := by
    funext j
    exact profileTopCoefficientEquiv_vector s (r+1) t p j
  rw [hc]
  have he : (profileTopCoefficientEquiv s r (t+1)
      (profileLaurentTopMultiply q hq s r t p) b).val =
      freeLaurentEquiv.symm (auxiliaryLaurentVectorEquiv
        (profileLaurentTopMultiply q hq s r t p).val b) := by
    apply freeLaurentEquiv.injective
    rw [LinearEquiv.apply_symm_apply]
    exact profileTopCoefficientEquiv_vector s r (t+1) _ b
  rw [he, profileLaurentTopMultiply_val,
    auxiliaryLaurentVectorEquiv_freeNegativePart,
    auxiliaryLaurentVectorEquiv_profileLaurentMultiply]

theorem profileNegativeMultiply_injective_iff_topMultiply_injective
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (t : ℕ) :
    Function.Injective (auxiliaryOperatorMultiply (K := K)
      (W' := negativeGrade (K := K) (profileLaurentWeights s) (r+1))
      (V' := negativeGrade (K := K) (profileLaurentWeights s) r)
      (profileNegativeOperators q hq s r) t) ↔
      Function.Injective (profileLaurentTopMultiply q hq s r t) := by
  constructor
  · intro h p p' hp
    apply (profileTopCoefficientEquiv s (r+1) t).injective
    apply h
    rw [← profileTopCoefficientEquiv_multiply, ← profileTopCoefficientEquiv_multiply, hp]
  · intro h c c' hc
    obtain ⟨p,rfl⟩ := (profileTopCoefficientEquiv s (r+1) t).surjective c
    obtain ⟨p',rfl⟩ := (profileTopCoefficientEquiv s (r+1) t).surjective c'
    apply congrArg (profileTopCoefficientEquiv s (r+1) t)
    apply h
    apply (profileTopCoefficientEquiv s r (t+1)).injective
    rw [profileTopCoefficientEquiv_multiply, profileTopCoefficientEquiv_multiply]
    exact hc

/-- Exact actual cubic residue duality: finite polynomial differentiation is
surjective if and only if the literal projected dual top Laurent map is
injective. -/
theorem profileDifferential_surjective_iff_topMultiply_injective [CharZero K]
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (t : ℕ) :
    Function.Surjective (operatorDifferential (gradedProfileOperators q s r) t) ↔
      Function.Injective (profileLaurentTopMultiply q hq s r t) := by
  rw [profileDifferential_surjective_iff_negativeMultiply_injective,
    profileNegativeMultiply_injective_iff_topMultiply_injective]

end ChoppedPlane.QWeyl
