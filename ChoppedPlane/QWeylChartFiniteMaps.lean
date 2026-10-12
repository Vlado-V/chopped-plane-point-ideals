module

public import ChoppedPlane.QWeylLaurentCharts
public import ChoppedPlane.CyclicScalarTower
public import ChoppedPlane.TensorCoefficientBaseChange
public import ChoppedPlane.BinaryChartPolynomialMaps
public import ChoppedPlane.FiniteCrossAnnihilation

@[expose] public section

/-! The finite coefficient maps on the actual cyclic modules of the two
binary Laurent charts.  The maps retain the original coefficient-field
action; their formulas and exactness are inherited from the actual tensor
operators, rather than postulated for an abstract finite complex. -/

noncomputable section
namespace ChoppedPlane.QWeyl

open MvPolynomial SymmetricDerivative FiniteCech BinaryChartRings LaurentPairing

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Finite auxiliary coefficient vectors on an actual chart. -/
abbrev ChartFiniteVector (A : Type*) (n : ℕ) := Sym (Fin 3) n → Fin 3 → A

/-- Cross substitution on a cyclic chart, with its genuine `K`-linear action. -/
def chartFiniteCross (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    ChartFiniteVector A n →ₗ[K] ChartFiniteVector A n := by
  letI := chartDualModuleStructure φ q hq s
  letI := cyclicModuleScalarTower (K := K) (φ (binaryCubic K))
    (chartDualZ φ q s) (chartDualZ_cube φ q hq s)
  exact (finiteCross (chartCrossMatrix φ) n).restrictScalars K

/-- Multiplication by the actual chart linear form. -/
def chartFiniteMultiply (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    ChartFiniteVector A n →ₗ[K] ChartFiniteVector A (n + 1) := by
  letI := chartDualModuleStructure φ q hq s
  letI := cyclicModuleScalarTower (K := K) (φ (binaryCubic K))
    (chartDualZ φ q s) (chartDualZ_cube φ q hq s)
  exact (finiteMultiply (chartLinearForm φ) n).restrictScalars K

/-- Directional differentiation for the actual chart linear form. -/
def chartFiniteDirectional (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    ChartFiniteVector A (n + 1) →ₗ[K] ChartFiniteVector A n := by
  letI := chartDualModuleStructure φ q hq s
  letI := cyclicModuleScalarTower (K := K) (φ (binaryCubic K))
    (chartDualZ φ q s) (chartDualZ_cube φ q hq s)
  exact (finiteDirectional (chartLinearForm φ) n).restrictScalars K

theorem chartFiniteCross_kernel_u (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ)
    (c : ChartFiniteVector A (n + 1)) :
    chartFiniteCross φ q hq s (n + 1) c = 0 ↔
      c ∈ LinearMap.range (chartFiniteMultiply φ q hq s n) := by
  let := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationU φ a hu).finite_cross_kernel n c

theorem chartFiniteCross_kernel_v (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ)
    (c : ChartFiniteVector A (n + 1)) :
    chartFiniteCross φ q hq s (n + 1) c = 0 ↔
      c ∈ LinearMap.range (chartFiniteMultiply φ q hq s n) := by
  let := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationV φ a hv).finite_cross_kernel n c

theorem chartFiniteMultiply_injective_u (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ) :
    Function.Injective (chartFiniteMultiply φ q hq s n) := by
  let := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationU φ a hu).finiteMultiply_injective n

theorem chartFiniteMultiply_injective_v (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ) :
    Function.Injective (chartFiniteMultiply φ q hq s n) := by
  let := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationV φ a hv).finiteMultiply_injective n

theorem chartFiniteCross_multiply_zero_u (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ)
    (c : ChartFiniteVector A n) :
    chartFiniteCross φ q hq s (n + 1) (chartFiniteMultiply φ q hq s n c) = 0 :=
  (chartFiniteCross_kernel_u φ q hq s a hu n _).mpr ⟨c, rfl⟩

theorem chartFiniteCross_multiply_zero_v (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ)
    (c : ChartFiniteVector A n) :
    chartFiniteCross φ q hq s (n + 1) (chartFiniteMultiply φ q hq s n c) = 0 :=
  (chartFiniteCross_kernel_v φ q hq s a hv n _).mpr ⟨c, rfl⟩

theorem chartFiniteCross_multiply_zero (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ)
    (c : ChartFiniteVector A n) :
    chartFiniteCross φ q hq s (n + 1) (chartFiniteMultiply φ q hq s n c) = 0 := by
  let := chartDualModuleStructure φ q hq s
  exact finiteCross_multiply_zero (chartU φ) (chartV φ) (chartZ φ) n c

/-- The two actual finite operators form a complex on every cyclic chart. -/
theorem chartFiniteDirectional_cross_zero (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ)
    (c : ChartFiniteVector A (n + 1)) :
    chartFiniteDirectional φ q hq s n (chartFiniteCross φ q hq s (n + 1) c) = 0 := by
  let := chartDualModuleStructure φ q hq s
  exact finiteDirectional_cross_zero (chartU φ) (chartV φ) (chartZ φ) n c

section CharacteristicZero
variable [CharZero K]

theorem chartFiniteDirectional_kernel_u (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ)
    (c : ChartFiniteVector A (n + 1)) :
    chartFiniteDirectional φ q hq s n c = 0 ↔
      c ∈ LinearMap.range (chartFiniteCross φ q hq s (n + 1)) := by
  let := chartDualModuleStructure φ q hq s
  constructor
  · intro hc
    have hd : tensorDirectional (chartLinearForm φ)
        (homogeneousTensorSynthesis (n + 1) c) = 0 := by
      rw [← synthesis_finiteDirectional]
      change homogeneousTensorSynthesis n (chartFiniteDirectional φ q hq s n c) = 0
      rw [hc]
      exact (homogeneousTensorSynthesisMap n).map_zero
    obtain ⟨Q, hQ, heq⟩ := chart_dual_cross_range_homogeneous_u φ q hq s a hu
      (n + 1) _ (homogeneousTensorSynthesis_homogeneous (n + 1) c) hd
    refine ⟨homogeneousTensorCoefficientVector (n + 1) Q, ?_⟩
    change homogeneousTensorCoefficientVector (n + 1)
      (tensorChange (chartCrossMatrix φ)
        (homogeneousTensorSynthesis (n + 1)
          (homogeneousTensorCoefficientVector (n + 1) Q))) = c
    rw [homogeneousTensorSynthesis_coefficients (n + 1) Q hQ, heq,
      homogeneousTensorCoefficientVector_synthesis]
  · rintro ⟨d, rfl⟩
    exact chartFiniteDirectional_cross_zero φ q hq s n d

theorem chartFiniteDirectional_kernel_v (φ : BinaryRing K →ₐ[K] A)
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ)
    (c : ChartFiniteVector A (n + 1)) :
    chartFiniteDirectional φ q hq s n c = 0 ↔
      c ∈ LinearMap.range (chartFiniteCross φ q hq s (n + 1)) := by
  let := chartDualModuleStructure φ q hq s
  constructor
  · intro hc
    have hd : tensorDirectional (chartLinearForm φ)
        (homogeneousTensorSynthesis (n + 1) c) = 0 := by
      rw [← synthesis_finiteDirectional]
      change homogeneousTensorSynthesis n (chartFiniteDirectional φ q hq s n c) = 0
      rw [hc]
      exact (homogeneousTensorSynthesisMap n).map_zero
    obtain ⟨Q, hQ, heq⟩ := chart_dual_cross_range_homogeneous_v φ q hq s a hv
      (n + 1) _ (homogeneousTensorSynthesis_homogeneous (n + 1) c) hd
    refine ⟨homogeneousTensorCoefficientVector (n + 1) Q, ?_⟩
    change homogeneousTensorCoefficientVector (n + 1)
      (tensorChange (chartCrossMatrix φ)
        (homogeneousTensorSynthesis (n + 1)
          (homogeneousTensorCoefficientVector (n + 1) Q))) = c
    rw [homogeneousTensorSynthesis_coefficients (n + 1) Q hQ, heq,
      homogeneousTensorCoefficientVector_synthesis]
  · rintro ⟨d, rfl⟩
    exact chartFiniteDirectional_cross_zero φ q hq s n d

end CharacteristicZero

section BaseChange

variable {A' : Type*} [CommRing A'] [Algebra K A']

/-- The actual cubic quotient-ring map induced by a chart coefficient map. -/
def chartCubicBaseChange (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    ChartCubicRing φ →+* ChartCubicRing (ψ.comp φ) :=
  cyclicBaseChangeHom ψ.toRingHom (φ (binaryCubic K))

/-- Coefficient extension is semilinear for the actual cyclic module action. -/
def chartModuleBaseChange (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure φ q hq s
    letI := chartDualModuleStructure (ψ.comp φ) q hq s
    (Fin 3 → A) →ₛₗ[chartCubicBaseChange φ ψ] (Fin 3 → A') := by
  letI := chartDualModuleStructure φ q hq s
  letI := chartDualModuleStructure (ψ.comp φ) q hq s
  exact cyclicModuleBaseChange ψ.toRingHom (φ (binaryCubic K))
    (cyclicVectorBaseChange ψ.toRingHom) (chartDualZ φ q s)
    (chartDualZ (ψ.comp φ) q s) (chartDualZ_cube φ q hq s)
    (chartDualZ_cube (ψ.comp φ) q hq s)
    (cyclicZDual_baseChange ψ.toRingHom (fun i => φ (profileFactors q s i)))

@[simp] theorem chartModuleBaseChange_apply
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (c : Fin 3 → A) (i : Fin 3) :
    chartModuleBaseChange φ ψ q hq s c i = ψ (c i) := rfl

/-- The finite coefficient map is pointwise coefficient extension over `K`. -/
def chartFiniteBaseChange (ψ : A →ₐ[K] A') (n : ℕ) :
    ChartFiniteVector A n →ₗ[K] ChartFiniteVector A' n where
  toFun c i j := ψ (c i j)
  map_add' c d := by funext i j; exact ψ.map_add _ _
  map_smul' k c := by funext i j; exact ψ.toLinearMap.map_smul k _

@[simp] theorem chartFiniteBaseChange_apply (ψ : A →ₐ[K] A')
    (n : ℕ) (c : ChartFiniteVector A n) (i : Sym (Fin 3) n) (j : Fin 3) :
    chartFiniteBaseChange ψ n c i j = ψ (c i j) := rfl

@[simp] theorem finiteCoefficient_chartModuleBaseChange
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (c : ChartFiniteVector A n) :
    letI := chartDualModuleStructure φ q hq s
    letI := chartDualModuleStructure (ψ.comp φ) q hq s
    finiteCoefficientBaseChange (chartModuleBaseChange φ ψ q hq s) n c =
      chartFiniteBaseChange ψ n c := by
  rfl

@[simp] theorem chartCubicBaseChange_U
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    chartCubicBaseChange φ ψ (chartU φ) = chartU (ψ.comp φ) :=
  cyclicBaseChangeHom_coefficient ψ.toRingHom (φ (binaryCubic K)) (φ (binaryU K))

@[simp] theorem chartCubicBaseChange_V
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    chartCubicBaseChange φ ψ (chartV φ) = chartV (ψ.comp φ) :=
  cyclicBaseChangeHom_coefficient ψ.toRingHom (φ (binaryCubic K)) (φ (binaryV K))

@[simp] theorem chartCubicBaseChange_Z
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    chartCubicBaseChange φ ψ (chartZ φ) = chartZ (ψ.comp φ) :=
  cyclicBaseChangeHom_root ψ.toRingHom (φ (binaryCubic K))

theorem chartCubicBaseChange_linearForm
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    (fun i => chartCubicBaseChange φ ψ (chartLinearForm φ i)) =
      chartLinearForm (ψ.comp φ) := by
  funext i
  fin_cases i <;> simp [chartLinearForm]

@[simp] theorem chartCubicBaseChange_crossMatrix
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A') :
    (chartCrossMatrix φ).map (chartCubicBaseChange φ ψ) =
      chartCrossMatrix (ψ.comp φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chartCrossMatrix, crossMatrix]

theorem chartFiniteCross_baseChange
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (c : ChartFiniteVector A n) :
    chartFiniteBaseChange ψ n (chartFiniteCross φ q hq s n c) =
      chartFiniteCross (ψ.comp φ) q hq s n (chartFiniteBaseChange ψ n c) := by
  let := chartDualModuleStructure φ q hq s
  let := chartDualModuleStructure (ψ.comp φ) q hq s
  simpa only [chartCubicBaseChange_crossMatrix, finiteCoefficient_chartModuleBaseChange,
    chartFiniteCross, LinearMap.restrictScalars_apply] using
    finiteCross_baseChange (chartModuleBaseChange φ ψ q hq s) (chartCrossMatrix φ) n c

theorem chartFiniteMultiply_baseChange
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (c : ChartFiniteVector A n) :
    chartFiniteBaseChange ψ (n + 1) (chartFiniteMultiply φ q hq s n c) =
      chartFiniteMultiply (ψ.comp φ) q hq s n (chartFiniteBaseChange ψ n c) := by
  let := chartDualModuleStructure φ q hq s
  let := chartDualModuleStructure (ψ.comp φ) q hq s
  simpa only [chartCubicBaseChange_linearForm, finiteCoefficient_chartModuleBaseChange,
    chartFiniteMultiply, LinearMap.restrictScalars_apply] using
    finiteMultiply_baseChange (chartModuleBaseChange φ ψ q hq s) (chartLinearForm φ) n c

theorem chartFiniteDirectional_baseChange
    (φ : BinaryRing K →ₐ[K] A) (ψ : A →ₐ[K] A')
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (c : ChartFiniteVector A (n + 1)) :
    chartFiniteBaseChange ψ n (chartFiniteDirectional φ q hq s n c) =
      chartFiniteDirectional (ψ.comp φ) q hq s n (chartFiniteBaseChange ψ (n + 1) c) := by
  let := chartDualModuleStructure φ q hq s
  let := chartDualModuleStructure (ψ.comp φ) q hq s
  simpa only [chartCubicBaseChange_linearForm, finiteCoefficient_chartModuleBaseChange,
    chartFiniteDirectional, LinearMap.restrictScalars_apply] using
    finiteDirectional_baseChange (chartModuleBaseChange φ ψ q hq s) (chartLinearForm φ) n c

end BaseChange
end ChoppedPlane.QWeyl
