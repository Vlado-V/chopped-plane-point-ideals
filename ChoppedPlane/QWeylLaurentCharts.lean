module

public import ChoppedPlane.QWeylModule
public import ChoppedPlane.FiniteCechDuality

@[expose] public section

/-!
# Concrete cubic coefficient modules on binary coefficient charts

Every chart uses the actual cyclic cubic quotient and the literal transposed
cyclic action.  The unit-chart cross exactness statements are specialized to
these modules; the cubic relation and unit identities are verified here.
-/

noncomputable section
namespace ChoppedPlane.QWeyl
set_option maxHeartbeats 1000000

open MvPolynomial SymmetricDerivative FiniteCech

variable {K : Type*} [Field K]
variable {A : Type*} [CommRing A] [Algebra K A]

/-- The dual cyclic operator after a binary coefficient change. -/
def chartDualZ (φ : BinaryRing K →ₐ[K] A) (q : K) (s : CubicProfile) :
    Module.End A (Fin 3 → A) :=
  cyclicZDual (fun i => φ (profileFactors q s i))

theorem chartDualZ_cube (φ : BinaryRing K →ₐ[K] A) (q : K)
    (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    chartDualZ φ q s ^ 3 = φ (binaryCubic K) • 1 := by
  rw [chartDualZ, cyclicZDual_cube]
  congr 1
  rw [← map_mul, ← map_mul, profileFactors_product q hq s]

abbrev ChartCubicRing (φ : BinaryRing K →ₐ[K] A) :=
  CyclicCubicRing A (φ (binaryCubic K))

/-- The concrete coefficient module, with its quotient-ring action. -/
abbrev chartDualModuleStructure (φ : BinaryRing K →ₐ[K] A) (q : K)
    (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :=
  cyclicModuleStructure (φ (binaryCubic K)) (chartDualZ φ q s)
    (chartDualZ_cube φ q hq s)

def chartU (φ : BinaryRing K →ₐ[K] A) : ChartCubicRing φ :=
  cyclicCoefficientHom (φ (binaryCubic K)) (φ (binaryU K))

def chartV (φ : BinaryRing K →ₐ[K] A) : ChartCubicRing φ :=
  cyclicCoefficientHom (φ (binaryCubic K)) (φ (binaryV K))

def chartZ (φ : BinaryRing K →ₐ[K] A) : ChartCubicRing φ :=
  cyclicRoot (φ (binaryCubic K))

def chartCoefficient (φ : BinaryRing K →ₐ[K] A) (a : A) : ChartCubicRing φ :=
  cyclicCoefficientHom (φ (binaryCubic K)) a

theorem chartU_unit (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hu : φ (binaryU K) * a = 1) : chartU φ * chartCoefficient φ a = 1 := by
  change cyclicCoefficientHom _ _ * cyclicCoefficientHom _ _ = 1
  rw [← map_mul, hu, map_one]

theorem chartV_unit (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hv : φ (binaryV K) * a = 1) : chartV φ * chartCoefficient φ a = 1 := by
  change cyclicCoefficientHom _ _ * cyclicCoefficientHom _ _ = 1
  rw [← map_mul, hv, map_one]

/-- Actual coordinates for the `u` chart's cyclic quotient. -/
def chartCrossPresentationU (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hu : φ (binaryU K) * a = 1) :
    CrossPresentation (chartU φ) (chartV φ) (chartZ φ) :=
  crossPresentationU (chartU φ) (chartV φ) (chartZ φ)
    (chartCoefficient φ a) (chartU_unit φ a hu)

/-- Actual coordinates for the `v` chart's cyclic quotient. -/
def chartCrossPresentationV (φ : BinaryRing K →ₐ[K] A) (a : A)
    (hv : φ (binaryV K) * a = 1) :
    CrossPresentation (chartU φ) (chartV φ) (chartZ φ) :=
  crossPresentationV (chartU φ) (chartV φ) (chartZ φ)
    (chartCoefficient φ a) (chartV_unit φ a hv)

def chartLinearForm (φ : BinaryRing K →ₐ[K] A) : Fin 3 → ChartCubicRing φ :=
  ![chartU φ, chartV φ, chartZ φ]

def chartCrossMatrix (φ : BinaryRing K →ₐ[K] A) :
    Matrix (Fin 3) (Fin 3) (ChartCubicRing φ) :=
  crossMatrix (chartU φ) (chartV φ) (chartZ φ)

/-- The local cross quotient for the actual dual cyclic module, on `u`. -/
theorem chart_dual_cross_kernel_u
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hu : φ (binaryU K) * a = 1) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      tensorChange (chartCrossMatrix φ) P = 0 ↔
        P ∈ LinearMap.range (tensorMultiplyLinear (chartLinearForm φ)) := by
  let _ := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationU φ a hu).cross_kernel

/-- The same local exactness calculation on `v`. -/
theorem chart_dual_cross_kernel_v
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hv : φ (binaryV K) * a = 1) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      tensorChange (chartCrossMatrix φ) P = 0 ↔
        P ∈ LinearMap.range (tensorMultiplyLinear (chartLinearForm φ)) := by
  let _ := chartDualModuleStructure φ q hq s
  exact (chartCrossPresentationV φ a hv).cross_kernel

/-- Homogeneous local exactness for the actual cyclic module on `u`. -/
theorem chart_dual_cross_kernel_homogeneous_u
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous (n + 1) P → tensorChange (chartCrossMatrix φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorMultiplyLinear (chartLinearForm φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hcross
  exact (chartCrossPresentationU φ a hu).cross_kernel_homogeneous hP hcross

/-- Homogeneous local exactness for the actual cyclic module on `v`. -/
theorem chart_dual_cross_kernel_homogeneous_v
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous (n + 1) P → tensorChange (chartCrossMatrix φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorMultiplyLinear (chartLinearForm φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hcross
  exact (chartCrossPresentationV φ a hv).cross_kernel_homogeneous hP hcross

variable [CharZero K]

/-- Every homogeneous local derivative kernel has a cross representative. -/
theorem chart_dual_cross_range_homogeneous_u
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hu : φ (binaryU K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous n P → tensorDirectional (chartLinearForm φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorChange (chartCrossMatrix φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hdP
  exact (chartCrossPresentationU φ a hu).cross_range_homogeneous (K := K) hP hdP

theorem chart_dual_cross_range_homogeneous_v
    (φ : BinaryRing K →ₐ[K] A) (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (a : A) (hv : φ (binaryV K) * a = 1) (n : ℕ) :
    letI := chartDualModuleStructure φ q hq s
    ∀ P : AuxTensor (R := ChartCubicRing φ) (M := Fin 3 → A),
      TensorHomogeneous n P → tensorDirectional (chartLinearForm φ) P = 0 →
      ∃ Q, TensorHomogeneous n Q ∧ tensorChange (chartCrossMatrix φ) Q = P := by
  let _ := chartDualModuleStructure φ q hq s
  intro P hP hdP
  exact (chartCrossPresentationV φ a hv).cross_range_homogeneous (K := K) hP hdP

end ChoppedPlane.QWeyl
