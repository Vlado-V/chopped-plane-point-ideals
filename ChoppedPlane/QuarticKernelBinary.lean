module

public import ChoppedPlane.QuarticKernelGlobal

@[expose] public section

/-! The global quartic symmetric-kernel theorem specialized to the literal
cyclic binary coefficient modules, including their dual actions. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
variable {K : Type*} [Field K] [CharZero K]

/-- Both transpose choices are genuine cubic-ring coefficient modules. -/
def quarticCyclicZ {A : Type*} [CommRing A] (dual : Bool) (γ : Fin 3 → A) :
    End A (Fin 3 → A) := if dual then cyclicZDual γ else cyclicZ γ

theorem quarticCyclicZ_cube {A : Type*} [CommRing A]
    (dual : Bool) (γ : Fin 3 → A) :
    quarticCyclicZ dual γ ^ 3 = (γ 0 * γ 1 * γ 2) • 1 := by
  cases dual
  · exact cyclicZ_cube γ
  · exact cyclicZDual_cube γ

theorem quarticCyclicZ_baseChange {A A' : Type*} [CommRing A] [CommRing A']
    (φ : A →+* A') (dual : Bool) (γ : Fin 3 → A) (m : Fin 3 → A) :
    cyclicVectorBaseChange φ (quarticCyclicZ dual γ m) =
      quarticCyclicZ dual (fun i => φ (γ i)) (cyclicVectorBaseChange φ m) := by
  cases dual
  · exact cyclicZ_baseChange φ γ m
  · exact cyclicZDual_baseChange φ γ m

theorem quarticU_binary_ne_zero :
    quarticU (binaryU K) (binaryV K) ≠ 0 := by
  intro h
  have he := congrArg (eval ![1,0]) h
  simp [quarticU, binaryU, binaryV] at he

theorem quarticV_binary_ne_zero :
    quarticV (binaryU K) (binaryV K) ≠ 0 := by
  intro h
  have he := congrArg (eval ![0,1]) h
  simp [quarticV, binaryU, binaryV] at he

/-- The two inverse charts descend every coefficient in all six actual
cyclic modules. This is a polynomial statement, with no assumed local
kernel or integrality certificates. -/
theorem quartic_cyclic_kernel_descends (dual : Bool) (γ : Fin 3 → BinaryRing K)
    (hγ : γ 0 * γ 1 * γ 2 = binaryCubic K) :
    let Z := quarticCyclicZ dual γ
    let hZ : Z ^ 3 = binaryCubic K • 1 := (quarticCyclicZ_cube dual γ).trans (by rw [hγ])
    let := cyclicModuleStructure (binaryCubic K) Z hZ
    ∀ {n : ℕ} (P : AuxTensor (R := CyclicCubicRing (BinaryRing K) (binaryCubic K))
        (M := BinaryVector K)), TensorHomogeneous n P →
      tensorDirectional (quarticRow
        (cyclicCoefficientHom (binaryCubic K) (binaryU K))
        (cyclicCoefficientHom (binaryCubic K) (binaryV K))
        (cyclicRoot (binaryCubic K))) P = 0 →
      ∃ c : Fin (n + 1) → BinaryVector K,
        kernelSynthesis (quarticKernelMatrixU
          (cyclicCoefficientHom (binaryCubic K) (binaryU K))
          (cyclicCoefficientHom (binaryCubic K) (binaryV K))
          (cyclicRoot (binaryCubic K)) 0) n c = P := by
  dsimp only
  let B := BinaryRing K
  let F := FractionRing B
  let φ : B →+* F := algebraMap B F
  let Z := quarticCyclicZ dual γ
  let Z' := quarticCyclicZ dual (fun i => φ (γ i))
  have hZ : Z ^ 3 = binaryCubic K • 1 :=
    (quarticCyclicZ_cube dual γ).trans (by rw [hγ])
  have hZ' : Z' ^ 3 = φ (binaryCubic K) • 1 := by
    rw [quarticCyclicZ_cube]
    congr 1
    rw [← map_mul, ← map_mul, hγ]
  let := cyclicModuleStructure (binaryCubic K) Z hZ
  intro n P hP hδ
  exact quartic_kernel_descends (K := F) (F := F)
    (binaryU K) (binaryV K) Z Z' hZ hZ'
    (quarticCyclicZ_baseChange φ dual γ)
    quarticU_binary_ne_zero quarticV_binary_ne_zero quartic_binary_relPrime P hP hδ

end ChoppedPlane.QWeyl
