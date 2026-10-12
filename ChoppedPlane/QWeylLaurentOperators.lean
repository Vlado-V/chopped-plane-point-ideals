module

public import ChoppedPlane.QWeylChartFiniteMaps
public import ChoppedPlane.QWeylLaurentGrading
public import ChoppedPlane.AuxiliaryCoefficientGrading

@[expose] public section

/-!
# Actual finite operators on free Laurent coefficients

The finite auxiliary coefficient vectors are flattened into the Laurent
coefficient model used by the two-chart complex.  All operators below are
conjugates of the actual cyclic-module tensor operators.
-/

noncomputable section
namespace ChoppedPlane.QWeyl

open LaurentPairing LaurentChartComplex FiniteCech SymmetricDerivative

variable {K : Type*} [Field K]
variable {S : Type*} [Finite S]

/-- Reorder a Laurent coefficient vector into auxiliary vectors of three coefficients. -/
def auxiliaryLaurentVectorEquiv :
    FreeLaurent K (Fin 3 × S) ≃ₗ[K] (S → Fin 3 → BinaryLaurent K) where
  toFun p j i := freeLaurentEquiv p (i,j)
  invFun c := freeLaurentEquiv.symm (fun ij => c ij.2 ij.1)
  left_inv p := by apply freeLaurentEquiv.injective; simp
  right_inv c := by funext j i; simp
  map_add' p q := by funext j i; simp
  map_smul' a p := by funext j i; simp

@[simp] theorem auxiliaryLaurentVectorEquiv_apply
    (p : FreeLaurent K (Fin 3 × S)) (j : S) (i : Fin 3) :
    auxiliaryLaurentVectorEquiv p j i = freeLaurentEquiv p (i,j) := rfl

@[simp] theorem auxiliaryLaurentVectorEquiv_coeff
    (p : FreeLaurent K (Fin 3 × S)) (j : S) (i : Fin 3) (e : ℤ × ℤ) :
    (auxiliaryLaurentVectorEquiv p j i).coeff e = p ((i,j),e) := by
  exact freeLaurentEquiv_coeff p (i,j) e

@[simp] theorem auxiliaryLaurentVectorEquiv_component_coeff
    (p : FreeLaurent K (Fin 3 × S)) (j : S) (i : Fin 3) (e : ℤ × ℤ) :
    freeLaurentEquiv.symm (auxiliaryLaurentVectorEquiv p j) (i,e) = p ((i,j),e) := by
  rw [← freeLaurentEquiv_coeff _ i e, LinearEquiv.apply_symm_apply]
  exact auxiliaryLaurentVectorEquiv_coeff p j i e

/-- Every actual component support condition is preserved by flattening. -/
theorem auxiliaryLaurentVectorEquiv_supported_iff
    (P : Fin 3 → (ℤ × ℤ) → Prop) (p : FreeLaurent K (Fin 3 × S)) :
    p ∈ Finsupp.supported K K {e | P e.1.1 e.2} ↔
      ∀ j : S, freeLaurentEquiv.symm (auxiliaryLaurentVectorEquiv p j) ∈
        Finsupp.supported K K {e | P e.1 e.2} := by
  simp only [Finsupp.mem_supported']
  constructor
  · intro hp j e he
    rw [auxiliaryLaurentVectorEquiv_component_coeff]
    exact hp ((e.1,j),e.2) he
  · intro hp e he
    rw [← auxiliaryLaurentVectorEquiv_component_coeff p e.1.2 e.1.1 e.2]
    exact hp e.1.2 (e.1.1,e.2) he

/-- Flattening of the actual overlap homogeneous component. -/
theorem auxiliaryLaurentVectorEquiv_overlap_iff
    (g : Fin 3 → ℤ) (k : ℤ) (p : FreeLaurent K (Fin 3 × S)) :
    p ∈ overlapGrade (fun i => g i.1) k ↔
      ∀ j : S, auxiliaryLaurentVectorEquiv p j ∈ vectorOverlapGrade g k :=
  auxiliaryLaurentVectorEquiv_supported_iff (fun i e => e.1 + e.2 + g i = k) p

/-- Flattening of the actual `u`-chart homogeneous component. -/
theorem auxiliaryLaurentVectorEquiv_uChart_iff
    (g : Fin 3 → ℤ) (k : ℤ) (p : FreeLaurent K (Fin 3 × S)) :
    p ∈ uChartGrade (fun i => g i.1) k ↔
      ∀ j : S, auxiliaryLaurentVectorEquiv p j ∈ vectorUChartGrade g k :=
  auxiliaryLaurentVectorEquiv_supported_iff
    (fun i e => (e.1 + e.2 + g i = k) ∧ 0 ≤ e.2) p

/-- Flattening of the actual `v`-chart homogeneous component. -/
theorem auxiliaryLaurentVectorEquiv_vChart_iff
    (g : Fin 3 → ℤ) (k : ℤ) (p : FreeLaurent K (Fin 3 × S)) :
    p ∈ vChartGrade (fun i => g i.1) k ↔
      ∀ j : S, auxiliaryLaurentVectorEquiv p j ∈ vectorVChartGrade g k :=
  auxiliaryLaurentVectorEquiv_supported_iff
    (fun i e => (e.1 + e.2 + g i = k) ∧ 0 ≤ e.1) p

/-- The generator weights of the flattened dual module. -/
def auxiliaryDualWeights (s : CubicProfile) (n : ℕ) : Fin 3 × Sym (Fin 3) n → ℤ :=
  fun i => (dualGeneratorWeights s i.1 : ℤ)

/-- The actual cross substitution on flattened overlap Laurent coefficients. -/
def profileLaurentCross (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    FreeLaurent K (Fin 3 × Sym (Fin 3) n) →ₗ[K]
      FreeLaurent K (Fin 3 × Sym (Fin 3) n) :=
  auxiliaryLaurentVectorEquiv.symm.toLinearMap.comp
    ((chartFiniteCross binaryChartLaurentMap q hq s n).comp
      auxiliaryLaurentVectorEquiv.toLinearMap)

/-- The actual linear-form multiplication on flattened overlap coefficients. -/
def profileLaurentMultiply (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :
    FreeLaurent K (Fin 3 × Sym (Fin 3) n) →ₗ[K]
      FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)) :=
  auxiliaryLaurentVectorEquiv.symm.toLinearMap.comp
    ((chartFiniteMultiply binaryChartLaurentMap q hq s n).comp
      auxiliaryLaurentVectorEquiv.toLinearMap)

/-- The actual directional differentiation on flattened overlap coefficients. -/
def profileLaurentDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :
    FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)) →ₗ[K]
      FreeLaurent K (Fin 3 × Sym (Fin 3) n) :=
  auxiliaryLaurentVectorEquiv.symm.toLinearMap.comp
    ((chartFiniteDirectional binaryChartLaurentMap q hq s n).comp
      auxiliaryLaurentVectorEquiv.toLinearMap)

@[simp] theorem auxiliaryLaurentVectorEquiv_profileLaurentCross
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n)) :
    auxiliaryLaurentVectorEquiv (profileLaurentCross q hq s n p) =
      chartFiniteCross binaryChartLaurentMap q hq s n (auxiliaryLaurentVectorEquiv p) := by
  simp [profileLaurentCross]

@[simp] theorem auxiliaryLaurentVectorEquiv_profileLaurentMultiply
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n)) :
    auxiliaryLaurentVectorEquiv (profileLaurentMultiply q hq s n p) =
      chartFiniteMultiply binaryChartLaurentMap q hq s n (auxiliaryLaurentVectorEquiv p) := by
  simp [profileLaurentMultiply]

@[simp] theorem auxiliaryLaurentVectorEquiv_profileLaurentDirectional
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1))) :
    auxiliaryLaurentVectorEquiv (profileLaurentDirectional q hq s n p) =
      chartFiniteDirectional binaryChartLaurentMap q hq s n (auxiliaryLaurentVectorEquiv p) := by
  simp [profileLaurentDirectional]

end ChoppedPlane.QWeyl
