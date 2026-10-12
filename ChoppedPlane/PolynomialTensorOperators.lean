module

public import ChoppedPlane.PolynomialOperatorDuality
public import ChoppedPlane.HomogeneousTensorCoordinates

@[expose] public section

/-!
# Actual tensor polynomial differential operators

Three coefficient-module maps act after the corresponding three partial
derivatives on genuine auxiliary polynomial tensors. Homogeneous coefficient
coordinates identify this map with the finite operator differential.
-/

noncomputable section
namespace ChoppedPlane
open Module MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {K : Type*} [Field K]
variable {V W : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- Apply each coefficient operator after its actual auxiliary derivative. -/
def operatorTensorDifferential (T : Fin 3 → V →ₗ[K] W) :
    AuxTensor (R := K) (M := V) →ₗ[K] AuxTensor (R := K) (M := W) :=
  ∑ i : Fin 3, TensorProduct.map (pderiv i).toLinearMap (T i)

@[simp] theorem operatorTensorDifferential_tmul
    (T : Fin 3 → V →ₗ[K] W) (f : Aux K) (v : V) :
    operatorTensorDifferential T (f ⊗ₜ[K] v) =
      ∑ i : Fin 3, pderiv i f ⊗ₜ[K] T i v := by
  simp [operatorTensorDifferential]

/-- The literal coefficient recurrence of the genuine tensor differential. -/
theorem operatorTensorDifferential_coeff
    (T : Fin 3 → V →ₗ[K] W) (P : AuxTensor (R := K) (M := V))
    (s : Fin 3 →₀ ℕ) :
    tensorCoefficients (operatorTensorDifferential T P) s =
      ∑ i : Fin 3, ((s i + 1 : ℕ) : K) •
        T i (tensorCoefficients P (s + Finsupp.single i 1)) := by
  induction P using TensorProduct.inductionOn with
  | tmul f v =>
    simp only [operatorTensorDifferential_tmul, map_sum, Finsupp.finsetSum_apply,
      tensorCoefficients_tmul, coeff_pderiv, map_smul]
    apply Finset.sum_congr rfl
    intro i _
    simp [smul_smul, mul_comm]
  | add P Q hP hQ =>
    simp only [map_add, Finsupp.add_apply, hP, hQ, smul_add,
      Finset.sum_add_distrib]

/-- An auxiliary degree-`t+1` tensor differentiates to auxiliary degree `t`. -/
theorem operatorTensorDifferential_homogeneous
    (T : Fin 3 → V →ₗ[K] W) {t : ℕ}
    (P : AuxTensor (R := K) (M := V)) (hP : TensorHomogeneous (t + 1) P) :
    TensorHomogeneous t (operatorTensorDifferential T P) := by
  apply (tensorHomogeneous_iff_coefficients t _).mpr
  intro s hs
  rw [operatorTensorDifferential_coeff]
  apply Finset.sum_eq_zero
  intro i _
  have hdegree : (s + Finsupp.single i 1).degree ≠ t + 1 := by
    simp only [map_add, Finsupp.degree_single]
    omega
  rw [(tensorHomogeneous_iff_coefficients (t + 1) P).mp hP
    (s + Finsupp.single i 1) hdegree, map_zero, smul_zero]

/-- Differentiating the synthesized monomials gives exactly the finite
coefficient operator, without assuming any freeness of the modules. -/
theorem operatorTensorDifferential_synthesis_coefficients
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) (x : Sym (Fin 3) (t + 1) → V) :
    homogeneousTensorCoefficientVector t
        (operatorTensorDifferential T (homogeneousTensorSynthesis (t + 1) x)) =
      operatorDifferential T t x := by
  funext s
  simp only [homogeneousTensorCoefficientVector, homogeneousTensorSynthesis,
    map_sum, operatorTensorDifferential_tmul, Finsupp.finsetSum_apply,
    tensorCoefficients_tmul, operatorDifferential_coeff]

/-- Synthesis intertwines the finite operator with the literal tensor map. -/
theorem operatorTensorDifferential_synthesis
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) (x : Sym (Fin 3) (t + 1) → V) :
    operatorTensorDifferential T (homogeneousTensorSynthesis (t + 1) x) =
      homogeneousTensorSynthesis t (operatorDifferential T t x) := by
  have hhom := operatorTensorDifferential_homogeneous T
    (homogeneousTensorSynthesis (t + 1) x)
    (homogeneousTensorSynthesis_homogeneous (t + 1) x)
  calc
    _ = homogeneousTensorSynthesis t (homogeneousTensorCoefficientVector t
        (operatorTensorDifferential T (homogeneousTensorSynthesis (t + 1) x))) :=
      (homogeneousTensorSynthesis_coefficients t _ hhom).symm
    _ = _ := by rw [operatorTensorDifferential_synthesis_coefficients]

/-- Restrict the actual tensor differential to its genuine homogeneous pieces. -/
def operatorHomogeneousTensorDifferential (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    homogeneousTensorSubmodule (R := K) (M := V) (t + 1) →ₗ[K]
      homogeneousTensorSubmodule (R := K) (M := W) t where
  toFun P := ⟨operatorTensorDifferential T P.val,
    operatorTensorDifferential_homogeneous T P.val P.property⟩
  map_add' P Q := Subtype.ext ((operatorTensorDifferential T).map_add P.val Q.val)
  map_smul' q P := Subtype.ext ((operatorTensorDifferential T).map_smul q P.val)

@[simp] theorem operatorHomogeneousTensorDifferential_val
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ)
    (P : homogeneousTensorSubmodule (R := K) (M := V) (t + 1)) :
    (operatorHomogeneousTensorDifferential T t P).val =
      operatorTensorDifferential T P.val := rfl

/-- The homogeneous coordinate equivalences preserve the actual tensor operator. -/
theorem operatorHomogeneousTensorDifferential_coordinates
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ)
    (P : homogeneousTensorSubmodule (R := K) (M := V) (t + 1)) :
    homogeneousTensorCoordinates t (operatorHomogeneousTensorDifferential T t P) =
      operatorDifferential T t (homogeneousTensorCoordinates (t + 1) P) := by
  change homogeneousTensorCoefficientVector t (operatorTensorDifferential T P.val) =
    operatorDifferential T t (homogeneousTensorCoefficientVector (t + 1) P.val)
  calc
    _ = homogeneousTensorCoefficientVector t (operatorTensorDifferential T
        (homogeneousTensorSynthesis (t + 1)
          (homogeneousTensorCoefficientVector (t + 1) P.val))) := by
      rw [homogeneousTensorSynthesis_coefficients (t + 1) P.val P.property]
    _ = _ := operatorTensorDifferential_synthesis_coefficients T t _

theorem operatorHomogeneousTensorDifferential_injective_iff
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    Function.Injective (operatorHomogeneousTensorDifferential T t) ↔
      Function.Injective (operatorDifferential T t) := by
  let S := homogeneousTensorCoordinates (R := K) (M := V) (t + 1)
  let E := homogeneousTensorCoordinates (R := K) (M := W) t
  have hcoord (P : homogeneousTensorSubmodule (R := K) (M := V) (t + 1)) :
      E (operatorHomogeneousTensorDifferential T t P) = operatorDifferential T t (S P) :=
    operatorHomogeneousTensorDifferential_coordinates T t P
  constructor
  · intro hF x y hxy
    obtain ⟨P, rfl⟩ := S.surjective x
    obtain ⟨Q, rfl⟩ := S.surjective y
    exact congrArg S (hF (E.injective (by rw [hcoord, hcoord]; exact hxy)))
  · intro hF P Q hPQ
    apply S.injective
    apply hF
    rw [← hcoord, ← hcoord, hPQ]

theorem operatorHomogeneousTensorDifferential_surjective_iff
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    Function.Surjective (operatorHomogeneousTensorDifferential T t) ↔
      Function.Surjective (operatorDifferential T t) := by
  let S := homogeneousTensorCoordinates (R := K) (M := V) (t + 1)
  let E := homogeneousTensorCoordinates (R := K) (M := W) t
  have hcoord (P : homogeneousTensorSubmodule (R := K) (M := V) (t + 1)) :
      E (operatorHomogeneousTensorDifferential T t P) = operatorDifferential T t (S P) :=
    operatorHomogeneousTensorDifferential_coordinates T t P
  constructor
  · intro hF y
    obtain ⟨Q, rfl⟩ := E.surjective y
    obtain ⟨P, hP⟩ := hF Q
    refine ⟨S P, ?_⟩
    rw [← hcoord, hP]
  · intro hF Q
    obtain ⟨x, hx⟩ := hF (E Q)
    obtain ⟨P, rfl⟩ := S.surjective x
    refine ⟨P, E.injective ?_⟩
    rw [hcoord, hx]

/-- Injectivity of the genuine tensor differential is surjectivity of the
actual transposed matrix of ternary linear forms. -/
theorem operatorHomogeneousTensorDifferential_injective_iff_linearMatrixMap_surjective
    [CharZero K] {a c : ℕ} (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    Function.Injective (operatorHomogeneousTensorDifferential T t) ↔
      Function.Surjective (linearMatrixMap (operatorLinearMatrix bV bW T) t) :=
  (operatorHomogeneousTensorDifferential_injective_iff T t).trans
    (operatorDifferential_injective_iff_linearMatrixMap_surjective bV bW T t)

/-- Surjectivity of the genuine tensor differential is injectivity of its
actual transposed matrix of ternary linear forms. -/
theorem operatorHomogeneousTensorDifferential_surjective_iff_linearMatrixMap_injective
    [CharZero K] {a c : ℕ} (bV : Basis (Fin a) K V) (bW : Basis (Fin c) K W)
    (T : Fin 3 → V →ₗ[K] W) (t : ℕ) :
    Function.Surjective (operatorHomogeneousTensorDifferential T t) ↔
      Function.Injective (linearMatrixMap (operatorLinearMatrix bV bW T) t) :=
  (operatorHomogeneousTensorDifferential_surjective_iff T t).trans
    (operatorDifferential_surjective_iff_linearMatrixMap_injective bV bW T t)

end ChoppedPlane
