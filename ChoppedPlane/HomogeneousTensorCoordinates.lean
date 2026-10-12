module

public import ChoppedPlane.SymmetricCoordinates
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.FixedSubmodule

@[expose] public section

/-!
Finite coordinates for an actual auxiliary-homogeneous tensor polynomial.
The coefficient module is arbitrary: neither freeness nor flatness is needed.
The inverse map synthesizes a finite sum of genuine coefficient-one monomials.
-/

noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Symmetric variable indices encode exactly the exponent vectors of degree `n`.
This equivalence depends on the indices alone, independently of the base ring. -/
def homogeneousTensorExponentEquiv (n : ℕ) :
    Sym (Fin 3) n ≃ {s : Fin 3 →₀ ℕ // s.degree = n} :=
  Sym.equivNatSum (Fin 3) n

/-- The exponent vector attached to one finite symmetric index. -/
def homogeneousTensorExponent (n : ℕ) (i : Sym (Fin 3) n) : Fin 3 →₀ ℕ :=
  (homogeneousTensorExponentEquiv n i).val

@[simp] theorem homogeneousTensorExponent_degree (n : ℕ) (i : Sym (Fin 3) n) :
    (homogeneousTensorExponent n i).degree = n :=
  (homogeneousTensorExponentEquiv n i).property

theorem homogeneousTensorExponent_injective (n : ℕ) :
    Function.Injective (homogeneousTensorExponent n) := by
  intro i j h
  apply (homogeneousTensorExponentEquiv n).injective
  exact Subtype.ext h

theorem exists_homogeneousTensorExponent (n : ℕ) (s : Fin 3 →₀ ℕ)
    (hs : s.degree = n) : ∃ i : Sym (Fin 3) n, homogeneousTensorExponent n i = s := by
  refine ⟨(homogeneousTensorExponentEquiv n).symm ⟨s,hs⟩, ?_⟩
  simp [homogeneousTensorExponent]

/-- The genuine submodule of tensors fixed by auxiliary degree-`n` extraction. -/
def homogeneousTensorSubmodule (n : ℕ) : Submodule R (AuxTensor (R := R) (M := M)) :=
  ((homogeneousComponent n).rTensor M).fixedSubmodule

@[simp] theorem mem_homogeneousTensorSubmodule (n : ℕ) (P : AuxTensor (R := R) (M := M)) :
    P ∈ homogeneousTensorSubmodule n ↔ TensorHomogeneous n P := Iff.rfl

/-- Read the finite degree-`n` coefficient vector from an actual tensor polynomial. -/
def homogeneousTensorCoefficientVector (n : ℕ) (P : AuxTensor (R := R) (M := M)) :
    Sym (Fin 3) n → M := fun i => tensorCoefficients P (homogeneousTensorExponent n i)

/-- Coefficient reading is an actual linear map on the full tensor module. -/
def homogeneousTensorCoefficientMap (n : ℕ) :
    AuxTensor (R := R) (M := M) →ₗ[R] (Sym (Fin 3) n → M) where
  toFun := homogeneousTensorCoefficientVector n
  map_add' P Q := by
    ext i
    simp [homogeneousTensorCoefficientVector]
  map_smul' r P := by
    ext i
    simp [homogeneousTensorCoefficientVector]

@[simp] theorem homogeneousTensorCoefficientVector_tmul (n : ℕ) (P : Aux R)
    (m : M) (i : Sym (Fin 3) n) :
    homogeneousTensorCoefficientVector n (P ⊗ₜ[R] m) i =
      P.coeff (homogeneousTensorExponent n i) • m := by
  simp [homogeneousTensorCoefficientVector]

/-- Synthesize a tensor polynomial by the finite sum of its homogeneous monomials. -/
def homogeneousTensorSynthesis (n : ℕ) (c : Sym (Fin 3) n → M) :
    AuxTensor (R := R) (M := M) :=
  ∑ i, monomial (homogeneousTensorExponent n i) 1 ⊗ₜ[R] c i

/-- Finite monomial synthesis is linear in the module coefficients. -/
def homogeneousTensorSynthesisMap (n : ℕ) :
    (Sym (Fin 3) n → M) →ₗ[R] AuxTensor (R := R) (M := M) where
  toFun := homogeneousTensorSynthesis n
  map_add' c d := by
    simp [homogeneousTensorSynthesis, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    simp [homogeneousTensorSynthesis, TensorProduct.tmul_smul, Finset.smul_sum]

/-- Each synthesized coefficient is exactly the coefficient supplied to it. -/
@[simp] theorem homogeneousTensorCoefficientVector_synthesis (n : ℕ)
    (c : Sym (Fin 3) n → M) :
    homogeneousTensorCoefficientVector n (homogeneousTensorSynthesis (R := R) n c) = c := by
  classical
  funext i
  simp only [homogeneousTensorCoefficientVector, homogeneousTensorSynthesis,
    map_sum, Finsupp.finsetSum_apply, tensorCoefficients_monomial, Finsupp.single_apply]
  simp only [(homogeneousTensorExponent_injective n).eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Synthesis lands in the actual auxiliary-homogeneous submodule. -/
theorem homogeneousTensorSynthesis_homogeneous (n : ℕ) (c : Sym (Fin 3) n → M) :
    TensorHomogeneous n (homogeneousTensorSynthesis (R := R) n c) := by
  apply (tensorHomogeneous_iff_coefficients n _).mpr
  intro s hs
  classical
  simp only [homogeneousTensorSynthesis, map_sum, Finsupp.finsetSum_apply,
    tensorCoefficients_monomial, Finsupp.single_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h : homogeneousTensorExponent n i ≠ s := by
    intro heq
    exact hs (heq ▸ homogeneousTensorExponent_degree n i)
  simp [h]

/-- Every homogeneous tensor is recovered by reading and synthesizing its coefficients. -/
theorem homogeneousTensorSynthesis_coefficients (n : ℕ)
    (P : AuxTensor (R := R) (M := M)) (hP : TensorHomogeneous n P) :
    homogeneousTensorSynthesis n (homogeneousTensorCoefficientVector n P) = P := by
  classical
  apply tensorCoefficients.injective
  ext s
  by_cases hs : s.degree = n
  · obtain ⟨i,rfl⟩ := exists_homogeneousTensorExponent n s hs
    exact congrFun (homogeneousTensorCoefficientVector_synthesis n
      (homogeneousTensorCoefficientVector n P)) i
  · rw [(tensorHomogeneous_iff_coefficients n _).mp
      (homogeneousTensorSynthesis_homogeneous n _) s hs,
      (tensorHomogeneous_iff_coefficients n _).mp hP s hs]

/-- The auxiliary degree-`n` submodule is the finite coefficient module indexed
by `Sym (Fin 3) n`, over any commutative ring and with arbitrary module coefficients. -/
def homogeneousTensorCoordinates (n : ℕ) :
    homogeneousTensorSubmodule (R := R) (M := M) n ≃ₗ[R] (Sym (Fin 3) n → M) where
  toFun P := homogeneousTensorCoefficientVector n P.val
  invFun c := ⟨homogeneousTensorSynthesis n c, homogeneousTensorSynthesis_homogeneous n c⟩
  left_inv P := Subtype.ext (homogeneousTensorSynthesis_coefficients n P.val P.property)
  right_inv := homogeneousTensorCoefficientVector_synthesis n
  map_add' P Q := (homogeneousTensorCoefficientMap n).map_add P.val Q.val
  map_smul' r P := (homogeneousTensorCoefficientMap n).map_smul r P.val

@[simp] theorem homogeneousTensorCoordinates_apply (n : ℕ)
    (P : homogeneousTensorSubmodule (R := R) (M := M) n) (i : Sym (Fin 3) n) :
    homogeneousTensorCoordinates n P i = tensorCoefficients P.val (homogeneousTensorExponent n i) := rfl

@[simp] theorem homogeneousTensorCoordinates_symm_val (n : ℕ) (c : Sym (Fin 3) n → M) :
    ((homogeneousTensorCoordinates (R := R) n).symm c).val =
      ∑ i, (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R] c i := rfl

end ChoppedPlane.SymmetricDerivative
