module

public import ChoppedPlane.FiniteCechDuality
public import ChoppedPlane.HomogeneousTensorCoordinates
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

@[expose] public section

/-!
# The actual finite auxiliary coefficient maps

These maps are coefficient forms of tensor multiplication, directional
differentiation and the cross substitution, indexed by finite symmetric
powers.  Their exactness comes from the explicit unit-chart calculations.
-/

noncomputable section
namespace ChoppedPlane.FiniteCech

open MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

lemma tensorHomogeneous_tmul {n : ℕ} {P : Aux R} (hP : P.IsHomogeneous n) (m : M) :
    TensorHomogeneous n (P ⊗ₜ[R] m) := by
  change ((homogeneousComponent n).rTensor M) (P ⊗ₜ[R] m) = _
  simp only [LinearMap.rTensor_tmul, homogeneousComponent_eq_self hP]

lemma tensorHomogeneous_sum {ι : Type*} (s : Finset ι)
    {n : ℕ} (P : ι → AuxTensor (R := R) (M := M))
    (hP : ∀ i ∈ s, TensorHomogeneous n (P i)) : TensorHomogeneous n (∑ i ∈ s, P i) := by
  change ((homogeneousComponent n).rTensor M) _ = _
  simp only [map_sum]
  exact Finset.sum_congr rfl hP

/-- Auxiliary multiplication increases the homogeneous auxiliary degree by one. -/
theorem tensorMultiplyLinear_homogeneous (f : Fin 3 → R) {n : ℕ}
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous n P) :
    TensorHomogeneous (n + 1) (tensorMultiplyLinear f P) := by
  rw [← homogeneousTensorSynthesis_coefficients n P hP]
  change TensorHomogeneous (n + 1)
    (((LinearMap.mulLeft R (linearForm f)).rTensor M) (∑ i,
      (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R]
        homogeneousTensorCoefficientVector n P i))
  rw [map_sum]
  apply tensorHomogeneous_sum
  intro i hi
  rw [LinearMap.rTensor_tmul]
  apply tensorHomogeneous_tmul
  simpa [Nat.add_comm] using (linearForm_homogeneous f).mul
    (isHomogeneous_monomial (1 : R) (homogeneousTensorExponent_degree n i))

lemma directional_homogeneous (f : Fin 3 → R) {n : ℕ}
    {P : Aux R} (hP : P.IsHomogeneous (n + 1)) :
    (directional f P).IsHomogeneous n := by
  rw [directional_eq_sum]
  change (∑ i : Fin 3, f i • pderiv i P).IsHomogeneous n
  apply IsHomogeneous.sum
  intro i hi
  apply (mem_homogeneousSubmodule n _).mp
  apply (homogeneousSubmodule (Fin 3) R n).smul_mem
  apply (mem_homogeneousSubmodule n _).mpr
  simpa using hP.pderiv (i := i)

/-- Directional differentiation decreases auxiliary degree by one. -/
theorem tensorDirectional_homogeneous (f : Fin 3 → R) {n : ℕ}
    {P : AuxTensor (R := R) (M := M)} (hP : TensorHomogeneous (n + 1) P) :
    TensorHomogeneous n (tensorDirectional f P) := by
  rw [← homogeneousTensorSynthesis_coefficients (n + 1) P hP]
  change TensorHomogeneous n
    ((directional f).toLinearMap.rTensor M (∑ i,
      (monomial (homogeneousTensorExponent (n + 1) i) 1 : Aux R) ⊗ₜ[R]
        homogeneousTensorCoefficientVector (n + 1) P i))
  rw [map_sum]
  apply tensorHomogeneous_sum
  intro i hi
  rw [LinearMap.rTensor_tmul]
  apply tensorHomogeneous_tmul
  exact directional_homogeneous f
    (isHomogeneous_monomial (1 : R) (homogeneousTensorExponent_degree (n + 1) i))

/-- Finite coefficient form of homogeneous cross substitution. -/
def finiteCross (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ) :
    (Sym (Fin 3) n → M) →ₗ[R] (Sym (Fin 3) n → M) :=
  (homogeneousTensorCoefficientMap n).comp
    ((tensorChange A).comp (homogeneousTensorSynthesisMap n))

/-- Finite coefficient form of multiplication by the actual auxiliary linear form. -/
def finiteMultiply (f : Fin 3 → R) (n : ℕ) :
    (Sym (Fin 3) n → M) →ₗ[R] (Sym (Fin 3) (n + 1) → M) :=
  (homogeneousTensorCoefficientMap (n + 1)).comp
    ((tensorMultiplyLinear f).comp (homogeneousTensorSynthesisMap n))

/-- Finite coefficient form of directional differentiation. -/
def finiteDirectional (f : Fin 3 → R) (n : ℕ) :
    (Sym (Fin 3) (n + 1) → M) →ₗ[R] (Sym (Fin 3) n → M) :=
  (homogeneousTensorCoefficientMap n).comp
    ((tensorDirectional f).comp (homogeneousTensorSynthesisMap (n + 1)))

@[simp] theorem synthesis_finiteCross (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ)
    (c : Sym (Fin 3) n → M) :
    homogeneousTensorSynthesis n (finiteCross A n c) =
      tensorChange A (homogeneousTensorSynthesis n c) := by
  exact homogeneousTensorSynthesis_coefficients n _
    (tensorChange_homogeneous A (homogeneousTensorSynthesis_homogeneous n c))

@[simp] theorem synthesis_finiteMultiply (f : Fin 3 → R) (n : ℕ)
    (c : Sym (Fin 3) n → M) :
    homogeneousTensorSynthesis (n + 1) (finiteMultiply f n c) =
      tensorMultiplyLinear f (homogeneousTensorSynthesis n c) := by
  exact homogeneousTensorSynthesis_coefficients (n + 1) _
    (tensorMultiplyLinear_homogeneous f (homogeneousTensorSynthesis_homogeneous n c))

@[simp] theorem synthesis_finiteDirectional (f : Fin 3 → R) (n : ℕ)
    (c : Sym (Fin 3) (n + 1) → M) :
    homogeneousTensorSynthesis n (finiteDirectional f n c) =
      tensorDirectional f (homogeneousTensorSynthesis (n + 1) c) := by
  exact homogeneousTensorSynthesis_coefficients n _
    (tensorDirectional_homogeneous f (homogeneousTensorSynthesis_homogeneous (n + 1) c))

/-- Each finite cross entry is the literal coefficient of the substituted monomial. -/
theorem finiteCross_apply (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ)
    (c : Sym (Fin 3) n → M) (j : Sym (Fin 3) n) :
    finiteCross A n c j = ∑ i : Sym (Fin 3) n,
      (linearChange A (monomial (homogeneousTensorExponent n i) 1)).coeff
        (homogeneousTensorExponent n j) • c i := by
  change tensorCoefficients (((linearChange A).toLinearMap.rTensor M)
    (∑ i, (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R] c i))
      (homogeneousTensorExponent n j) = _
  simp only [map_sum, LinearMap.rTensor_tmul, Finsupp.finsetSum_apply,
    tensorCoefficients_tmul, AlgHom.toLinearMap_apply]

/-- Multiplication coefficients on the full module-valued polynomial. -/
theorem tensorCoefficients_multiplyLinear (f : Fin 3 → R)
    (P : AuxTensor (R := R) (M := M)) (s : Fin 3 →₀ ℕ) :
    tensorCoefficients (tensorMultiplyLinear f P) s =
      ∑ i : Fin 3, if i ∈ s.support then
        f i • tensorCoefficients P (s - Finsupp.single i 1) else 0 := by
  classical
  induction P using TensorProduct.inductionOn with
  | tmul Q m =>
    simp only [tensorMultiplyLinear, LinearMap.rTensor_tmul, LinearMap.mulLeft_apply,
      tensorCoefficients_tmul, linearForm, Finset.sum_mul, coeff_sum,
      mul_assoc, coeff_C_mul, coeff_X_mul', Finset.sum_smul, mul_smul]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  | add P Q hP hQ =>
    simp only [map_add, Finsupp.add_apply, hP, hQ]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp [smul_add]

namespace CrossPresentation

variable {u v z : R} (T : CrossPresentation u v z)
include T

/-- Exactness on the actual finite coefficient vectors of auxiliary degree `n+1`. -/
theorem finite_cross_kernel (n : ℕ) (c : Sym (Fin 3) (n + 1) → M) :
    finiteCross (crossMatrix u v z) (n + 1) c = 0 ↔
      c ∈ LinearMap.range (finiteMultiply ![u,v,z] n) := by
  constructor
  · intro hc
    have hcross : tensorChange (crossMatrix u v z)
        (homogeneousTensorSynthesis (n + 1) c) = 0 := by
      rw [← synthesis_finiteCross, hc]
      exact (homogeneousTensorSynthesisMap (n + 1)).map_zero
    obtain ⟨Q,hQ,heq⟩ := T.cross_kernel_homogeneous
      (homogeneousTensorSynthesis_homogeneous (n + 1) c) hcross
    refine ⟨homogeneousTensorCoefficientVector n Q, ?_⟩
    change homogeneousTensorCoefficientVector (n + 1)
      (tensorMultiplyLinear ![u,v,z]
        (homogeneousTensorSynthesis n (homogeneousTensorCoefficientVector n Q))) = c
    rw [homogeneousTensorSynthesis_coefficients n Q hQ, heq,
      homogeneousTensorCoefficientVector_synthesis]
  · rintro ⟨d,rfl⟩
    change homogeneousTensorCoefficientVector (n + 1)
      (tensorChange (crossMatrix u v z)
        (homogeneousTensorSynthesis (n + 1) (finiteMultiply ![u,v,z] n d))) = 0
    rw [synthesis_finiteMultiply]
    have hcross := (T.cross_kernel (tensorMultiplyLinear ![u,v,z]
      (homogeneousTensorSynthesis n d))).mpr
      ⟨homogeneousTensorSynthesis n d, rfl⟩
    rw [hcross]
    exact (homogeneousTensorCoefficientMap (n + 1)).map_zero

/-- Finite linear-form multiplication is injective on a unit chart. -/
theorem finiteMultiply_injective (n : ℕ) :
    Function.Injective (finiteMultiply (M := M) ![u,v,z] n) := by
  intro c d h
  have ht := congrArg (homogeneousTensorSynthesis (R := R) (n + 1)) h
  rw [synthesis_finiteMultiply, synthesis_finiteMultiply] at ht
  have hc := T.multiply_injective ht
  simpa using congrArg (homogeneousTensorCoefficientVector (R := R) n) hc

end CrossPresentation
end ChoppedPlane.FiniteCech
