module

public import ChoppedPlane.FiniteAuxiliaryMaps

@[expose] public section

/-!
# Coefficient grading of the finite cross substitution

Only the coefficient-module grading is used.  Each entry of the cross row
acts in degree one, so a substituted auxiliary monomial of degree `n` acts
in coefficient degree `n`.  This argument works for Laurent coefficient
modules without choosing bases in the cubic quotient ring.
-/

noncomputable section
namespace ChoppedPlane.FiniteCech

open MvPolynomial SymmetricDerivative
open scoped TensorProduct
variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Every coefficient belongs to one fixed additive homogeneous component. -/
def CoefficientGrade (G : ℤ → AddSubgroup M) (k : ℤ)
    (P : AuxTensor (R := R) (M := M)) : Prop :=
  ∀ s : Fin 3 →₀ ℕ, tensorCoefficients P s ∈ G k

lemma coefficientGrade_zero (G : ℤ → AddSubgroup M) (k : ℤ) :
    CoefficientGrade G k (0 : AuxTensor (R := R) (M := M)) := by
  intro s
  simp only [map_zero, Finsupp.zero_apply]
  exact (G k).zero_mem

lemma coefficientGrade_sum {ι : Type*} (G : ℤ → AddSubgroup M) (k : ℤ)
    (s : Finset ι) (P : ι → AuxTensor (R := R) (M := M))
    (hP : ∀ i ∈ s, CoefficientGrade G k (P i)) :
    CoefficientGrade G k (∑ i ∈ s, P i) := by
  intro e
  simp only [map_sum, Finsupp.finsetSum_apply]
  exact (G k).sum_mem fun i hi => hP i hi e

lemma coefficientGrade_constant (G : ℤ → AddSubgroup M) (k : ℤ)
    (m : M) (hm : m ∈ G k) :
    CoefficientGrade G k ((monomial 0 1 : Aux R) ⊗ₜ[R] m) := by
  intro s
  rw [tensorCoefficients_monomial]
  by_cases hs : (0 : Fin 3 →₀ ℕ) = s
  · subst s
    simpa using hm
  · simp only [Finsupp.single_apply, ite_eq_right hs]
    exact (G k).zero_mem

/-- Multiplication by a row whose entries act in degree one raises coefficient degree one. -/
theorem coefficientGrade_multiplyLinear (G : ℤ → AddSubgroup M)
    (f : Fin 3 → R)
    (hf : ∀ k i m, m ∈ G k → f i • m ∈ G (k + 1))
    (k : ℤ) {P : AuxTensor (R := R) (M := M)} (hP : CoefficientGrade G k P) :
    CoefficientGrade G (k + 1) (tensorMultiplyLinear f P) := by
  intro s
  rw [tensorCoefficients_multiplyLinear]
  apply (G (k + 1)).sum_mem
  intro i hi
  split_ifs
  · exact hf k i _ (hP _)
  · exact (G (k + 1)).zero_mem

/-- Iterated multiplication is the ordinary power of the linear form. -/
lemma tensorMultiplyLinear_iterate_tmul (f : Fin 3 → R) (d : ℕ)
    (P : Aux R) (m : M) :
    (tensorMultiplyLinear f)^[d] (P ⊗ₜ[R] m) =
      (linearForm f ^ d * P) ⊗ₜ[R] m := by
  induction d with
  | zero => simp
  | succ d hd =>
    rw [Function.iterate_succ_apply', hd]
    change (linearForm f * (linearForm f ^ d * P)) ⊗ₜ[R] m = _
    apply congrArg (fun Q : Aux R => Q ⊗ₜ[R] m)
    rw [pow_succ]
    ring

lemma coefficientGrade_multiplyLinear_iterate (G : ℤ → AddSubgroup M)
    (f : Fin 3 → R)
    (hf : ∀ k i m, m ∈ G k → f i • m ∈ G (k + 1))
    (k : ℤ) (d : ℕ) {P : AuxTensor (R := R) (M := M)}
    (hP : CoefficientGrade G k P) :
    CoefficientGrade G (k + d) ((tensorMultiplyLinear f)^[d] P) := by
  induction d with
  | zero => simpa using hP
  | succ d hd =>
    rw [Function.iterate_succ_apply']
    convert coefficientGrade_multiplyLinear G f hf (k + d) hd using 1
    omega

/-- A substituted monomial acts on coefficients in its auxiliary degree. -/
theorem coefficientGrade_change_monomial (G : ℤ → AddSubgroup M)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ k i j m, m ∈ G k → A i j • m ∈ G (k + 1))
    (k : ℤ) (s : Fin 3 →₀ ℕ) (m : M) (hm : m ∈ G k) :
    CoefficientGrade G (k + s.degree)
      (linearChange A (monomial s 1) ⊗ₜ[R] m) := by
  classical
  induction s using Finsupp.induction with
  | zero =>
    simpa using coefficientGrade_constant G k m hm
  | @single_add i d s hi hd ih =>
    have heq : linearChange A (monomial (Finsupp.single i d + s) 1) ⊗ₜ[R] m =
        (tensorMultiplyLinear (A i))^[d]
          (linearChange A (monomial s 1) ⊗ₜ[R] m) := by
      rw [tensorMultiplyLinear_iterate_tmul]
      congr 1
      rw [add_comm (Finsupp.single i d) s, monomial_add_single, map_mul,
        map_pow, linearChange_X, mul_comm]
    rw [heq]
    have h := coefficientGrade_multiplyLinear_iterate G (A i)
      (fun k j m hm => hA k i j m hm) (k + s.degree) d ih
    convert h using 1
    simp only [map_add, Finsupp.degree_single, Nat.cast_add]
    omega

/-- Synthesis of a fixed-degree coefficient vector preserves its coefficient component. -/
theorem coefficientGrade_synthesis (G : ℤ → AddSubgroup M) (k : ℤ) (n : ℕ)
    (c : Sym (Fin 3) n → M) (hc : ∀ i, c i ∈ G k) :
    CoefficientGrade G k (homogeneousTensorSynthesis (R := R) n c) := by
  intro s
  change tensorCoefficients
    (∑ i, (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R] c i) s ∈ _
  simp only [map_sum, Finsupp.finsetSum_apply, tensorCoefficients_monomial]
  apply (G k).sum_mem
  intro i hi
  by_cases heq : homogeneousTensorExponent n i = s
  · simp only [Finsupp.single_apply, heq, ite_true]
    exact hc i
  · simp only [Finsupp.single_apply, ite_eq_right heq]
    exact (G k).zero_mem

/-- Finite linear-form multiplication raises coefficient degree by one. -/
theorem finiteMultiply_mem_coefficientGrade (G : ℤ → AddSubgroup M)
    (f : Fin 3 → R)
    (hf : ∀ k i m, m ∈ G k → f i • m ∈ G (k + 1))
    (k : ℤ) (n : ℕ) (c : Sym (Fin 3) n → M) (hc : ∀ i, c i ∈ G k) :
    ∀ j, finiteMultiply f n c j ∈ G (k + 1) :=
  fun j => coefficientGrade_multiplyLinear G f hf k
    (coefficientGrade_synthesis G k n c hc) (homogeneousTensorExponent (n + 1) j)

/-- Directional differentiation also raises coefficient degree by one. -/
theorem coefficientGrade_directional (G : ℤ → AddSubgroup M)
    (f : Fin 3 → R)
    (hf : ∀ k i m, m ∈ G k → f i • m ∈ G (k + 1))
    (k : ℤ) {P : AuxTensor (R := R) (M := M)} (hP : CoefficientGrade G k P) :
    CoefficientGrade G (k + 1) (tensorDirectional f P) := by
  intro s
  rw [tensorCoefficients_directional]
  apply (G (k + 1)).sum_mem
  intro i hi
  rw [mul_smul, Nat.cast_smul_eq_nsmul]
  exact hf k i _ ((G k).nsmul_mem (hP _) (s i + 1))

/-- The finite directional map raises coefficient degree by one. -/
theorem finiteDirectional_mem_coefficientGrade (G : ℤ → AddSubgroup M)
    (f : Fin 3 → R)
    (hf : ∀ k i m, m ∈ G k → f i • m ∈ G (k + 1))
    (k : ℤ) (n : ℕ) (c : Sym (Fin 3) (n + 1) → M) (hc : ∀ i, c i ∈ G k) :
    ∀ j, finiteDirectional f n c j ∈ G (k + 1) :=
  fun j => coefficientGrade_directional G f hf k
    (coefficientGrade_synthesis G k (n + 1) c hc) (homogeneousTensorExponent n j)

/-- The finite cross map raises coefficient degree by the fixed auxiliary degree. -/
theorem finiteCross_mem_coefficientGrade (G : ℤ → AddSubgroup M)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ k i j m, m ∈ G k → A i j • m ∈ G (k + 1))
    (k : ℤ) (n : ℕ) (c : Sym (Fin 3) n → M) (hc : ∀ i, c i ∈ G k) :
    ∀ j, finiteCross A n c j ∈ G (k + n) := by
  have hsum : CoefficientGrade G (k + n)
      (tensorChange A (homogeneousTensorSynthesis n c)) := by
    change CoefficientGrade G (k + n)
      (((linearChange A).toLinearMap.rTensor M)
        (∑ i, (monomial (homogeneousTensorExponent n i) 1 : Aux R) ⊗ₜ[R] c i))
    rw [map_sum]
    apply coefficientGrade_sum
    intro i hi
    rw [LinearMap.rTensor_tmul]
    simpa only [AlgHom.toLinearMap_apply, homogeneousTensorExponent_degree] using
      coefficientGrade_change_monomial G A hA k
        (homogeneousTensorExponent n i) (c i) (hc i)
  exact fun j => hsum (homogeneousTensorExponent n j)

/-- The cross matrix inherits degree-one action from its three coefficients. -/
theorem crossMatrix_degree_one (G : ℤ → AddSubgroup M) (u v z : R)
    (hf : ∀ k i m, m ∈ G k → (![u,v,z] : Fin 3 → R) i • m ∈ G (k + 1)) :
    ∀ k i j m, m ∈ G k → crossMatrix u v z i j • m ∈ G (k + 1) := by
  intro k i j m hm
  have hu : u • m ∈ G (k + 1) := by simpa using hf k 0 m hm
  have hv : v • m ∈ G (k + 1) := by simpa using hf k 1 m hm
  have hz : z • m ∈ G (k + 1) := by simpa using hf k 2 m hm
  fin_cases i <;> fin_cases j <;> simp [crossMatrix, neg_smul] <;> assumption

/-- The literal cross substitution has coefficient shift equal to its auxiliary degree. -/
theorem finiteCross_crossMatrix_mem_coefficientGrade (G : ℤ → AddSubgroup M)
    (u v z : R)
    (hf : ∀ k i m, m ∈ G k → (![u,v,z] : Fin 3 → R) i • m ∈ G (k + 1))
    (k : ℤ) (n : ℕ) (c : Sym (Fin 3) n → M) (hc : ∀ i, c i ∈ G k) :
    ∀ j, finiteCross (crossMatrix u v z) n c j ∈ G (k + n) :=
  finiteCross_mem_coefficientGrade G (crossMatrix u v z)
    (crossMatrix_degree_one G u v z hf) k n c hc

end ChoppedPlane.FiniteCech
