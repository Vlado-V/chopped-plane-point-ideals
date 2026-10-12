module

public import ChoppedPlane.LaurentAuxiliaryPerfectPairing

@[expose] public section

/-! Surjectivity of the actual coefficient differential follows from injectivity
of its literal projected multiplication adjoint under perfect residue duality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace ChoppedPlane.LaurentPairing
open Module MvPolynomial SymmetricDerivative
variable {K : Type*} [Field K] {J : Type*}

/-- Exact pointwise transpose identity under the genuine perfect residue
pairing, for the actual three-operator finite auxiliary maps. -/
theorem auxiliaryCoefficientResidueDualEquiv_adjoint [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ)
    (T : Fin 3 → positiveGrade (K := K) g r →ₗ[K] positiveGrade (K := K) g (r + 1))
    (L : Fin 3 → negativeGrade (K := K) g (r + 1) →ₗ[K] negativeGrade (K := K) g r)
    (h : ∀ i q p, residuePair g (r + 1) q (T i p) = residuePair g r (L i q) p)
    (t : ℕ) (q : Sym (Fin 3) t → negativeGrade (K := K) g (r + 1))
    (p : Sym (Fin 3) (t + 1) → positiveGrade (K := K) g r) :
    auxiliaryCoefficientResidueDualEquiv g r (t + 1)
        (auxiliaryOperatorMultiply (K := K) L t q) p =
      auxiliaryCoefficientResidueDualEquiv g (r + 1) t q
        (operatorDifferential (K := K) T t p) := by
  rw [auxiliaryCoefficientResidueDualEquiv_apply, auxiliaryCoefficientResidueDualEquiv_apply]
  symm
  unfold auxiliaryCoefficientPair
  simp only [operatorDifferential_coeff, auxiliaryOperatorMultiply_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  rw [h]
  calc
    _ = (factorialWeight K (homogeneousTensorExponent t s) *
        (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
          (homogeneousTensorExponent t s)) * residuePair g r (L i (q s)) (p b) := by ring
    _ = (factorialWeight K (homogeneousTensorExponent (t + 1) b) *
        (X i * monomial (homogeneousTensorExponent t s) 1 : Poly K 3).coeff
          (homogeneousTensorExponent (t + 1) b)) * residuePair g r (L i (q s)) (p b) := by
      rw [factorialWeight_pderiv_monomial_pair]
    _ = _ := by ring

/-- Surjectivity of the actual positive differential is equivalent to
injectivity of the actual projected multiplication on the negative dual. -/
theorem operatorDifferential_surjective_iff_auxiliaryMultiply_injective
    [Finite J] [CharZero K] (g : J → ℤ) (r : ℤ)
    (T : Fin 3 → positiveGrade (K := K) g r →ₗ[K] positiveGrade (K := K) g (r + 1))
    (L : Fin 3 → negativeGrade (K := K) g (r + 1) →ₗ[K] negativeGrade (K := K) g r)
    (h : ∀ i q p, residuePair g (r + 1) q (T i p) = residuePair g r (L i q) p)
    (t : ℕ) :
    Function.Surjective (operatorDifferential (K := K) (V := positiveGrade (K := K) g r) (W := positiveGrade (K := K) g (r + 1)) T t) ↔
      Function.Injective (auxiliaryOperatorMultiply (K := K) (W' := negativeGrade (K := K) g (r + 1)) (V' := negativeGrade (K := K) g r) L t) := by
  let E := auxiliaryCoefficientResidueDualEquiv (K := K) g (r + 1) t
  let F := auxiliaryCoefficientResidueDualEquiv (K := K) g r (t + 1)
  have hadj (q : Sym (Fin 3) t → negativeGrade (K := K) g (r + 1)) :
      F (auxiliaryOperatorMultiply (K := K) (W' := negativeGrade (K := K) g (r + 1)) (V' := negativeGrade (K := K) g r) L t q) = (operatorDifferential (K := K) (V := positiveGrade (K := K) g r) (W := positiveGrade (K := K) g (r + 1)) T t).dualMap (E q) :=
    LinearMap.ext fun p => auxiliaryCoefficientResidueDualEquiv_adjoint g r T L h t q p
  constructor
  · intro hD q q' hq
    apply E.injective
    apply LinearMap.dualMap_injective_of_surjective hD
    rw [← hadj, ← hadj, hq]
  · intro hL
    apply (LinearMap.dualMap_injective_iff (K := K)
      (V₁ := Sym (Fin 3) (t + 1) → positiveGrade (K := K) g r)
      (V₂ := Sym (Fin 3) t → positiveGrade (K := K) g (r + 1)) (f :=
      operatorDifferential (K := K) (V := positiveGrade (K := K) g r)
        (W := positiveGrade (K := K) g (r + 1)) T t)).mp
    intro φ ψ hφ
    obtain ⟨q,rfl⟩ := E.surjective φ
    obtain ⟨q',rfl⟩ := E.surjective ψ
    have hq : auxiliaryOperatorMultiply (K := K) (W' := negativeGrade (K := K) g (r + 1)) (V' := negativeGrade (K := K) g r) L t q = auxiliaryOperatorMultiply (K := K) (W' := negativeGrade (K := K) g (r + 1)) (V' := negativeGrade (K := K) g r) L t q' := by
      apply F.injective
      rw [hadj, hadj]
      exact hφ
    exact congrArg E (hL hq)

end ChoppedPlane.LaurentPairing
