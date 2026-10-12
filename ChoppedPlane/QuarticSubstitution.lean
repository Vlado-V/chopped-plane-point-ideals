module

public import ChoppedPlane.QWeylModule
public import ChoppedPlane.DistinctLeadingDegrees

@[expose] public section

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial
open scoped MonomialOrder
variable (K : Type*) [Field K]

/-- The actual binary quartic substitution in the cubic witness. -/
def quarticSubstitution : BinaryRing K →ₐ[K] BinaryRing K :=
  MvPolynomial.aeval ![quarticU (binaryU K) (binaryV K),
    quarticV (binaryU K) (binaryV K)]

variable {K}
@[simp] theorem quarticSubstitution_u :
    quarticSubstitution K (binaryU K) = quarticU (binaryU K) (binaryV K) := by
  simp [quarticSubstitution, binaryU]
@[simp] theorem quarticSubstitution_v :
    quarticSubstitution K (binaryV K) = quarticV (binaryU K) (binaryV K) := by
  simp [quarticSubstitution, binaryV]
@[simp] theorem quarticSubstitution_C (s : K) :
    quarticSubstitution K (C s) = C s := by
  simp [quarticSubstitution]

/-- Both coordinate quartics are actual homogeneous binary forms. -/
theorem quarticU_homogeneous :
    (quarticU (binaryU K) (binaryV K)).IsHomogeneous 4 := by
  have hu : (X (R := K) (0 : Fin 2)).IsHomogeneous 1 := isHomogeneous_X K 0
  have hu3 : ((X (0 : Fin 2) : BinaryRing K) ^ 3).IsHomogeneous 3 := isHomogeneous_X_pow _ _
  have hv3 : ((X (1 : Fin 2) : BinaryRing K) ^ 3).IsHomogeneous 3 := isHomogeneous_X_pow _ _
  simpa [quarticU, binaryU, binaryV, map_ofNat] using hu.mul (hu3.add (hv3.C_mul (2 : K)))

theorem quarticV_homogeneous :
    (quarticV (binaryU K) (binaryV K)).IsHomogeneous 4 := by
  have hv : (X (R := K) (1 : Fin 2)).IsHomogeneous 1 := isHomogeneous_X K 1
  have hu3 : ((X (0 : Fin 2) : BinaryRing K) ^ 3).IsHomogeneous 3 := isHomogeneous_X_pow _ _
  have hv3 : ((X (1 : Fin 2) : BinaryRing K) ^ 3).IsHomogeneous 3 := isHomogeneous_X_pow _ _
  simpa [quarticV, binaryU, binaryV, map_ofNat] using hv.neg.mul ((hu3.C_mul (2 : K)).add hv3)

/-- The actual quartic substitution multiplies each homogeneous degree by four. -/
theorem quarticSubstitution_homogeneous {p : BinaryRing K} {d : ℕ}
    (hp : p.IsHomogeneous d) : (quarticSubstitution K p).IsHomogeneous (4 * d) := by
  apply hp.aeval
  intro i
  fin_cases i
  · change (quarticU (binaryU K) (binaryV K)).IsHomogeneous 4
    exact quarticU_homogeneous
  · change (quarticV (binaryU K) (binaryV K)).IsHomogeneous 4
    exact quarticV_homogeneous

private def binaryLex : MonomialOrder (Fin 2) := MonomialOrder.lex

private theorem binaryLex_lt_of_first {s t : Fin 2 →₀ ℕ} (h : s 0 < t 0) :
    s ≺[binaryLex] t := by
  apply MonomialOrder.lex_lt_iff.mpr
  apply Finsupp.Lex.lt_iff.mpr
  refine ⟨0, ?_, h⟩
  intro j hj
  have : ¬j < (0 : Fin 2) := by omega
  exact False.elim (this hj)

private theorem quarticU_monomials :
    quarticU (binaryU K) (binaryV K) =
      monomial (Finsupp.single 0 4) (1 : K) +
      monomial (Finsupp.single 0 1 + Finsupp.single 1 3) (2 : K) := by
  rw [monomial_add_single]
  simp only [monomial_eq, Finsupp.prod_single_index, pow_zero, C_1, one_mul]
  simp only [quarticU, binaryU, binaryV, map_ofNat]
  ring

private theorem quarticV_monomials :
    quarticV (binaryU K) (binaryV K) =
      monomial (Finsupp.single 0 3 + Finsupp.single 1 1) (-2 : K) +
      monomial (Finsupp.single 1 4) (-1 : K) := by
  rw [monomial_add_single]
  simp only [monomial_eq, Finsupp.prod_single_index, pow_zero, pow_one,
    C_neg, map_ofNat, C_1]
  simp only [quarticV, binaryU, binaryV]
  ring

variable [CharZero K]

private theorem quarticU_lower_degree :
    binaryLex.degree (monomial (Finsupp.single 0 1 + Finsupp.single 1 3) (2 : K)) ≺[binaryLex]
      binaryLex.degree (monomial (Finsupp.single 0 4) (1 : K)) := by
  classical
  rw [MonomialOrder.degree_monomial, MonomialOrder.degree_monomial]
  simp only [show (2 : K) ≠ 0 by norm_num, one_ne_zero, ite_false]
  apply binaryLex_lt_of_first
  simp

private theorem quarticV_lower_degree :
    binaryLex.degree (monomial (Finsupp.single 1 4) (-1 : K)) ≺[binaryLex]
      binaryLex.degree (monomial (Finsupp.single 0 3 + Finsupp.single 1 1) (-2 : K)) := by
  classical
  rw [MonomialOrder.degree_monomial, MonomialOrder.degree_monomial]
  simp only [show (-2 : K) ≠ 0 by norm_num, neg_ne_zero.mpr one_ne_zero, ite_false]
  apply binaryLex_lt_of_first
  simp

private theorem quarticU_degree :
    binaryLex.degree (quarticU (binaryU K) (binaryV K)) = Finsupp.single 0 4 := by
  rw [quarticU_monomials, MonomialOrder.degree_add_of_lt quarticU_lower_degree]
  classical
  simp [MonomialOrder.degree_monomial]

private theorem quarticV_degree :
    binaryLex.degree (quarticV (binaryU K) (binaryV K)) =
      Finsupp.single 0 3 + Finsupp.single 1 1 := by
  rw [quarticV_monomials, MonomialOrder.degree_add_of_lt quarticV_lower_degree]
  classical
  simp [MonomialOrder.degree_monomial]

private theorem quarticU_leadingCoeff :
    binaryLex.leadingCoeff (quarticU (binaryU K) (binaryV K)) = (1 : K) := by
  rw [quarticU_monomials, MonomialOrder.leadingCoeff_add_of_lt quarticU_lower_degree]
  exact binaryLex.leadingCoeff_monomial _

private theorem quarticV_leadingCoeff :
    binaryLex.leadingCoeff (quarticV (binaryU K) (binaryV K)) = (-2 : K) := by
  rw [quarticV_monomials, MonomialOrder.leadingCoeff_add_of_lt quarticV_lower_degree]
  exact binaryLex.leadingCoeff_monomial _

/-- The exponent of the leading monomial after the actual quartic pullback. -/
def quarticExponent (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  d 0 • Finsupp.single 0 4 + d 1 • (Finsupp.single 0 3 + Finsupp.single 1 1)

@[simp] theorem quarticExponent_zero (d : Fin 2 →₀ ℕ) :
    quarticExponent d 0 = 4 * d 0 + 3 * d 1 := by
  simp [quarticExponent, mul_comm]
@[simp] theorem quarticExponent_one (d : Fin 2 →₀ ℕ) :
    quarticExponent d 1 = d 1 := by simp [quarticExponent]

theorem quarticExponent_injective : Function.Injective quarticExponent := by
  intro s t h
  have h0 := congrArg (fun q : Fin 2 →₀ ℕ => q 0) h
  have h1 := congrArg (fun q : Fin 2 →₀ ℕ => q 1) h
  simp only [quarticExponent_zero, quarticExponent_one] at h0 h1
  ext i
  fin_cases i
  · change s 0 = t 0
    omega
  · change s 1 = t 1
    exact h1

omit [CharZero K] in
private theorem quarticSubstitution_monomial (d : Fin 2 →₀ ℕ) (s : K) :
    quarticSubstitution K (monomial d s) = C s *
      (quarticU (binaryU K) (binaryV K) ^ d 0 *
        quarticV (binaryU K) (binaryV K) ^ d 1) := by
  rw [quarticSubstitution, MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  rfl

private theorem quarticSubstitution_monomial_leadingCoeff
    (d : Fin 2 →₀ ℕ) (s : K) :
    binaryLex.leadingCoeff (quarticSubstitution K (monomial d s)) = s * (-2) ^ d 1 := by
  rw [quarticSubstitution_monomial]
  simp only [MonomialOrder.leadingCoeff_mul, MonomialOrder.leadingCoeff_pow,
    MonomialOrder.leadingCoeff_C, quarticU_leadingCoeff, quarticV_leadingCoeff,
    one_pow, one_mul]

private theorem quarticSubstitution_monomial_ne_zero
    (d : Fin 2 →₀ ℕ) {s : K} (hs : s ≠ 0) :
    quarticSubstitution K (monomial d s) ≠ 0 := by
  apply MonomialOrder.leadingCoeff_ne_zero_iff.mp
  rw [quarticSubstitution_monomial_leadingCoeff]
  exact mul_ne_zero hs (pow_ne_zero _ (by norm_num))

private theorem quarticSubstitution_monomial_degree
    (d : Fin 2 →₀ ℕ) {s : K} (hs : s ≠ 0) :
    binaryLex.degree (quarticSubstitution K (monomial d s)) = quarticExponent d := by
  have hu : quarticU (binaryU K) (binaryV K) ≠ 0 := by
    apply MonomialOrder.leadingCoeff_ne_zero_iff.mp
    rw [quarticU_leadingCoeff]
    exact one_ne_zero
  have hv : quarticV (binaryU K) (binaryV K) ≠ 0 := by
    apply MonomialOrder.leadingCoeff_ne_zero_iff.mp
    rw [quarticV_leadingCoeff]
    norm_num
  rw [quarticSubstitution_monomial,
    MonomialOrder.degree_mul (MvPolynomial.C_ne_zero.mpr hs)
      (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)),
    MonomialOrder.degree_mul (pow_ne_zero _ hu) (pow_ne_zero _ hv),
    MonomialOrder.degree_pow, MonomialOrder.degree_pow,
    MonomialOrder.degree_C, zero_add, quarticU_degree, quarticV_degree]
  rfl

/-- The quartic pullback preserves nonzero binary polynomials. -/
theorem quarticSubstitution_ne_zero {p : BinaryRing K} (hp : p ≠ 0) :
    quarticSubstitution K p ≠ 0 := by
  classical
  rw [p.as_sum, map_sum]
  apply MonomialOrder.sum_ne_zero_of_degree_injOn binaryLex p.support
  · exact MvPolynomial.support_nonempty.mpr hp
  · intro d hd
    exact quarticSubstitution_monomial_ne_zero d (MvPolynomial.mem_support_iff.mp hd)
  · intro d hd e he h
    apply quarticExponent_injective
    change binaryLex.degree (quarticSubstitution K (monomial d (p.coeff d))) =
      binaryLex.degree (quarticSubstitution K (monomial e (p.coeff e))) at h
    rw [quarticSubstitution_monomial_degree d (MvPolynomial.mem_support_iff.mp hd),
      quarticSubstitution_monomial_degree e (MvPolynomial.mem_support_iff.mp he)] at h
    exact h

/-- The actual quartic binary substitution is injective in characteristic zero. -/
theorem quarticSubstitution_injective : Function.Injective (quarticSubstitution K) := by
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra h
  apply quarticSubstitution_ne_zero h
  rw [map_sub, hpq, sub_self]

end ChoppedPlane.QWeyl
