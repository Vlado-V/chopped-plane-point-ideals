module

public import ChoppedPlane.Homogeneous
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section

/-! Homogeneous division by a coordinate variable. -/

namespace ChoppedPlane

open MvPolynomial

variable {K : Type*} [Field K]

/-- Removing one `x` factor lowers the homogeneous degree by one. Terms
without an `x` factor are discarded by `divMonomial`. -/
theorem homogeneous_div_x {t : ℕ} (p : Poly K 3)
    (hp : p.IsHomogeneous (t + 1)) :
    (p.divMonomial (Finsupp.single 0 1)).IsHomogeneous t := by
  intro e he
  have hcoeff : p.coeff (Finsupp.single 0 1 + e) ≠ 0 := by
    simpa only [coeff_divMonomial] using he
  have hdeg : (Finsupp.single 0 1 + e).degree = t + 1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp hcoeff
  have hedeg : e.degree = t := by
    simp only [map_add, Finsupp.degree_single] at hdeg
    omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hedeg

/-- A homogeneous constant with a coordinate factor is zero. -/
theorem homogeneous_zero_of_x_dvd (p : Poly K 3)
    (hp : p.IsHomogeneous 0) (hdiv : X 0 ∣ p) : p = 0 := by
  ext e
  by_cases he : e = 0
  · subst e
    obtain ⟨q, rfl⟩ := hdiv
    simp [coeff_X_mul']
  · simpa only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] using
      hp.coeff_eq_zero (fun hd => he ((Finsupp.degree_eq_zero_iff e).mp hd))

/-- The quotient by `x` reconstructs a polynomial when `x` divides it. -/
theorem x_mul_div_of_x_dvd (p : Poly K 3) (hdiv : X 0 ∣ p) :
    X 0 * p.divMonomial (Finsupp.single 0 1) = p := by
  have hmod := (X_dvd_iff_modMonomial_eq_zero).mp hdiv
  simpa only [hmod, add_zero] using p.divMonomial_add_modMonomial_single 0

end ChoppedPlane
