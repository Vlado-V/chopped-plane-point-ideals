module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Factorial weights for coefficient duality

The factorial weight turns partial differentiation into the adjoint of
multiplication by a variable under the coefficient pairing.
-/

noncomputable section
namespace ChoppedPlane

open MvPolynomial

/-- The product of the factorials of the three exponents. -/
def factorialWeightNat (s : Fin 3 →₀ ℕ) : ℕ :=
  ∏ i : Fin 3, (s i).factorial

/-- The coefficient-field version of the factorial weight. -/
def factorialWeight (K : Type*) [CommSemiring K] (s : Fin 3 →₀ ℕ) : K :=
  ∏ i : Fin 3, ((s i).factorial : K)

@[simp] theorem factorialWeightNat_zero : factorialWeightNat 0 = 1 := by
  simp [factorialWeightNat]

@[simp] theorem factorialWeight_zero (K : Type*) [CommSemiring K] :
    factorialWeight K 0 = 1 := by
  simp [factorialWeight]

@[simp] theorem factorialWeight_eq_cast (K : Type*) [CommSemiring K]
    (s : Fin 3 →₀ ℕ) :
    factorialWeight K s = (factorialWeightNat s : K) := by
  simp [factorialWeight, factorialWeightNat]

theorem factorialWeightNat_ne_zero (s : Fin 3 →₀ ℕ) :
    factorialWeightNat s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact Nat.factorial_ne_zero (s i)

theorem factorialWeight_ne_zero (K : Type*) [CommSemiring K] [CharZero K]
    (s : Fin 3 →₀ ℕ) : factorialWeight K s ≠ 0 := by
  rw [factorialWeight_eq_cast]
  exact_mod_cast factorialWeightNat_ne_zero s

theorem factorialWeightNat_add_single (s : Fin 3 →₀ ℕ) (i : Fin 3) :
    factorialWeightNat (s + Finsupp.single i 1) = (s i + 1) * factorialWeightNat s := by
  classical
  have hprod :
      (∏ j ∈ (Finset.univ.erase i : Finset (Fin 3)),
        ((s + Finsupp.single i 1 : Fin 3 →₀ ℕ) j).factorial) =
        ∏ j ∈ (Finset.univ.erase i : Finset (Fin 3)), (s j).factorial := by
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [hji]
  unfold factorialWeightNat
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : Fin 3 => ((s + Finsupp.single i 1 : Fin 3 →₀ ℕ) j).factorial)
      (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j : Fin 3 => (s j).factorial) (Finset.mem_univ i)]
  rw [hprod]
  simp [Nat.factorial_succ, mul_assoc]

/-- Increasing one exponent multiplies its weight by the new exponent. -/
theorem factorialWeight_add_single (K : Type*) [CommSemiring K]
    (s : Fin 3 →₀ ℕ) (i : Fin 3) :
    factorialWeight K (s + Finsupp.single i 1) =
      ((s i + 1 : ℕ) : K) * factorialWeight K s := by
  rw [factorialWeight_eq_cast, factorialWeightNat_add_single, Nat.cast_mul,
    factorialWeight_eq_cast]

/-- A commuted form convenient for weighted coefficient calculations. -/
theorem factorialWeight_add_single_comm (K : Type*) [CommSemiring K]
    (s : Fin 3 →₀ ℕ) (i : Fin 3) :
    factorialWeight K (s + Finsupp.single i 1) =
      factorialWeight K s * ((s i + 1 : ℕ) : K) := by
  rw [factorialWeight_add_single, mul_comm]

/-- Factorial-weighted partial derivative coefficients have no scalar factor. -/
theorem factorialWeight_mul_coeff_pderiv (K : Type*) [CommSemiring K]
    (s : Fin 3 →₀ ℕ) (i : Fin 3) (f : MvPolynomial (Fin 3) K) :
    factorialWeight K s * (pderiv i f).coeff s =
      factorialWeight K (s + Finsupp.single i 1) *
        f.coeff (s + Finsupp.single i 1) := by
  rw [coeff_pderiv, factorialWeight_add_single]
  push_cast
  ring

/-- On monomials, multiplication by a variable and partial differentiation
have transposed matrix entries for the factorial-weighted coefficient pairing. -/
theorem factorialWeight_pderiv_monomial_pair (K : Type*) [CommSemiring K]
    (s b : Fin 3 →₀ ℕ) (i : Fin 3) :
    factorialWeight K s *
        (pderiv i (monomial b 1 : MvPolynomial (Fin 3) K)).coeff s =
      factorialWeight K b *
        (X i * monomial s 1 : MvPolynomial (Fin 3) K).coeff b := by
  classical
  rw [factorialWeight_mul_coeff_pderiv]
  simp only [X, monomial_mul_monomial, one_mul, coeff_monomial]
  by_cases h : b = s + Finsupp.single i 1
  · subst b
    simp [add_comm]
  · have hs : Finsupp.single i 1 + s ≠ b := by
      simpa [add_comm] using Ne.symm h
    simp [h, hs]

end ChoppedPlane
