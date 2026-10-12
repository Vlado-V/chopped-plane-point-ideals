module

public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic

@[expose] public section

/-!
# Exact interpolation on a Cartesian grid

A polynomial of degree less than the number of grid coordinates in each
variable is determined by its values on that grid. This is the algebraic
interpolation input for the two-generator witness on page 5.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ChoppedPlane.Grid

open Polynomial
open scoped Polynomial.Bivariate

variable {K : Type*} [Field K]

/-- Iterated univariate root counting, with independent bounds in both variables. -/
theorem eq_zero_of_grid_eval_eq_zero {m n : ℕ} (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (P : K[X][Y]) (hY : P.natDegree < n)
    (hX : ∀ j : ℕ, (P.coeff j).natDegree < m)
    (hv : ∀ i j, P.evalEval (α i) (β j) = 0) : P = 0 := by
  have hmap (i : Fin m) : P.map (evalRingHom (α i)) = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hβ
    · intro j
      simpa only [map_evalRingHom_eval] using hv i j
    · simpa using lt_of_le_of_lt (natDegree_map_le) hY
  apply Polynomial.ext
  intro j
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hα
  · intro i
    have hi := congrArg (fun Q : K[X] => Q.coeff j) (hmap i)
    simpa only [coeff_map, coeff_zero, coe_evalRingHom] using hi
  · simpa using hX j

/-- Two polynomials in the same rectangular degree bounds agree exactly when
    their grid evaluations agree. -/
theorem eq_of_grid_eval_eq {m n : ℕ} (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (P Q : K[X][Y]) (hY : max P.natDegree Q.natDegree < n)
    (hX : ∀ j : ℕ, max (P.coeff j).natDegree (Q.coeff j).natDegree < m)
    (hv : ∀ i j, P.evalEval (α i) (β j) = Q.evalEval (α i) (β j)) : P = Q := by
  apply sub_eq_zero.mp
  apply eq_zero_of_grid_eval_eq_zero α β hα hβ (P - Q)
  · exact lt_of_le_of_lt (natDegree_sub_le _ _) hY
  · intro j
    rw [coeff_sub]
    exact lt_of_le_of_lt (natDegree_sub_le _ _) (hX j)
  · intro i j
    simpa only [evalEval_sub, sub_eq_zero] using hv i j

/-- The monic polynomial whose roots are the selected first coordinates. -/
def coordinatePolynomial {d : ℕ} (α : Fin d → K) : K[X] :=
  ∏ i, (X - C (α i))

@[simp] theorem coordinatePolynomial_eval {d : ℕ} (α : Fin d → K) (i : Fin d) :
    (coordinatePolynomial α).eval (α i) = 0 := by
  classical
  simp only [coordinatePolynomial, eval_prod, eval_sub, eval_X, eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (sub_self _)

/-- Every selected coordinate is a root, and root counting excludes all others. -/
theorem coordinatePolynomial_eval_eq_zero_iff {d : ℕ} (α : Fin d → K) (x : K) :
    (coordinatePolynomial α).eval x = 0 ↔ ∃ i, x = α i := by
  classical
  simp only [coordinatePolynomial, eval_prod, eval_sub, eval_X, eval_C,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero]

/-- The first defining equation of the affine grid. -/
def firstEquation {d : ℕ} (α : Fin d → K) : K[X][Y] := C (coordinatePolynomial α)

/-- The second defining equation of the affine grid. -/
def secondEquation {d : ℕ} (β : Fin d → K) : K[X][Y] :=
  (coordinatePolynomial β).map C

/-- The two equations cut out exactly the Cartesian product, as a set. -/
theorem affine_zero_set {d : ℕ} (α β : Fin d → K) (x y : K) :
    (firstEquation α).evalEval x y = 0 ∧ (secondEquation β).evalEval x y = 0 ↔
      (∃ i, x = α i) ∧ (∃ j, y = β j) := by
  simp only [firstEquation, secondEquation, evalEval_C, evalEval_map_C,
    coordinatePolynomial_eval_eq_zero_iff]

omit [Field K] in
/-- Pairwise distinct coordinates yield pairwise distinct grid points. -/
theorem grid_injective {m n : ℕ} (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (fun ij : Fin m × Fin n => (α ij.1, β ij.2)) := by
  intro ij kl h
  exact Prod.ext (hα (congrArg Prod.fst h)) (hβ (congrArg Prod.snd h))

end ChoppedPlane.Grid

namespace ChoppedPlane.Grid

open Polynomial
open scoped Polynomial.Bivariate
variable {K : Type*} [Field K]

@[simp] theorem coordinatePolynomial_natDegree {d : ℕ} (α : Fin d → K) :
    (coordinatePolynomial α).natDegree = d := by
  classical
  simpa only [coordinatePolynomial, Finset.card_univ, Fintype.card_fin] using
    natDegree_finsetProd_X_sub_C_eq_card Finset.univ α

theorem coordinatePolynomial_monic {d : ℕ} (α : Fin d → K) :
    (coordinatePolynomial α).Monic := monic_prod_X_sub_C α Finset.univ

@[simp] theorem coordinatePolynomial_coeff_degree {d : ℕ} (α : Fin d → K) :
    (coordinatePolynomial α).coeff d = 1 := by
  simpa only [coordinatePolynomial_natDegree] using
    (coordinatePolynomial_monic α).coeff_natDegree

/-- A coefficient description of total degree at most `d`, independent of
    choices of support finsets. -/
def TotalDegreeLE (d : ℕ) (P : K[X][Y]) : Prop :=
  ∀ i j : ℕ, d < i + j → (P.coeff j).coeff i = 0

@[simp] theorem firstEquation_coeff_coeff {d : ℕ} (α : Fin d → K) (i j : ℕ) :
    ((firstEquation α).coeff j).coeff i =
      if j = 0 then (coordinatePolynomial α).coeff i else 0 := by
  by_cases hj : j = 0 <;> simp [firstEquation, hj, coeff_C]

@[simp] theorem secondEquation_coeff_coeff {d : ℕ} (β : Fin d → K) (i j : ℕ) :
    ((secondEquation β).coeff j).coeff i =
      if i = 0 then (coordinatePolynomial β).coeff j else 0 := by
  by_cases hi : i = 0 <;> simp [secondEquation, hi, coeff_map, coeff_C]

/-- Subtract the two pure top-degree terms using the grid equations. -/
def gridRemainder {d : ℕ} (α β : Fin d → K) (P : K[X][Y]) : K[X][Y] :=
  P - (P.coeff 0).coeff d • firstEquation α -
    (P.coeff d).coeff 0 • secondEquation β

theorem gridRemainder_coeff_vanish {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (P : K[X][Y]) (hP : TotalDegreeLE d P) (i j : ℕ) (hij : d ≤ i ∨ d ≤ j) :
    ((gridRemainder α β P).coeff j).coeff i = 0 := by
  simp only [gridRemainder, coeff_sub, coeff_smul, smul_eq_mul,
    firstEquation_coeff_coeff, secondEquation_coeff_coeff]
  by_cases hx : i = d ∧ j = 0
  · rcases hx with ⟨rfl, rfl⟩
    simp [Nat.ne_of_gt hd]
  by_cases hy : i = 0 ∧ j = d
  · rcases hy with ⟨rfl, rfl⟩
    simp [Nat.ne_of_gt hd]
  have hcoeff : (P.coeff j).coeff i = 0 := hP i j (by omega)
  have hfirst : (if j = 0 then (coordinatePolynomial α).coeff i else 0) = 0 := by
    split_ifs with hj
    · exact coeff_eq_zero_of_natDegree_lt (by rw [coordinatePolynomial_natDegree]; omega)
    · rfl
  have hsecond : (if i = 0 then (coordinatePolynomial β).coeff j else 0) = 0 := by
    split_ifs with hi
    · exact coeff_eq_zero_of_natDegree_lt (by rw [coordinatePolynomial_natDegree]; omega)
    · rfl
  rw [hcoeff, hfirst, hsecond]
  simp

/-- In degree at most `d`, the full-grid vanishing space is exactly the span of
    the two defining equations. -/
theorem grid_kernel {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (P : K[X][Y]) (hP : TotalDegreeLE d P) :
    (∀ i j, P.evalEval (α i) (β j) = 0) ↔
      ∃ a b : K, P = a • firstEquation α + b • secondEquation β := by
  constructor
  · intro hv
    have hzero : gridRemainder α β P = 0 := by
      apply eq_zero_of_grid_eval_eq_zero α β hα hβ
      · have hle : (gridRemainder α β P).natDegree ≤ d - 1 := by
          apply natDegree_le_iff_coeff_eq_zero.mpr
          intro j hj
          apply Polynomial.ext
          intro i
          simpa only [coeff_zero] using gridRemainder_coeff_vanish hd α β P hP i j
            (Or.inr (by omega))
        omega
      · intro j
        have hle : ((gridRemainder α β P).coeff j).natDegree ≤ d - 1 := by
          apply natDegree_le_iff_coeff_eq_zero.mpr
          intro i hi
          exact gridRemainder_coeff_vanish hd α β P hP i j (Or.inl (by omega))
        omega
      · intro i j
        simp only [gridRemainder, evalEval_sub, evalEval_smul, firstEquation,
          secondEquation, evalEval_C, evalEval_map_C, coordinatePolynomial_eval,
          smul_zero, sub_zero, hv]
    refine ⟨(P.coeff 0).coeff d, (P.coeff d).coeff 0, ?_⟩
    rw [gridRemainder, sub_sub] at hzero
    exact sub_eq_zero.mp hzero
  · rintro ⟨a, b, rfl⟩ i j
    simp only [evalEval_add, evalEval_smul, firstEquation, secondEquation,
      evalEval_C, evalEval_map_C, coordinatePolynomial_eval, smul_zero, add_zero]

/-- The two equations are linearly independent: their pure degree-`d`
    coefficients distinguish them. -/
theorem grid_equations_independent {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    {a b : K} (h : a • firstEquation α + b • secondEquation β = 0) :
    a = 0 ∧ b = 0 := by
  have hx := congrArg (fun P : K[X][Y] => (P.coeff 0).coeff d) h
  have hy := congrArg (fun P : K[X][Y] => (P.coeff d).coeff 0) h
  simp only [coeff_add, coeff_smul, smul_eq_mul, coeff_zero,
    firstEquation_coeff_coeff, secondEquation_coeff_coeff,
    coordinatePolynomial_coeff_degree] at hx hy
  simpa [Nat.ne_of_gt hd] using And.intro hx hy

end ChoppedPlane.Grid
