module

public import ChoppedPlane.Grid
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.LinearAlgebra.Dimension.Constructions

@[expose] public section

/-! The exact affine Cartesian-grid quotient and its larger quotients. -/

noncomputable section
set_option maxHeartbeats 800000

namespace ChoppedPlane.Grid

open Polynomial
open scoped Polynomial.Bivariate BigOperators

variable {K : Type*} [Field K] {m n : ℕ}

/-- The actual two-equation ideal of the full affine grid. -/
def affineGridIdeal (α : Fin m → K) (β : Fin n → K) : Ideal K[X][Y] :=
  Ideal.span {firstEquation α, secondEquation β}

/-- Simultaneous evaluation on all Cartesian pairs. -/
def affineGridEvaluation (α : Fin m → K) (β : Fin n → K) :
    K[X][Y] →+* (Fin m × Fin n → K) :=
  RingHom.pi (fun ij => evalEvalRingHom (α ij.1) (β ij.2))

@[simp] theorem affineGridEvaluation_apply (α : Fin m → K) (β : Fin n → K)
    (P : K[X][Y]) (ij : Fin m × Fin n) :
    affineGridEvaluation α β P ij = P.evalEval (α ij.1) (β ij.2) := rfl

/-- A polynomial vanishing at every distinct coordinate is divisible by the
monic product of the corresponding linear factors. -/
theorem coordinatePolynomial_dvd_of_eval_zero (α : Fin m → K)
    (hα : Function.Injective α) (P : K[X]) (hP : ∀ i, P.eval (α i) = 0) :
    coordinatePolynomial α ∣ P := by
  by_cases hm : m = 0
  · subst m
    simp [coordinatePolynomial]
  have hf := coordinatePolynomial_monic α
  have hf1 : coordinatePolynomial α ≠ 1 := by
    intro h
    have hd := congrArg Polynomial.natDegree h
    simp only [coordinatePolynomial_natDegree, natDegree_one] at hd
    exact hm hd
  apply (modByMonic_eq_zero_iff_dvd hf).mp
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hα
  · intro i
    change eval₂ (RingHom.id K) (α i) (P %ₘ coordinatePolynomial α) = 0
    rw [eval₂_modByMonic_eq_self_of_root]
    · simpa only [eval₂_id] using hP i
    · simpa only [eval₂_id] using coordinatePolynomial_eval α i
  · simpa only [coordinatePolynomial_natDegree, Fintype.card_fin] using
      natDegree_modByMonic_lt P hf hf1

theorem affineGridIdeal_le_evaluation_ker (α : Fin m → K) (β : Fin n → K) :
    affineGridIdeal α β ≤ RingHom.ker (affineGridEvaluation α β) := by
  apply Ideal.span_le.mpr
  rintro P (rfl | rfl)
  · change affineGridEvaluation α β (firstEquation α) = 0
    ext ij
    simp [firstEquation, evalEval_C]
  · change affineGridEvaluation α β (secondEquation β) = 0
    ext ij
    simp [secondEquation, evalEval_map_C]

/-- The two defining equations generate the full vanishing ideal in every
degree, proved by monic division in the second variable and root counting. -/
theorem affineGridEvaluation_ker (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    RingHom.ker (affineGridEvaluation α β) = affineGridIdeal α β := by
  apply le_antisymm _ (affineGridIdeal_le_evaluation_ker α β)
  intro P hP
  have hv : ∀ i j, P.evalEval (α i) (β j) = 0 := by
    intro i j
    exact congrFun hP (i, j)
  by_cases hn : n = 0
  · subst n
    have h1 : (1 : K[X][Y]) ∈ affineGridIdeal α β := by
      have := Ideal.subset_span (show secondEquation β ∈
        ({firstEquation α, secondEquation β} : Set K[X][Y]) by simp)
      simpa [affineGridIdeal, secondEquation, coordinatePolynomial] using this
    simpa only [mul_one] using (affineGridIdeal α β).mul_mem_left P h1
  let G := secondEquation β
  let Q := P %ₘ G
  have hG : G.Monic := (coordinatePolynomial_monic β).map C
  have hGdegree : G.natDegree = n := by
    exact (coordinatePolynomial_monic β).natDegree_map C |>.trans
      (coordinatePolynomial_natDegree β)
  have hG1 : G ≠ 1 := by
    intro hh
    have hdegree := congrArg Polynomial.natDegree hh
    simp only [hGdegree, natDegree_one] at hdegree
    exact hn hdegree
  have hQdegree : Q.natDegree < n := by
    simpa only [hGdegree] using natDegree_modByMonic_lt P hG hG1
  have hQeval : ∀ i j, Q.evalEval (α i) (β j) = 0 := by
    intro i j
    change evalEval (α i) (β j) (P %ₘ G) = 0
    rw [← eval₂_evalRingHom]
    rw [eval₂_modByMonic_eq_self_of_root]
    · simpa only [eval₂_evalRingHom] using hv i j
    · rw [eval₂_evalRingHom]
      change (secondEquation β).evalEval (α i) (β j) = 0
      simp [secondEquation, evalEval_map_C]
  have hQmap (i : Fin m) : Q.map (evalRingHom (α i)) = 0 := by
    apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hβ
    · intro j
      simpa only [map_evalRingHom_eval] using hQeval i j
    · simpa only [Fintype.card_fin] using lt_of_le_of_lt natDegree_map_le hQdegree
  have hFQ : firstEquation α ∣ Q := by
    apply (C_dvd_iff_dvd_coeff _ Q).mpr
    intro j
    apply coordinatePolynomial_dvd_of_eval_zero α hα
    intro i
    have hh := congrArg (fun q : K[X] => q.coeff j) (hQmap i)
    simpa only [coeff_map, coeff_zero, coe_evalRingHom] using hh
  have hQmem : Q ∈ affineGridIdeal α β := by
    obtain ⟨q, hq⟩ := hFQ
    rw [hq]
    exact (affineGridIdeal α β).mul_mem_right q (Ideal.subset_span (by simp))
  have hGmem : G * (P /ₘ G) ∈ affineGridIdeal α β :=
    (affineGridIdeal α β).mul_mem_right _ (Ideal.subset_span (by simp [G]))
  rw [← modByMonic_add_div P G]
  exact (affineGridIdeal α β).add_mem hQmem hGmem

/-- Lagrange interpolation independently in the two coordinates makes full
grid evaluation surjective. -/
theorem affineGridEvaluation_surjective (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Surjective (affineGridEvaluation α β) := by
  classical
  intro v
  let L : Fin m → K[X] := fun i =>
    Lagrange.interpolate Finset.univ α (Pi.single i 1)
  let H : Fin m → K[X] := fun i =>
    Lagrange.interpolate Finset.univ β (fun j => v (i, j))
  let P : K[X][Y] := ∑ i, C (L i) * (H i).map C
  refine ⟨P, ?_⟩
  ext ij
  obtain ⟨k, l⟩ := ij
  change P.evalEval (α k) (β l) = v (k, l)
  simp only [P, evalEval_finsetSum, evalEval_mul, evalEval_C, evalEval_map_C]
  have hL (i : Fin m) : (L i).eval (α k) = (Pi.single i (1 : K) : Fin m → K) k := by
    simpa only [L] using Lagrange.eval_interpolate_at_node
      (Pi.single i (1 : K) : Fin m → K) hα.injOn (Finset.mem_univ k)
  have hH (i : Fin m) : (H i).eval (β l) = v (i, l) := by
    exact Lagrange.eval_interpolate_at_node (fun j => v (i, j))
      hβ.injOn (Finset.mem_univ l)
  simp_rw [hL, hH]
  rw [Fintype.sum_eq_single k]
  · simp
  · intro i hi
    simp [Pi.single_eq_of_ne hi.symm]

/-- The actual affine grid algebra is the product of one copy of the field
for every Cartesian pair. -/
def affineGridQuotientEquiv (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    (K[X][Y] ⧸ affineGridIdeal α β) ≃+* (Fin m × Fin n → K) :=
  (Ideal.quotEquivOfEq (affineGridEvaluation_ker α β hα hβ).symm).trans
    ((affineGridEvaluation α β).quotientKerEquivOfSurjective
      (affineGridEvaluation_surjective α β hα hβ))

/-- The full-grid quotient is reduced. -/
theorem affineGridQuotient_reduced (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    IsReduced (K[X][Y] ⧸ affineGridIdeal α β) :=
  isReduced_of_injective (affineGridQuotientEquiv α β hα hβ)
    (affineGridQuotientEquiv α β hα hβ).injective

end ChoppedPlane.Grid

namespace ChoppedPlane

open scoped BigOperators

variable {R K ι : Type*} [CommRing R] [Field K] [Fintype ι]

/-- A surjection onto a finite product of fields detects every ideal containing
its kernel by the coordinates on which that ideal vanishes. -/
theorem mem_ideal_of_vanish_on_selected (e : R →+* (ι → K))
    (he : Function.Surjective e) (I : Ideal R) (hker : RingHom.ker e ≤ I)
    (S : Set ι) (hsep : ∀ x, x ∉ S → ∃ g ∈ I, e g x ≠ 0)
    (f : R) (hf : ∀ x ∈ S, e f x = 0) : f ∈ I := by
  classical
  have hex : ∀ x, ∃ g : R, g ∈ I ∧ (x ∉ S → e g x ≠ 0) := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨0, I.zero_mem, fun h => (h hx).elim⟩
    · obtain ⟨g, hg, hge⟩ := hsep x hx
      exact ⟨g, hg, fun _ => hge⟩
  choose g hg hge using hex
  choose q hq using fun x => he (Pi.single x (e f x / e (g x) x))
  let P : R := ∑ x, q x * g x
  have hP : P ∈ I := by
    apply I.sum_mem
    intro x _
    exact I.mul_mem_left (q x) (hg x)
  have hPe : e P = e f := by
    ext x
    simp only [P, map_sum, Finset.sum_apply, map_mul, Pi.mul_apply]
    rw [Fintype.sum_eq_single x]
    · rw [hq]
      simp only [Pi.single_eq_same]
      by_cases hx : x ∈ S
      · simp [hf x hx]
      · exact div_mul_cancel₀ _ (hge x hx)
    · intro y hy
      rw [hq]
      simp [Pi.single_eq_of_ne hy.symm]
  have hdiff : f - P ∈ I := by
    apply hker
    change e (f - P) = 0
    rw [map_sub, hPe, sub_self]
  simpa only [sub_add_cancel] using I.add_mem hdiff hP

theorem mem_ideal_iff_vanish_on_selected (e : R →+* (ι → K))
    (he : Function.Surjective e) (I : Ideal R) (hker : RingHom.ker e ≤ I)
    (S : Set ι) (hvan : ∀ g ∈ I, ∀ x ∈ S, e g x = 0)
    (hsep : ∀ x, x ∉ S → ∃ g ∈ I, e g x ≠ 0) (f : R) :
    f ∈ I ↔ ∀ x ∈ S, e f x = 0 :=
  ⟨fun hf => hvan f hf, mem_ideal_of_vanish_on_selected e he I hker S hsep f⟩

omit [Fintype ι] in
/-- Every ideal above the kernel of a surjection onto a product of fields is
radical: coordinatewise inverses produce `f = f²q` modulo the kernel. -/
theorem isRadical_of_surjective_pi_kernel_le (e : R →+* (ι → K))
    (he : Function.Surjective e) (I : Ideal R) (hker : RingHom.ker e ≤ I) :
    I.IsRadical := by
  apply (I.isRadical_iff_pow_one_lt 2 (by norm_num)).mpr
  intro f hf
  obtain ⟨q, hq⟩ := he (fun x => (e f x)⁻¹)
  have hdiff : f - f ^ 2 * q ∈ I := by
    apply hker
    change e (f - f ^ 2 * q) = 0
    ext x
    simp only [map_sub, map_mul, map_pow, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, hq,
      Pi.zero_apply]
    by_cases hx : e f x = 0
    · simp [hx]
    · rw [pow_two, mul_assoc, mul_inv_cancel₀ hx, mul_one, sub_self]
  have hprod : f ^ 2 * q ∈ I := I.mul_mem_right q hf
  simpa only [sub_add_cancel] using I.add_mem hdiff hprod

omit [Fintype ι] in
theorem quotient_reduced_of_surjective_pi_kernel_le (e : R →+* (ι → K))
    (he : Function.Surjective e) (I : Ideal R) (hker : RingHom.ker e ≤ I) :
    IsReduced (R ⧸ I) :=
  (I.isRadical_iff_quotient_reduced).mp
    (isRadical_of_surjective_pi_kernel_le e he I hker)

end ChoppedPlane

namespace ChoppedPlane.Grid

open Polynomial
open scoped Polynomial.Bivariate BigOperators

variable {K : Type*} [Field K] {m n : ℕ}

theorem quotient_reduced_of_affineGridIdeal_le (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (I : Ideal K[X][Y]) (hI : affineGridIdeal α β ≤ I) : IsReduced (K[X][Y] ⧸ I) := by
  apply quotient_reduced_of_surjective_pi_kernel_le (affineGridEvaluation α β)
    (affineGridEvaluation_surjective α β hα hβ) I
  rwa [affineGridEvaluation_ker α β hα hβ]

/-- The two separated products in the actual two-variable polynomial ring. -/
def affineFirstProduct (α : Fin m → K) : MvPolynomial (Fin 2) K :=
  ∏ i, (MvPolynomial.X 0 - MvPolynomial.C (α i))

def affineSecondProduct (β : Fin n → K) : MvPolynomial (Fin 2) K :=
  ∏ j, (MvPolynomial.X 1 - MvPolynomial.C (β j))

def mvAffineGridIdeal (α : Fin m → K) (β : Fin n → K) :
    Ideal (MvPolynomial (Fin 2) K) :=
  Ideal.span {affineFirstProduct α, affineSecondProduct β}

def mvAffineGridEvaluation (α : Fin m → K) (β : Fin n → K) :
    MvPolynomial (Fin 2) K →+* (Fin m × Fin n → K) :=
  (affineGridEvaluation α β).comp (Bivariate.equivMvPolynomial K).symm.toRingHom

@[simp] theorem equivMvPolynomial_firstEquation (α : Fin m → K) :
    Bivariate.equivMvPolynomial K (firstEquation α) = affineFirstProduct α := by
  simp [firstEquation, coordinatePolynomial, affineFirstProduct, map_prod]

@[simp] theorem equivMvPolynomial_secondEquation (β : Fin n → K) :
    Bivariate.equivMvPolynomial K (secondEquation β) = affineSecondProduct β := by
  simp [secondEquation, coordinatePolynomial, affineSecondProduct, Polynomial.map_prod, map_prod]

theorem equivMvPolynomial_map_affineGridIdeal (α : Fin m → K) (β : Fin n → K) :
    (affineGridIdeal α β).map (Bivariate.equivMvPolynomial K).toRingHom =
      mvAffineGridIdeal α β := by
  rw [affineGridIdeal, Ideal.map_span]
  simp [mvAffineGridIdeal]

@[simp] theorem mvAffineGridEvaluation_apply (α : Fin m → K) (β : Fin n → K)
    (P : MvPolynomial (Fin 2) K) (ij : Fin m × Fin n) :
    mvAffineGridEvaluation α β P ij =
      MvPolynomial.eval ![α ij.1, β ij.2] P := by
  let e := Bivariate.equivMvPolynomial K
  have h : (evalEvalRingHom (α ij.1) (β ij.2)).comp e.symm.toRingHom =
      MvPolynomial.eval ![α ij.1, β ij.2] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [e]
    · intro i
      fin_cases i <;> simp [e]
  exact congrArg (fun φ : MvPolynomial (Fin 2) K →+* K => φ P) h

theorem mvAffineGridEvaluation_surjective (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Surjective (mvAffineGridEvaluation α β) :=
  (affineGridEvaluation_surjective α β hα hβ).comp
    (Bivariate.equivMvPolynomial K).symm.surjective

/-- The kernel in `MvPolynomial (Fin 2) K` is exactly the ideal generated by
the displayed separated products. -/
theorem mvAffineGridEvaluation_ker (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    RingHom.ker (mvAffineGridEvaluation α β) = mvAffineGridIdeal α β := by
  rw [mvAffineGridEvaluation, ← RingHom.comap_ker, affineGridEvaluation_ker α β hα hβ]
  calc
    _ = (affineGridIdeal α β).map (Bivariate.equivMvPolynomial K).toRingHom :=
      (Ideal.map_comap_of_equiv (Bivariate.equivMvPolynomial K).toRingEquiv).symm
    _ = mvAffineGridIdeal α β := equivMvPolynomial_map_affineGridIdeal α β

theorem quotient_reduced_of_mvAffineGridIdeal_le (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (I : Ideal (MvPolynomial (Fin 2) K)) (hI : mvAffineGridIdeal α β ≤ I) :
    IsReduced (MvPolynomial (Fin 2) K ⧸ I) := by
  apply quotient_reduced_of_surjective_pi_kernel_le (mvAffineGridEvaluation α β)
    (mvAffineGridEvaluation_surjective α β hα hβ) I
  rwa [mvAffineGridEvaluation_ker α β hα hβ]

/-- Grid evaluation also preserves the specified coefficient-field algebra. -/
def affineGridEvaluationAlg (α : Fin m → K) (β : Fin n → K) :
    K[X][Y] →ₐ[K] (Fin m × Fin n → K) where
  toRingHom := affineGridEvaluation α β
  commutes' a := by
    ext ij
    change evalEval (α ij.1) (β ij.2) (C (C a)) = a
    exact evalEval_CC _ _ _

def mvAffineGridEvaluationAlg (α : Fin m → K) (β : Fin n → K) :
    MvPolynomial (Fin 2) K →ₐ[K] (Fin m × Fin n → K) where
  toRingHom := mvAffineGridEvaluation α β
  commutes' a := by
    ext ij
    change mvAffineGridEvaluation α β (MvPolynomial.C a) ij = a
    rw [mvAffineGridEvaluation_apply]
    simp

/-- The full affine CRT identification as a `K`-algebra equivalence. -/
def affineGridQuotientAlgEquiv (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    (K[X][Y] ⧸ affineGridIdeal α β) ≃ₐ[K] (Fin m × Fin n → K) :=
  (Ideal.quotientEquivAlgOfEq K (affineGridEvaluation_ker α β hα hβ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := affineGridEvaluationAlg α β)
      (affineGridEvaluation_surjective α β hα hβ))

def mvAffineGridQuotientAlgEquiv (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    (MvPolynomial (Fin 2) K ⧸ mvAffineGridIdeal α β) ≃ₐ[K] (Fin m × Fin n → K) :=
  (Ideal.quotientEquivAlgOfEq K (mvAffineGridEvaluation_ker α β hα hβ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := mvAffineGridEvaluationAlg α β)
      (mvAffineGridEvaluation_surjective α β hα hβ))

theorem affineGridQuotient_finite (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Module.Finite K (K[X][Y] ⧸ affineGridIdeal α β) :=
  Module.Finite.of_surjective (affineGridQuotientAlgEquiv α β hα hβ).symm.toLinearMap
    (affineGridQuotientAlgEquiv α β hα hβ).symm.surjective

theorem affineGridQuotient_finrank (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Module.finrank K (K[X][Y] ⧸ affineGridIdeal α β) = m * n := by
  rw [(affineGridQuotientAlgEquiv α β hα hβ).toLinearEquiv.finrank_eq]
  simp [Fintype.card_prod]

theorem mvAffineGridQuotient_finite (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Module.Finite K (MvPolynomial (Fin 2) K ⧸ mvAffineGridIdeal α β) :=
  Module.Finite.of_surjective (mvAffineGridQuotientAlgEquiv α β hα hβ).symm.toLinearMap
    (mvAffineGridQuotientAlgEquiv α β hα hβ).symm.surjective

theorem mvAffineGridQuotient_finrank (α : Fin m → K) (β : Fin n → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Module.finrank K (MvPolynomial (Fin 2) K ⧸ mvAffineGridIdeal α β) = m * n := by
  rw [(mvAffineGridQuotientAlgEquiv α β hα hβ).toLinearEquiv.finrank_eq]
  simp [Fintype.card_prod]

end ChoppedPlane.Grid
