module

public import ChoppedPlane.Points
public import ChoppedPlane.RankOpen

@[expose] public section

/-! General points have the expected Hilbert function on one actual nonempty
principal open for all homogeneous degrees simultaneously. The proof uses
interpolation in the affine chart and determinant opens, with no geometric
rank assumption. -/

noncomputable section
namespace ChoppedPlane
open MvPolynomial Module

variable {K : Type*} [Field K]

/-- The evaluation of a fixed form at a point with universal chart coordinates. -/
def chartEvaluationPolynomial {p d : ℕ} (f : Forms K 3 d) (i : Fin p) :
    MvPolynomial (Fin p × Fin 2) K :=
  eval₂ C ![X (i, 0), X (i, 1), 1] f.val

@[simp] theorem eval_chartEvaluationPolynomial {p d : ℕ} (f : Forms K 3 d)
    (i : Fin p) (a : PointCoordinates K p) :
    eval a (chartEvaluationPolynomial f i) = pointEvaluation K a d f i := by
  rw [chartEvaluationPolynomial, MvPolynomial.eval_eval₂]
  change eval₂ ((eval a).comp C) (fun j => eval a (![X (i, 0), X (i, 1), 1] j)) f.val = _
  have hc : (eval a).comp C = RingHom.id K := by ext c; simp
  rw [hc]
  congr 1
  funext j
  fin_cases j <;> simp [chartPoint]

/-- Point evaluation depends polynomially on the actual chart coefficients. -/
theorem pointEvaluation_isPolynomialFamily (p d : ℕ) :
    IsPolynomialFamily (fun a : PointCoordinates K p => pointEvaluation K a d) := by
  apply isPolynomialFamily_linearMap
  intro f
  have hterm (i : Fin p) : IsPolynomialFamily (fun a : PointCoordinates K p =>
      pointEvaluation K a d f i • (Pi.single i 1 : Fin p → K)) := by
    have hi : IsPolynomialFamily (fun a : PointCoordinates K p => pointEvaluation K a d f i) := by
      simpa only [eval_chartEvaluationPolynomial] using
        isPolynomialFamily_eval (chartEvaluationPolynomial f i)
    exact hi.smul (isPolynomialFamily_const (Pi.single i 1))
  have hs := IsPolynomialFamily.sum hterm
  have heq : (fun a : PointCoordinates K p =>
      ∑ i, pointEvaluation K a d f i • (Pi.single i 1 : Fin p → K)) =
      (fun a => pointEvaluation K a d f) := by
    funext a i
    simp [Pi.single_apply]
  exact heq ▸ hs

/-- The expected Hilbert function in any fixed degree holds on a genuine
nonempty determinant open of the chart configuration space. -/
theorem generic_pointHilbertFunction_at [Infinite K] (p d : ℕ) :
    ∃ D : MvPolynomial (Fin p × Fin 2) K,
      (∃ a : PointCoordinates K p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → pointHilbertFunction K a d = min ((d + 2).choose 2) p := by
  obtain ⟨a₀, ha₀⟩ := exists_pointHilbertFunction_maximal (K := K) p d
  obtain ⟨D, hD, hgood⟩ := rank_polynomial_principal_open
    (fun a : PointCoordinates K p => pointEvaluation K a d)
    (pointEvaluation_isPolynomialFamily p d) a₀
  refine ⟨D, ⟨a₀, hD⟩, fun a ha => le_antisymm (pointHilbertFunction_le a) ?_⟩
  have hl := hgood a ha
  rw [← pointHilbertFunction_eq_rank, ← pointHilbertFunction_eq_rank, ha₀] at hl
  exact hl

/-- Multiplication by the chart coordinate `z` preserves evaluation and
propagates surjectivity to every higher degree. -/
theorem pointEvaluation_surjective_above {p q t : ℕ} (a : PointCoordinates K p)
    (hqt : q ≤ t) (h : Function.Surjective (pointEvaluation K a q)) :
    Function.Surjective (pointEvaluation K a t) := by
  intro y
  obtain ⟨f, hf⟩ := h y
  let g : Forms K 3 t := ⟨f.val * X 2 ^ (t - q), by
    have hh := f.property.mul ((isHomogeneous_X (R := K) (2 : Fin 3)).pow (t - q))
    simpa [Nat.add_sub_of_le hqt] using hh⟩
  refine ⟨g, ?_⟩
  ext i
  change eval (chartPoint K a i) (f.val * X 2 ^ (t - q)) = y i
  simpa [chartPoint] using congrFun hf i

/-- An evaluation rank equal to the point count means the map is surjective. -/
theorem pointEvaluation_surjective_of_hilbert_eq {p q : ℕ} (a : PointCoordinates K p)
    (h : pointHilbertFunction K a q = p) :
    Function.Surjective (pointEvaluation K a q) := by
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simpa [pointHilbertFunction_eq_rank, Module.finrank_pi_fintype] using h

/-- Surjective evaluation gives the constant point count in every higher degree. -/
theorem pointHilbertFunction_constant_above {p q t : ℕ} (a : PointCoordinates K p)
    (hqt : q ≤ t) (h : pointHilbertFunction K a q = p) :
    pointHilbertFunction K a t = p := by
  rw [pointHilbertFunction_eq_rank,
    LinearMap.range_eq_top.mpr (pointEvaluation_surjective_above a hqt
      (pointEvaluation_surjective_of_hilbert_eq a h)), finrank_top]
  simp

/-- An explicit degree sufficient for interpolation of any `p` points. -/
theorem point_count_le_forms (p : ℕ) : p ≤ (p + 2).choose 2 := by
  induction p with
  | zero => omega
  | succ p ih =>
    have hs : (p + 1 + 2).choose 2 = (p + 2).choose 2 + (p + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.choose_succ_succ (p + 2) 1
    rw [hs]
    omega

/-- Polynomial selecting configurations whose first affine coordinates differ. -/
def distinctnessPolynomial (K : Type*) [Field K] (p : ℕ) :
    MvPolynomial (Fin p × Fin 2) K :=
  ∏ ij : {ij : Fin p × Fin p // ij.1 < ij.2}, (X (ij.val.1, 0) - X (ij.val.2, 0))

/-- The displayed configuration condition is genuinely nonempty. -/
theorem distinctnessPolynomial_nonempty [CharZero K] (p : ℕ) :
    ∃ a : PointCoordinates K p, eval a (distinctnessPolynomial K p) ≠ 0 := by
  classical
  refine ⟨fun ik => if ik.2 = 0 then (ik.1.val : K) else 0, ?_⟩
  simp only [distinctnessPolynomial, map_prod, map_sub, eval_X]
  apply Finset.prod_ne_zero_iff.mpr
  intro ij _
  simp only [ite_true]
  apply sub_ne_zero.mpr
  exact_mod_cast (ne_of_lt ij.property : ij.val.1.val ≠ ij.val.2.val)

/-- Nonvanishing of the separation polynomial guarantees distinct projective points. -/
theorem distinctPoints_of_polynomial_ne_zero {p : ℕ} (a : PointCoordinates K p)
    (h : eval a (distinctnessPolynomial K p) ≠ 0) : DistinctPoints K a := by
  classical
  have hall : ∀ ij : {ij : Fin p × Fin p // ij.1 < ij.2},
      a (ij.val.1, 0) - a (ij.val.2, 0) ≠ 0 := by
    simp only [distinctnessPolynomial, map_prod, map_sub, eval_X] at h
    intro ij
    exact (Finset.prod_ne_zero_iff.mp h) ij (Finset.mem_univ ij)
  intro i j hij
  by_contra hn
  have heq : a (i, 0) = a (j, 0) := congrArg Prod.fst hij
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · exact hall ⟨(i, j), hlt⟩ (by simp [heq])
  · exact hall ⟨(j, i), hgt⟩ (by simp [heq])

/-- One nonempty principal open gives distinct points and the expected point
Hilbert function in every degree simultaneously. -/
theorem generic_pointHilbertFunction [CharZero K] (p : ℕ) :
    ∃ D : MvPolynomial (Fin p × Fin 2) K,
      (∃ a : PointCoordinates K p, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → DistinctPoints K a ∧
        ∀ t, pointHilbertFunction K a t = min ((t + 2).choose 2) p := by
  classical
  choose D hD hgood using fun i : Fin (p + 1) => generic_pointHilbertFunction_at (K := K) p i.val
  let E := distinctnessPolynomial K p * ∏ i, D i
  have hne : E ≠ 0 := by
    apply mul_ne_zero
    · obtain ⟨a, ha⟩ := distinctnessPolynomial_nonempty (K := K) p
      intro hz
      simp [hz] at ha
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _
      obtain ⟨a, ha⟩ := hD i
      intro hz
      simp [hz] at ha
  have hex : ∃ a : PointCoordinates K p, eval a E ≠ 0 := by
    by_contra! h
    exact hne (MvPolynomial.funext h)
  refine ⟨E, hex, ?_⟩
  intro a ha
  have hparts : eval a (distinctnessPolynomial K p) ≠ 0 ∧ ∀ i, eval a (D i) ≠ 0 := by
    simpa only [E, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, forall_true_left] using ha
  refine ⟨distinctPoints_of_polynomial_ne_zero a hparts.1, ?_⟩
  intro t
  by_cases ht : t ≤ p
  · exact hgood ⟨t, by omega⟩ a (hparts.2 ⟨t, by omega⟩)
  · have hp : pointHilbertFunction K a p = p := by
      simpa only [min_eq_right (point_count_le_forms p)] using
        hgood ⟨p, by omega⟩ a (hparts.2 ⟨p, by omega⟩)
    have hc := pointHilbertFunction_constant_above a (by omega : p ≤ t) hp
    have hle : p ≤ (t + 2).choose 2 := by
      exact (point_count_le_forms p).trans (Nat.choose_le_choose 2 (by omega))
    simpa only [min_eq_right hle] using hc

end ChoppedPlane
