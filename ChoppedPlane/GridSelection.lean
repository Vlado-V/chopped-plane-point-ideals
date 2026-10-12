module

public import ChoppedPlane.GridHomogeneous
public import ChoppedPlane.RegularSequence
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! The finite coordinate selection in the complete-intersection grid witness. -/
noncomputable section
set_option maxHeartbeats 800000
namespace ChoppedPlane.Grid

open Module Submodule
variable {K : Type*} [Field K] [Infinite K]

/-- The grid's degree-`d` evaluation functionals. -/
def gridEvaluation {d : ℕ} (α β : Fin d → K) (ij : Fin d × Fin d) :
    Module.Dual K (Forms K 3 d) := evaluationLinear K 3 d ![α ij.1, β ij.2, 1]

omit [Infinite K] in
/-- The two grid equations are linearly independent as homogeneous forms. -/
theorem first_second_linearIndependent {d : ℕ} (hd : 0 < d) (α β : Fin d → K) :
    LinearIndependent K (![firstForm α, secondForm β] : Fin 2 → Forms K 3 d) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hc' : c 0 • firstEquation α + c 1 • secondEquation β = 0 := by
    have h := congrArg (fun f : Forms K 3 d => dehom f.val) hc
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Submodule.coe_add, Submodule.coe_smul, Submodule.coe_zero, map_add, map_zero, firstForm, secondForm,
      dehom_smul, dehom_first, dehom_second] using h
  obtain ⟨h0,h1⟩ := grid_equations_independent hd α β hc'
  fin_cases i <;> assumption

/-- The simultaneous grid vanishing space is the two-dimensional equation span. -/
theorem grid_span_coannihilator {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    (span K (Set.range (gridEvaluation α β))).dualCoannihilator =
      span K ({firstForm α,secondForm β} : Set (Forms K 3 d)) := by
  ext f
  rw [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span]
  simp only [Set.mem_ofPred_eq, Set.forall_mem_range, gridEvaluation,
    evaluationLinear_apply, Prod.forall, mem_span_pair]
  exact (grid_forms_kernel hd α β hα hβ f).trans (by
    constructor
    · rintro ⟨a,b,h⟩
      exact ⟨a,b,h.symm⟩
    · rintro ⟨a,b,h⟩
      exact ⟨a,b,h.symm⟩)

/-- The full-grid evaluation rank is precisely `N_d - 2`. -/
theorem grid_span_finrank {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    finrank K (span K (Set.range (gridEvaluation α β))) = (d + 2).choose 2 - 2 := by
  have hrange : Set.range (![firstForm α, secondForm β] : Fin 2 → Forms K 3 d) =
      ({firstForm α,secondForm β} : Set (Forms K 3 d)) := by
    ext f
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  have hk : finrank K (span K ({firstForm α,secondForm β} : Set (Forms K 3 d))) = 2 := by
    rw [← hrange, finrank_span_eq_card (first_second_linearIndependent hd α β)]
    simp
  have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq
    (span K (Set.range (gridEvaluation α β)))
  rw [grid_span_coannihilator hd α β hα hβ, hk, finrank_plane_forms] at hdim
  omega

/-- Select exactly `N_d - 2` pairwise distinct grid coordinates whose evaluations
    span all full-grid evaluations. -/
theorem exists_spanning_grid_coordinates {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    ∃ sel : Fin ((d + 2).choose 2 - 2) → Fin d × Fin d,
      Function.Injective sel ∧
      span K (Set.range (gridEvaluation α β ∘ sel)) =
        span K (Set.range (gridEvaluation α β)) := by
  classical
  obtain ⟨κ,a,ha,hspan,hli⟩ := exists_linearIndependent' K (gridEvaluation α β)
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = (d + 2).choose 2 - 2 := by
    rw [← finrank_span_eq_card hli, hspan]
    exact grid_span_finrank hd α β hα hβ
  let e : Fin ((d + 2).choose 2 - 2) ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e,ha.comp e.injective,?_⟩
  have hset : Set.range (gridEvaluation α β ∘ (a ∘ e)) =
      Set.range (gridEvaluation α β ∘ a) := by
    ext y
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨e i,rfl⟩
    · rintro ⟨k,rfl⟩
      obtain ⟨i,rfl⟩ := e.surjective k
      exact ⟨i,rfl⟩
  rw [hset]
  exact hspan

/-- A subset of exactly `N_d - 2` distinct points retains the exact kernel of the
    complete grid, and its two degree-`d` equations form a regular sequence. -/
theorem exists_grid_subset {d : ℕ} (hd : 0 < d) (α β : Fin d → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    ∃ coords : PointCoordinates K ((d + 2).choose 2 - 2),
      DistinctPoints K coords ∧
      (∀ f : Forms K 3 d,
        (∀ i, MvPolynomial.eval (chartPoint K coords i) f.val = 0) ↔
          ∃ a b : K, f = a • firstForm α + b • secondForm β) ∧
      RingTheory.Sequence.IsRegular (Poly K 3) [planeFirst α,planeSecond β] := by
  classical
  obtain ⟨sel,hsel,hspan⟩ := exists_spanning_grid_coordinates hd α β hα hβ
  let coords : PointCoordinates K ((d + 2).choose 2 - 2) :=
    fun ic => ![α (sel ic.1).1,β (sel ic.1).2] ic.2
  refine ⟨coords,?_,?_,?_⟩
  · intro i j hij
    apply hsel
    apply Prod.ext
    · apply hα
      simpa only [coords, Matrix.cons_val_zero] using congrArg Prod.fst hij
    · apply hβ
      simpa [coords] using congrArg Prod.snd hij
  · intro f
    have hvan : (∀ i, (gridEvaluation α β ∘ sel) i f = 0) ↔
        ∀ ij, gridEvaluation α β ij f = 0 := by
      have hco := congrArg Submodule.dualCoannihilator hspan
      have hf := congrArg (fun W : Submodule K (Forms K 3 d) => f ∈ W) hco
      simpa only [← SetLike.mem_coe, Submodule.coe_dualCoannihilator_span,
        Set.mem_ofPred_eq, Set.forall_mem_range] using (eq_iff_iff.mp hf)
    have hleft : (∀ i, MvPolynomial.eval (chartPoint K coords i) f.val = 0) ↔
        ∀ i, (gridEvaluation α β ∘ sel) i f = 0 := by
      simp only [coords, chartPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
        Function.comp_apply, gridEvaluation, evaluationLinear_apply]
    rw [hleft,hvan]
    simpa only [gridEvaluation, evaluationLinear_apply, Prod.forall] using
      grid_forms_kernel hd α β hα hβ f
  · exact homogeneous_regular_pair hd (firstForm α) (secondForm β)
      (planeFirst_ne_zero α) (plane_equations_relPrime α β)

end ChoppedPlane.Grid

namespace ChoppedPlane.Grid
open MvPolynomial
variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
@[simp] theorem planeFirst_eval_other_infinity {d : ℕ} (hd : 0 < d) (α : Fin d → K) :
    eval ![0,1,0] (planeFirst α) = 0 := by
  classical
  simp [planeFirst, Finset.prod_const, Nat.ne_of_gt hd]

omit [Infinite K] in
@[simp] theorem planeSecond_eval_other_infinity {d : ℕ} (hd : 0 < d) (β : Fin d → K) :
    eval ![1,0,0] (planeSecond β) = 0 := by
  classical
  simp [planeSecond, Finset.prod_const, Nat.ne_of_gt hd]

omit [Infinite K] in
/-- Retaining the two-equation kernel in degree `d` also forces injectivity in
    every smaller degree. -/
theorem lower_form_eq_zero_of_grid_kernel {p d t : ℕ} (hd : 0 < d)
    (α β : Fin d → K) (coords : PointCoordinates K p)
    (hkernel : ∀ f : Forms K 3 d,
      (∀ i, eval (chartPoint K coords i) f.val = 0) ↔
        ∃ a b : K, f = a • firstForm α + b • secondForm β)
    (ht : t < d) (h : Forms K 3 t)
    (hv : ∀ i, eval (chartPoint K coords i) h.val = 0) : h = 0 := by
  let lifted : Forms K 3 d := ⟨X 2 ^ (d - t) * h.val, by
    change (X 2 ^ (d - t) * h.val).IsHomogeneous d
    have hh := (isHomogeneous_X_pow (R := K) (2 : Fin 3) (d - t)).mul h.property
    simpa only [Nat.sub_add_cancel (Nat.le_of_lt ht)] using hh⟩
  have hvl : ∀ i, eval (chartPoint K coords i) lifted.val = 0 := by
    intro i
    simp [lifted, hv i]
  obtain ⟨a,b,hab⟩ := (hkernel lifted).mp hvl
  have ha : a = 0 := by
    have hh := congrArg (fun f : Forms K 3 d => eval ![1,0,0] f.val) hab
    simpa [lifted, firstForm, secondForm, planeSecond_eval_other_infinity hd,
      Nat.ne_of_gt (Nat.sub_pos_of_lt ht), MvPolynomial.smul_eq_C_mul] using hh.symm
  have hb : b = 0 := by
    have hh := congrArg (fun f : Forms K 3 d => eval ![0,1,0] f.val) hab
    simpa [lifted, firstForm, secondForm, planeFirst_eval_other_infinity hd,
      Nat.ne_of_gt (Nat.sub_pos_of_lt ht), MvPolynomial.smul_eq_C_mul] using hh.symm
  have hz : lifted = 0 := by simpa only [ha,hb,zero_smul,zero_add] using hab
  have hval : X 2 ^ (d - t) * h.val = 0 := congrArg Subtype.val hz
  apply Subtype.ext
  exact (mul_eq_zero.mp hval).resolve_left (pow_ne_zero _ (X_ne_zero (2 : Fin 3)))

/-- The complete-intersection witness exists over every infinite field. It has
    exactly `N_d - 2` distinct normalized projective points, a regular pair of
    degree-`d` equations, and no equations of smaller degree. -/
theorem exists_two_generator_witness (d : ℕ) (hd : 0 < d) :
    ∃ (coords : PointCoordinates K ((d + 2).choose 2 - 2))
      (f g : Forms K 3 d),
      DistinctPoints K coords ∧
      (∀ h : Forms K 3 d,
        (∀ i, eval (chartPoint K coords i) h.val = 0) ↔
          ∃ a b : K, h = a • f + b • g) ∧
      RingTheory.Sequence.IsRegular (Poly K 3) [f.val,g.val] ∧
      (∀ t : ℕ, t < d → ∀ h : Forms K 3 t,
        (∀ i, eval (chartPoint K coords i) h.val = 0) → h = 0) := by
  let α : Fin d → K := fun i => Infinite.natEmbedding K i.val
  have hα : Function.Injective α :=
    (Infinite.natEmbedding K).injective.comp Fin.val_injective
  obtain ⟨coords,hcoords,hkernel,hreg⟩ := exists_grid_subset hd α α hα hα
  refine ⟨coords,firstForm α,secondForm α,hcoords,hkernel,hreg,?_⟩
  intro t ht h hv
  exact lower_form_eq_zero_of_grid_kernel hd α α coords hkernel ht h hv

end ChoppedPlane.Grid

namespace ChoppedPlane.Grid
open Module Submodule MvPolynomial
variable {K : Type*} [Field K] [Infinite K]

omit [Infinite K] in
/-- Dimension of the genuine homogeneous equation span. -/
theorem grid_equation_span_finrank {d : ℕ} (hd : 0 < d) (α β : Fin d → K) :
    finrank K (span K ({firstForm α,secondForm β} : Set (Forms K 3 d))) = 2 := by
  have hrange : Set.range (![firstForm α, secondForm β] : Fin 2 → Forms K 3 d) =
      ({firstForm α,secondForm β} : Set (Forms K 3 d)) := by
    ext f
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0,rfl⟩
      · exact ⟨1,rfl⟩
  rw [← hrange, finrank_span_eq_card (first_second_linearIndependent hd α β)]
  simp

omit [Infinite K] in
/-- The degree-`d` piece is the actual two-equation span. -/
theorem degree_piece_eq_grid_span {p d : ℕ} (α β : Fin d → K)
    (coords : PointCoordinates K p)
    (hkernel : ∀ f : Forms K 3 d,
      (∀ i, eval (chartPoint K coords i) f.val = 0) ↔
        ∃ a b : K, f = a • firstForm α + b • secondForm β) :
    pointDegreePiece K coords d =
      span K ({firstForm α,secondForm β} : Set (Forms K 3 d)) := by
  ext f
  rw [mem_pointDegreePiece,mem_span_pair]
  exact (hkernel f).trans (by
    constructor <;> rintro ⟨a,b,h⟩ <;> exact ⟨a,b,h.symm⟩)

omit [Infinite K] in
/-- The selected grid evaluations attain full target rank in degree `d`. -/
theorem grid_subset_evaluation_surjective {d : ℕ} (hd : 0 < d)
    (α β : Fin d → K) (coords : PointCoordinates K ((d + 2).choose 2 - 2))
    (hkernel : ∀ f : Forms K 3 d,
      (∀ i, eval (chartPoint K coords i) f.val = 0) ↔
        ∃ a b : K, f = a • firstForm α + b • secondForm β) :
    Function.Surjective (pointEvaluation K coords d) := by
  have hk : finrank K (pointEvaluation K coords d).ker = 2 := by
    change finrank K (pointDegreePiece K coords d) = 2
    rw [degree_piece_eq_grid_span α β coords hkernel]
    exact grid_equation_span_finrank hd α β
  have hdim := (pointEvaluation K coords d).finrank_range_add_finrank_ker
  rw [hk,finrank_plane_forms] at hdim
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  simp only [Module.finrank_pi_fintype, finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  omega

/-- The r=2 witness with exactly the evaluation-rank conditions used in the
    general-point open conditions. -/
theorem exists_two_generator_rank_witness (d : ℕ) (hd : 0 < d) :
    ∃ (coords : PointCoordinates K ((d + 2).choose 2 - 2)) (f g : Forms K 3 d),
      DistinctPoints K coords ∧
      pointDegreePiece K coords d = span K ({f,g} : Set (Forms K 3 d)) ∧
      finrank K (pointDegreePiece K coords d) = 2 ∧
      Function.Surjective (pointEvaluation K coords d) ∧
      (∀ t : ℕ, t < d → Function.Injective (pointEvaluation K coords t)) ∧
      f.val ≠ 0 ∧ IsRelPrime f.val g.val ∧
      RingTheory.Sequence.IsRegular (Poly K 3) [f.val,g.val] := by
  let α : Fin d → K := fun i => Infinite.natEmbedding K i.val
  have hα : Function.Injective α :=
    (Infinite.natEmbedding K).injective.comp Fin.val_injective
  obtain ⟨coords,hcoords,hkernel,hreg⟩ := exists_grid_subset hd α α hα hα
  refine ⟨coords,firstForm α,secondForm α,hcoords,
    degree_piece_eq_grid_span α α coords hkernel,?_,
    grid_subset_evaluation_surjective hd α α coords hkernel,?_,
    planeFirst_ne_zero α,plane_equations_relPrime α α,hreg⟩
  · rw [degree_piece_eq_grid_span α α coords hkernel]
    exact grid_equation_span_finrank hd α α
  · intro t ht
    apply (injective_iff_map_eq_zero (pointEvaluation K coords t)).mpr
    intro h hh
    apply lower_form_eq_zero_of_grid_kernel hd α α coords hkernel ht h
    intro i
    have hhi := congrFun hh i
    simpa only [pointEvaluation_apply, Pi.zero_apply] using hhi

end ChoppedPlane.Grid
