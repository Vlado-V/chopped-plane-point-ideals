module

public import ChoppedPlane.GenericAffineChart
public import ChoppedPlane.QuotientMultiplicationChart

@[expose] public section

/-!
# Reduced affine algebras of universal homogeneous row matrices

Starting with an actual primitive and finite-chart open and a split witness,
fixed homogeneous representatives give a quotient basis on a smaller open.
The degree twice as large supplies polynomial relations and product
representatives.  The proved adjugate and trace-discriminant constructions
then produce a nonempty open of reduced algebras.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {c : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
/-- A concrete split witness and the primitive degree-cut open give an actual
reduced finite-algebra open; quotient bases and multiplication matrices are
constructed in the proof. -/
theorem universalRowMatrix_reduced_principal_open
    (δ : Fin (c + 1) → ℕ) (N : ℕ)
    (H₀ : MvPolynomial (RowMatrixParameter δ) K)
    (a₀ : RowMatrixParameter δ → K) (hH₀ : eval a₀ H₀ ≠ 0)
    (hprimitive : ∀ a, eval a H₀ ≠ 0 →
      PrimitiveMaximalMinors (rowMatrixVal δ (universalRowMatrix δ a)))
    (hbinary : ∀ a, eval a H₀ ≠ 0 →
      PrimitiveMaximalMinors (universalInfinityMatrix δ a))
    (hcut : ∀ a, eval a H₀ ≠ 0 → ∀ f : Forms K 2 N,
      f.val ∈ maximalMinorIdeal (universalInfinityMatrix δ a))
    (splitWitness :
      AffineCoordinateAlgebra (maximalMinorIdeal
        (rowMatrixVal δ (universalRowMatrix δ a₀))) ≃ₐ[K] (κ → K)) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
        eval a H₀ ≠ 0 ∧
        IsReduced (AffineCoordinateAlgebra (maximalMinorIdeal
          (rowMatrixVal δ (universalRowMatrix δ a)))) ∧
        Module.Finite K (AffineCoordinateAlgebra (maximalMinorIdeal
          (rowMatrixVal δ (universalRowMatrix δ a)))) ∧
        finrank K (AffineCoordinateAlgebra (maximalMinorIdeal
          (rowMatrixVal δ (universalRowMatrix δ a)))) = Fintype.card κ := by
  classical
  let I (a : RowMatrixParameter δ → K) :=
    maximalMinorIdeal (rowMatrixVal δ (universalRowMatrix δ a))
  let A (a : RowMatrixParameter δ → K) := AffineCoordinateAlgebra (I a)
  let q (t : ℕ) (a : RowMatrixParameter δ → K) :=
    formChartMap (affineQuotientMap (I a)) t
  have hI (a) : (I a).IsHomogeneous (homogeneousSubmodule (Fin 3) K) :=
    maximalMinorIdeal_homogeneous δ _ (rowMatrixVal_homogeneous δ _)
  have hsat (a) (ha : eval a H₀ ≠ 0) :
      ∀ p : Poly K 3, X 2 * p ∈ I a → p ∈ I a :=
    rowMatrix_z_saturated δ _ (hbinary a ha)
  have hCut (a) (ha : eval a H₀ ≠ 0) :
      ∀ f : Forms K 3 N, f.val ∈ I a ⊔ Ideal.span {X (R := K) 2} :=
    rowMatrix_form_cut_of_binary δ _ N (hcut a ha)
  have hfinite (a) (ha : eval a H₀ ≠ 0) : Module.Finite K (A a) :=
    affineCoordinateAlgebra_finite (I a) (hI a) N (hCut a ha)
  let : Module.Finite K (A a₀) := hfinite a₀ hH₀
  let b₀ : Basis κ K (A a₀) := (Pi.basisFun K κ).map splitWitness.symm.toLinearEquiv
  have hdim₀ : finrank K (A a₀) = Fintype.card κ :=
    Module.finrank_eq_card_basis b₀
  have hdimQ₀ : finrank K (Forms K 3 N ⧸ idealFormPiece (I a₀) N) =
      Fintype.card κ :=
    (affineFormQuotientEquiv (I a₀) (hI a₀) (hsat a₀ hH₀) N
      (hCut a₀ hH₀)).finrank_eq.trans hdim₀
  have hdimQ (a) (ha : eval a H₀ ≠ 0) :
      finrank K (Forms K 3 N ⧸ idealFormPiece (I a) N) = Fintype.card κ :=
    (rowMatrix_quotient_finrank_eq δ _ _ (hprimitive a ha)
      (hprimitive a₀ hH₀) N).trans hdimQ₀
  have hdimA (a) (ha : eval a H₀ ≠ 0) : finrank K (A a) = Fintype.card κ :=
    (finrank_affineCoordinateAlgebra (I a) (hI a) (hsat a ha) N
      (hCut a ha)).trans (hdimQ a ha)
  have hsurj₀ : Function.Surjective (q N a₀) :=
    affineFormMap_surjective (I a₀) (hI a₀) N (hCut a₀ hH₀)
  choose v hv using fun i => hsurj₀ (b₀ i)
  have hker (t : ℕ) : (universalDegreeCofactorMap δ t a₀).range =
      (q t a₀).ker := by
    rw [universalDegreeCofactorMap_range]
    exact (ker_formChartMap (affineQuotientMap (I a₀)) (I a₀) t
      (affineQuotientMap_form_eq_zero_iff (I a₀) (hI a₀) (hsat a₀ hH₀) t)).symm
  obtain ⟨r, hrpoly, hrmem, hrbij⟩ := polynomial_relations_for_quotient_basis
    (fun a => universalDegreeCofactorMap δ N a)
    (universalDegreeCofactorMap_isPolynomialFamily δ N) a₀ (q N a₀)
    (hker N) b₀ v hv
  obtain ⟨G, hG₀, hG⟩ := quotient_basis_principal_open
    (fun a => idealFormPiece (I a) N) r v hrpoly
    (fun a i => by rw [← universalDegreeCofactorMap_range]; exact hrmem a i)
    a₀ hrbij
  let H := H₀ * G
  have hH (a) (ha : eval a H ≠ 0) : eval a H₀ ≠ 0 ∧ eval a G ≠ 0 := by
    exact mul_ne_zero_iff.mp (by simpa only [H, map_mul] using ha)
  have hH₀' : eval a₀ H ≠ 0 := by
    simpa only [H, map_mul] using mul_ne_zero hH₀ hG₀
  have hbases (a) (ha : eval a H ≠ 0) :
      ∃ b : Basis κ K (A a), ∀ i, b i = q N a (v i) := by
    obtain ⟨b, hb⟩ := hG a (hH a ha).2 (hdimQ a (hH a ha).1)
    let e := affineFormQuotientEquiv (I a) (hI a) (hsat a (hH a ha).1) N
      (hCut a (hH a ha).1)
    refine ⟨b.map e, fun i => ?_⟩
    rw [Basis.map_apply, hb]
    exact affineFormQuotientEquiv_mk (I a) (hI a) (hsat a (hH a ha).1) N
      (hCut a (hH a ha).1) (v i)
  choose b hb using hbases
  let l (i : κ) : Forms K 3 (2 * N) :=
    ⟨(v i).val * X 2 ^ N, by
      simpa only [Forms, mem_homogeneousSubmodule, ← Nat.two_mul] using
        (v i).property.mul (isHomogeneous_X_pow 2 N)⟩
  let p (i j : κ) : Forms K 3 (2 * N) :=
    ⟨(v i).val * (v j).val, by
      simpa only [Forms, mem_homogeneousSubmodule, ← Nat.two_mul] using
        (v i).property.mul (v j).property⟩
  have hl (a) (ha : eval a H ≠ 0) (i) : q (2 * N) a (l i) = b a ha i := by
    rw [hb a ha]
    simp only [q, l, formChartMap_apply, map_mul, map_pow,
      affineQuotientMap_z, one_pow, mul_one]
  have hp (a) (ha : eval a H ≠ 0) (i j) :
      q (2 * N) a (p i j) = b a ha i * b a ha j := by
    rw [hb a ha, hb a ha]
    simp only [q, p, formChartMap_apply, map_mul]
  obtain ⟨s, hspoly, hsmem, hsbij⟩ := polynomial_relations_for_quotient_basis
    (fun a => universalDegreeCofactorMap δ (2 * N) a)
    (universalDegreeCofactorMap_isPolynomialFamily δ (2 * N)) a₀ (q (2 * N) a₀)
    (hker (2 * N)) (b a₀ hH₀') l (hl a₀ hH₀')
  obtain ⟨D, hD, hred⟩ := reduced_principal_open_of_polynomial_quotient_chart
    A H b (q (2 * N)) s (fun i _ => l i) (fun i j _ => p i j) hspoly
    (fun i => isPolynomialFamily_const (l i))
    (fun i j => isPolynomialFamily_const (p i j))
    (fun a ha i => by
      apply affineQuotientMap_eq_zero_of_mem
      have hs := hsmem a i
      rw [universalDegreeCofactorMap_range] at hs
      exact hs)
    hl hp a₀ hH₀' hsbij splitWitness
  refine ⟨H₀ * D, ?_, fun a ha => ?_⟩
  · simpa only [map_mul] using mul_ne_zero hH₀ hD
  · have hparts : eval a H₀ ≠ 0 ∧ eval a D ≠ 0 :=
      mul_ne_zero_iff.mp (by simpa only [map_mul] using ha)
    exact ⟨hparts.1, hred a hparts.2, hfinite a hparts.1, hdimA a hparts.1⟩

end ChoppedPlane
