module

public import ChoppedPlane.GenericHilbertBurchOpen
public import ChoppedPlane.FiniteAffineChart

@[expose] public section

/-! Natural-degree maps and actual affine charts for the universal row matrix. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
attribute [local instance] MvPolynomial.gradedAlgebra
variable {K : Type*} [Field K] {c : ℕ}

def universalDegreeCofactorMap (δ : Fin (c + 1) → ℕ) (N : ℕ)
    (u : RowMatrixParameter δ → K) :
    rowForms K 3 δ ((N : ℤ) - ∑ i, δ i) →ₗ[K] Forms K 3 N where
  toFun v := ⟨(gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
    (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i) v).val, by
      simpa only [sub_add_cancel, signedForms_nat] using
        (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
          (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i) v).property⟩
  map_add' v w := by
    apply Subtype.ext
    exact congrArg (fun x : signedForms K 3
      ((N : ℤ) - ∑ i, δ i + ∑ i, δ i) => x.val)
      (map_add (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
        (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i)) v w)
  map_smul' k v := by
    apply Subtype.ext
    exact congrArg (fun x : signedForms K 3
      ((N : ℤ) - ∑ i, δ i + ∑ i, δ i) => x.val)
      (map_smul (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
        (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i)) k v)

@[simp] theorem universalDegreeCofactorMap_val (δ : Fin (c + 1) → ℕ) (N : ℕ)
    (u : RowMatrixParameter δ → K) (v : rowForms K 3 δ ((N : ℤ) - ∑ i, δ i)) :
    (universalDegreeCofactorMap δ N u v).val =
      (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
        (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i) v).val := rfl

theorem universalDegreeCofactorMap_isPolynomialFamily (δ : Fin (c + 1) → ℕ)
    (N : ℕ) :
    IsPolynomialFamily (fun u : RowMatrixParameter δ → K =>
      universalDegreeCofactorMap δ N u) := by
  classical
  apply isPolynomialFamily_linearMap
  intro v
  have h := (universalRowCofactorMap_isPolynomialFamily (K := K) δ
    ((N : ℤ) - ∑ i, δ i)).linear_comp
      (LinearMap.applyₗ (R := K) v)
  have hval := h.linear_comp (signedForms K 3
    ((N : ℤ) - ∑ i, δ i + ∑ i, δ i)).subtype
  let P : Poly K 3 →ₗ[K] Forms K 3 N :=
    (homogeneousComponent N).codRestrict _ (fun p => homogeneousComponent_mem N p)
  have hp := hval.linear_comp P
  convert hp using 1
  funext u
  apply Subtype.ext
  change _ = homogeneousComponent N _
  simpa only [universalDegreeCofactorMap_val, LinearMap.applyₗ_apply_apply,
    Submodule.subtype_apply] using
      (homogeneousComponent_eq_self (universalDegreeCofactorMap δ N u v).property).symm

theorem universalDegreeCofactorMap_range (δ : Fin (c + 1) → ℕ) (N : ℕ)
    (u : RowMatrixParameter δ → K) :
    (universalDegreeCofactorMap δ N u).range =
      idealFormPiece (maximalMinorIdeal (rowMatrixVal δ (universalRowMatrix δ u))) N := by
  ext f
  constructor
  · rintro ⟨v, rfl⟩
    have hv : gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
        (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i) v ∈
        (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
          (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i)).range := ⟨v, rfl⟩
    rw [gradedCofactorMap_range_eq_idealPiece] at hv
    change (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
      (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i) v).val ∈
        maximalMinorIdeal (rowMatrixVal δ (universalRowMatrix δ u)) at hv
    simpa only [mem_idealFormPiece, universalDegreeCofactorMap_val] using hv
  · intro hf
    let f' : signedForms K 3 ((N : ℤ) - ∑ i, δ i + ∑ i, δ i) :=
      ⟨f.val, by simpa only [sub_add_cancel, signedForms_nat] using f.property⟩
    have hf' : f' ∈ (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
        (rowMatrixVal_homogeneous δ _) ((N : ℤ) - ∑ i, δ i)).range := by
      rw [gradedCofactorMap_range_eq_idealPiece]
      exact hf
    obtain ⟨v, hv⟩ := hf'
    refine ⟨v, ?_⟩
    apply Subtype.ext
    exact congrArg (fun x : signedForms K 3
      ((N : ℤ) - ∑ i, δ i + ∑ i, δ i) => x.val) hv

/-- The actual cofactor ideal commutes with coefficient-ring maps. -/
theorem maximalMinorIdeal_map {R : Type*} [CommRing R]
    (φ : Poly K 3 →+* R) (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) :
    (maximalMinorIdeal B).map φ =
      Ideal.span (Set.range (signedMaximalMinor (B.map φ))) := by
  rw [maximalMinorIdeal, Ideal.map_span]
  congr 1
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, signedMaximalMinor_map φ B i⟩
  · rintro ⟨i, rfl⟩
    exact ⟨signedMaximalMinor B i, ⟨i, rfl⟩, (signedMaximalMinor_map φ B i).symm⟩

/-- Primitive row matrices of the same degrees have identical genuine
homogeneous quotient dimensions. -/
theorem rowMatrix_quotient_finrank_eq (δ : Fin (c + 1) → ℕ)
    (B C : HomogeneousRowMatrix K δ)
    (hB : PrimitiveMaximalMinors (rowMatrixVal δ B))
    (hC : PrimitiveMaximalMinors (rowMatrixVal δ C)) (N : ℕ) :
    finrank K (Forms K 3 N ⧸ idealFormPiece (maximalMinorIdeal (rowMatrixVal δ B)) N) =
      finrank K (Forms K 3 N ⧸ idealFormPiece (maximalMinorIdeal (rowMatrixVal δ C)) N) := by
  have hdegree : ((N : ℤ) - ∑ i, δ i) + ∑ i, δ i = (N : ℤ) := by omega
  have hb := gradedMinorQuotient_finrank (rowMatrixVal δ B) δ
    (rowMatrixVal_homogeneous δ B) hB ((N : ℤ) - ∑ i, δ i)
  have hc := gradedMinorQuotient_finrank (rowMatrixVal δ C) δ
    (rowMatrixVal_homogeneous δ C) hC ((N : ℤ) - ∑ i, δ i)
  unfold gradedMinorIdealPiece at hb hc
  rw [hdegree, signedForms_nat] at hb hc
  exact_mod_cast hb.trans hc.symm

/-- Binary primitive minors make the genuine ternary ideal `z`-saturated. -/
theorem rowMatrix_z_saturated (δ : Fin (c + 1) → ℕ) (B : HomogeneousRowMatrix K δ)
    (hB : PrimitiveMaximalMinors ((rowMatrixVal δ B).map Ferrers.infinityMap)) :
    ∀ p : Poly K 3, X 2 * p ∈ maximalMinorIdeal (rowMatrixVal δ B) →
      p ∈ maximalMinorIdeal (rowMatrixVal δ B) := by
  intro p hp
  exact mem_cofactorIdeal_of_mul (rowMatrixVal δ B) (X 2) (X_ne_zero _)
    Ferrers.infinityMap Ferrers.infinityMap_surjective Ferrers.infinityMap_ker hB p hp

/-- The binary cut is the ternary cut needed for affine finiteness. -/
theorem rowMatrix_form_cut_of_binary (δ : Fin (c + 1) → ℕ)
    (B : HomogeneousRowMatrix K δ) (N : ℕ)
    (hcut : ∀ f : Forms K 2 N,
      f.val ∈ maximalMinorIdeal ((rowMatrixVal δ B).map Ferrers.infinityMap)) :
    ∀ f : Forms K 3 N, f.val ∈
      maximalMinorIdeal (rowMatrixVal δ B) ⊔ Ideal.span {X (R := K) 2} := by
  apply form_cut_of_map Ferrers.infinityMap Ferrers.infinityMap_surjective
    Ferrers.infinityMap_ker
  intro f
  have hf := hcut ⟨Ferrers.infinityMap f.val, infinityMap_homogeneous f.property⟩
  rw [maximalMinorIdeal_map]
  exact hf

end ChoppedPlane
