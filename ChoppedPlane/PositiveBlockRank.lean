module

public import ChoppedPlane.RowProfiles
public import ChoppedPlane.RowChopPresentation

@[expose] public section

/-! The actual signed bottom block has maximal rank whenever its genuine
matrix of linear forms has maximal rank in every ordinary twist. -/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial
variable {K : Type*} [Field K] {r a : ℕ}

/-- Degree transport for homogeneous forms preserves the polynomial. -/
def signedFormsEquivNatOfEq {n : ℕ} {t : ℤ} (m : ℕ) (h : t = (m : ℤ)) :
    signedForms K n t ≃ₗ[K] Forms K n m where
  toFun f := ⟨f.val, by simpa only [h, signedForms_nat] using f.property⟩
  invFun f := ⟨f.val, by simpa only [h, signedForms_nat] using f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem signedFormsEquivNatOfEq_val {n : ℕ} {t : ℤ}
    (m : ℕ) (h : t = (m : ℤ)) (f : signedForms K n t) :
    (signedFormsEquivNatOfEq m h f).val = f.val := rfl

@[simp] theorem signedFormsEquivNatOfEq_symm_val {n : ℕ} {t : ℤ}
    (m : ℕ) (h : t = (m : ℤ)) (f : Forms K n m) :
    ((signedFormsEquivNatOfEq (K := K) m h).symm f).val = f.val := rfl

@[simp] theorem positive_linearRow_eq (hr : 0 < r) (i : Fin a) :
    linearRow (positiveRowColumns_rows r a hr).symm i = positiveLinearRowIndex hr i := by
  apply Fin.ext
  rfl

/-- The profile used for generic matrices is the profile used in the actual
row presentation. -/
theorem positiveRowMatrix_standard_homogeneous (B : HomogeneousRowMatrix K
    (positiveRowProfile r a)) :
    ∀ i j, (rowMatrixVal (positiveRowProfile r a) B i j).IsHomogeneous
      (standardRowDegrees r (positiveRowColumns r a) i) :=
  fun i j => (B i j).property

/-- The two vacuous signed source degrees and every ordinary twist fit the
same literal finite-dimensional maximal-rank statement. -/
theorem positiveRowLinearBlock_maximalRank (hr : 0 < r)
    (B : HomogeneousRowMatrix K (positiveRowProfile r a))
    (hmax : ∀ t, LinearMatrixMaximalRank (positiveLinearBlock hr B) t) (e : ℕ) :
    finrank K (rowLinearBlockMap (rowMatrixVal (positiveRowProfile r a) B)
        (positiveRowColumns_rows r a hr).symm (positiveRowMatrix_standard_homogeneous B)
        (e : ℤ)).range =
      min (finrank K (Fin (positiveRowColumns r a) → signedForms K 3 ((e : ℤ) - 2)))
        (finrank K (Fin a → signedForms K 3 ((e : ℤ) - 1))) := by
  classical
  let f := rowLinearBlockMap (rowMatrixVal (positiveRowProfile r a) B)
    (positiveRowColumns_rows r a hr).symm (positiveRowMatrix_standard_homogeneous B) (e : ℤ)
  change finrank K f.range = _
  by_cases he : 2 ≤ e
  · let t := e - 2
    have hs : (e : ℤ) - 2 = (t : ℤ) := by dsimp [t]; omega
    have ht : (e : ℤ) - 1 = ((t + 1 : ℕ) : ℤ) := by dsimp [t]; omega
    let S : (Fin (positiveRowColumns r a) → signedForms K 3 ((e : ℤ) - 2)) ≃ₗ[K]
        MatrixSource K (positiveRowColumns r a) t :=
      LinearEquiv.piCongrRight (fun _ => signedFormsEquivNatOfEq t hs)
    let T : (Fin a → signedForms K 3 ((e : ℤ) - 1)) ≃ₗ[K] MatrixTarget K a t :=
      LinearEquiv.piCongrRight (fun _ => signedFormsEquivNatOfEq (t + 1) ht)
    have hmap : T.toLinearMap.comp (f.comp S.symm.toLinearMap) =
        linearMatrixMap (positiveLinearBlock hr B) t := by
      apply LinearMap.ext
      intro v
      funext i
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        linearMatrixMap_val, positiveLinearBlock_val]
      change (f (S.symm v) i).val = _
      simp only [f, rowLinearBlockMap_val, rowMatrixVal,
        S, LinearEquiv.piCongrRight_symm, LinearEquiv.piCongrRight_apply,
        signedFormsEquivNatOfEq_symm_val]
      rw [positive_linearRow_eq hr i]
    have hgr : (linearMatrixMap (positiveLinearBlock hr B) t).range = f.range.map T.toLinearMap := by
      rw [← hmap, LinearMap.range_comp,
        LinearMap.range_comp_of_range_eq_top f S.symm.range]
    have hrank : finrank K (linearMatrixMap (positiveLinearBlock hr B) t).range =
        finrank K f.range := by rw [hgr]; exact T.finrank_map_eq f.range
    rw [← hrank, hmax t, S.finrank_eq, T.finrank_eq]
  · have hs : ¬ (0 : ℤ) ≤ (e : ℤ) - 2 := by omega
    have hzero : finrank K (Fin (positiveRowColumns r a) → signedForms K 3 ((e : ℤ) - 2)) = 0 := by
      rw [show signedForms K 3 ((e : ℤ) - 2) = ⊥ from ite_eq_right hs]
      simp [Module.finrank_pi_fintype]
    have hle := LinearMap.finrank_range_le f
    rw [hzero] at hle
    rw [hzero, min_eq_left (Nat.zero_le _)]
    omega

end ChoppedPlane
