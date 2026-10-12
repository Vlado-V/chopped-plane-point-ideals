module

public import ChoppedPlane.Toeplitz
public import Mathlib.Data.Matrix.Block
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

noncomputable section

namespace ChoppedPlane

variable {K : Type*} [Field K]

/-- The direct sum of two matrices of linear forms. -/
def linearMatrixBlock {a₁ a₂ c₁ c₂ : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂) :
    LinearMatrix K (a₁ + a₂) (c₁ + c₂) :=
  (Matrix.fromBlocks L₁ 0 0 L₂).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

@[simp] theorem linearMatrixBlock_left {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (v : MatrixSource K (c₁+c₂) t) (i : Fin a₁) :
    linearMatrixMap (linearMatrixBlock L₁ L₂) t v (Fin.castAdd a₂ i) =
      linearMatrixMap L₁ t (fun j => v (Fin.castAdd c₂ j)) i := by
  apply Subtype.ext
  simp [linearMatrixMap_val, linearMatrixBlock, Fin.sum_univ_add]

@[simp] theorem linearMatrixBlock_right {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (v : MatrixSource K (c₁+c₂) t) (i : Fin a₂) :
    linearMatrixMap (linearMatrixBlock L₁ L₂) t v (Fin.natAdd a₁ i) =
      linearMatrixMap L₂ t (fun j => v (Fin.natAdd c₁ j)) i := by
  apply Subtype.ext
  simp [linearMatrixMap_val, linearMatrixBlock, Fin.sum_univ_add]

theorem linearMatrixBlock_injective {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (h₁ : Function.Injective (linearMatrixMap L₁ t))
    (h₂ : Function.Injective (linearMatrixMap L₂ t)) :
    Function.Injective (linearMatrixMap (linearMatrixBlock L₁ L₂) t) := by
  intro v w h
  have hleft : (fun j : Fin c₁ => v (Fin.castAdd c₂ j)) =
      (fun j : Fin c₁ => w (Fin.castAdd c₂ j)) := by
    apply h₁
    funext i
    simpa only [linearMatrixBlock_left] using congrFun h (Fin.castAdd a₂ i)
  have hright : (fun j : Fin c₂ => v (Fin.natAdd c₁ j)) =
      (fun j : Fin c₂ => w (Fin.natAdd c₁ j)) := by
    apply h₂
    funext i
    simpa only [linearMatrixBlock_right] using congrFun h (Fin.natAdd a₁ i)
  funext j
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases j with
  | inl j => simpa using congrFun hleft j
  | inr j => simpa using congrFun hright j

theorem linearMatrixBlock_surjective {a₁ a₂ c₁ c₂ t : ℕ}
    (L₁ : LinearMatrix K a₁ c₁) (L₂ : LinearMatrix K a₂ c₂)
    (h₁ : Function.Surjective (linearMatrixMap L₁ t))
    (h₂ : Function.Surjective (linearMatrixMap L₂ t)) :
    Function.Surjective (linearMatrixMap (linearMatrixBlock L₁ L₂) t) := by
  intro y
  obtain ⟨v₁, hv₁⟩ := h₁ (fun i => y (Fin.castAdd a₂ i))
  obtain ⟨v₂, hv₂⟩ := h₂ (fun i => y (Fin.natAdd a₁ i))
  let v : MatrixSource K (c₁+c₂) t :=
    fun j => Sum.elim v₁ v₂ (finSumFinEquiv.symm j)
  refine ⟨v, ?_⟩
  funext i
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  cases i with
  | inl i => simpa [v] using congrFun hv₁ i
  | inr i => simpa [v] using congrFun hv₂ i

/-- The rank-two block is surjective on and above its crossing. This also
includes the block with no rows and two columns. -/
theorem toeplitzMatrix_surjective_at_or_above {a t : ℕ} (hat : a ≤ t + 1) :
    Function.Surjective (linearMatrixMap (toeplitzMatrix K a) t) := by
  by_cases ha : 0 < a
  · apply (linearMatrixMaximalRank_iff_surjective (toeplitzMatrix K a) t
      ((matrixTarget_le_source_iff K a (a+2) t).mpr (by nlinarith))).mp
    exact toeplitzMatrix_maximalRank ha t
  · have ha0 : a = 0 := by omega
    subst a
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Balanced rank-two blocks have a common pair of rank thresholds. There
are `q` blocks, `r` of row count `m+1` and the others of row count `m`. -/
theorem exists_balanced_toeplitz_blocks (q m r : ℕ) (hr : r ≤ q) :
    ∃ L : LinearMatrix K (q*m+r) (q*m+r+2*q),
      (∀ t, t < m → Function.Injective (linearMatrixMap L t)) ∧
      (∀ t, m ≤ t → Function.Surjective (linearMatrixMap L t)) := by
  induction q generalizing r with
  | zero =>
      have hr0 : r = 0 := by omega
      subst r
      refine ⟨0, ?_, ?_⟩
      · intro t ht v w h
        funext i
        have hi := i.isLt
        omega
      · intro t ht y
        refine ⟨0, ?_⟩
        funext i
        have hi := i.isLt
        omega
  | succ q ih =>
      cases r with
      | zero =>
          obtain ⟨L, hinj, hsurj⟩ := ih 0 (by omega)
          have hrow : (q+1)*m+0 = m+(q*m+0) := by ring
          rw [hrow]
          have hcol : m+(q*m+0)+2*(q+1) = (m+2)+(q*m+0+2*q) := by ring
          rw [hcol]
          refine ⟨linearMatrixBlock (toeplitzMatrix K m) L, ?_, ?_⟩
          · intro t ht
            exact linearMatrixBlock_injective _ _ (toeplitzMatrix_injective ht)
              (hinj t ht)
          · intro t ht
            exact linearMatrixBlock_surjective _ _
              (toeplitzMatrix_surjective_at_or_above (by omega)) (hsurj t ht)
      | succ r =>
          obtain ⟨L, hinj, hsurj⟩ := ih r (by omega)
          have hrow : (q+1)*m+(r+1) = (m+1)+(q*m+r) := by ring
          rw [hrow]
          have hcol : (m+1)+(q*m+r)+2*(q+1) = (m+1+2)+(q*m+r+2*q) := by ring
          rw [hcol]
          refine ⟨linearMatrixBlock (toeplitzMatrix K (m+1)) L, ?_, ?_⟩
          · intro t ht
            exact linearMatrixBlock_injective _ _ (toeplitzMatrix_injective (by omega))
              (hinj t ht)
          · intro t ht
            exact linearMatrixBlock_surjective _ _
              (toeplitzMatrix_surjective_at_or_above (by omega)) (hsurj t ht)

/-- Every even positive column defect has an explicit matrix with maximal
rank in every degree, over any field. -/
theorem exists_even_extra_columns_maximalRank (a q : ℕ) (hq : 0 < q) :
    ∃ L : LinearMatrix K a (a+2*q), ∀ t, LinearMatrixMaximalRank L t := by
  have hdecomp : q*(a/q)+(a%q) = a := by
    have h := Nat.mod_add_div a q
    omega
  have hex := exists_balanced_toeplitz_blocks (K := K) q (a/q) (a%q)
    (Nat.le_of_lt (Nat.mod_lt a hq))
  rw [hdecomp] at hex
  obtain ⟨L, hinj, hsurj⟩ := hex
  refine ⟨L, ?_⟩
  intro t
  by_cases ht : t < a/q
  · exact linearMatrixMaximalRank_of_injective L t (hinj t ht)
  · exact linearMatrixMaximalRank_of_surjective L t (hsurj t (by omega))

/-- If there are at least three columns per row, a matrix can be chosen
surjective in every degree. Extra columns may be filled with zeros. -/
theorem exists_many_columns_maximalRank (a c : ℕ) (hac : 3*a ≤ c) :
    ∃ L : LinearMatrix K a c, ∀ t, LinearMatrixMaximalRank L t := by
  by_cases ha : 0 < a
  · have hex := exists_even_extra_columns_maximalRank (K := K) a a ha
    have hthree : a+2*a = 3*a := by omega
    rw [hthree] at hex
    obtain ⟨L, hmax⟩ := hex
    have hsurj0 : Function.Surjective (linearMatrixMap L 0) := by
      apply (linearMatrixMaximalRank_iff_surjective L 0
        ((matrixTarget_le_source_iff K a (3*a) 0).mpr (by omega))).mp
      exact hmax 0
    have hsurj : ∀ t, Function.Surjective (linearMatrixMap L t) :=
      fun t => linearMatrixMap_surjective_upward L (Nat.zero_le t) hsurj0
    have hc : c = 3*a+(c-3*a) := by omega
    rw [hc]
    let Z : LinearMatrix K 0 (c-3*a) := 0
    refine ⟨linearMatrixBlock L Z, ?_⟩
    intro t
    apply linearMatrixMaximalRank_of_surjective
    apply linearMatrixBlock_surjective L Z (hsurj t)
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩
  · have ha0 : a = 0 := by omega
    subst a
    refine ⟨0, ?_⟩
    intro t
    apply linearMatrixMaximalRank_of_surjective
    intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end ChoppedPlane
