module

public import ChoppedPlane.ColumnFerrers
public import ChoppedPlane.ChoppedFunctions
public import ChoppedPlane.GeneralPoints

@[expose] public section

/-! Hilbert functions of the actual point ideals supplied by the split seeds. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K] {p c : ℕ}

/-- Equality of actual generated ideals identifies their homogeneous quotient dimensions. -/
theorem generatedHilbertFunction_eq_pointHilbertFunction_of_ideal_eq
    (a : PointCoordinates K p) (U : Submodule K (Poly K 3))
    (hI : Ideal.span (U : Set (Poly K 3)) = pointIdeal K a) (t : ℕ) :
    generatedHilbertFunction U t = pointHilbertFunction K a t := by
  have hker : (formToRingQuotient t U).ker = pointDegreePiece K a t := by
    ext f
    change Ideal.Quotient.mk (Ideal.span (U : Set (Poly K 3))) f.val = 0 ↔
      f ∈ pointDegreePiece K a t
    rw [Ideal.Quotient.eq_zero_iff_mem,hI]
    exact homogeneous_mem_pointIdeal_iff a f
  have h := (formToRingQuotient t U).quotKerEquivRange.finrank_eq
  rw [hker] at h
  exact h.symm

/-- A Hilbert–Burch ideal equal to a point ideal has the actual point Hilbert function. -/
theorem pointHilbertFunction_eq_minorHilbertFunction_of_ideal_eq
    (B : Matrix (Fin (c+1)) (Fin c) (Poly K 3)) (a : PointCoordinates K p)
    (hI : maximalMinorIdeal B = pointIdeal K a) (t : ℕ) :
    pointHilbertFunction K a t = minorHilbertFunction B (t : ℤ) := by
  rw [← generatedHilbertFunction_minorGeneratorSpace]
  symm
  apply generatedHilbertFunction_eq_pointHilbertFunction_of_ideal_eq
  rw [minorGeneratorSpace_idealSpan,hI]

namespace Ferrers

theorem seedMatrix_maximalMinorIdeal_eq_pointIdeal (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    maximalMinorIdeal (seedMatrix δ α β) = pointIdeal K (pointCoordinates δ α β) := by
  change ChoppedPlane.cofactorIdeal (seedMatrix δ α β) = _
  rw [seedMatrix_cofactorIdeal,cofactorIdeal_eq_pointIdeal δ α β hα hβ]

theorem pointHilbertFunction_eq_minorHilbertFunction (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (t : ℕ) :
    pointHilbertFunction K (pointCoordinates δ α β) t =
      minorHilbertFunction (seedMatrix δ α β) (t : ℤ) :=
  pointHilbertFunction_eq_minorHilbertFunction_of_ideal_eq _ _
    (seedMatrix_maximalMinorIdeal_eq_pointIdeal δ α β hα hβ) t

theorem pointHilbertFunction_formula (δ : Fin (c+1) → ℕ) (α β : RootIndex δ → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) (t : ℕ) :
    (pointHilbertFunction K (pointCoordinates δ α β) t : ℤ) = N₂ t -
      (∑ i, N₂ ((t : ℤ) - (∑ j, δ j) + δ i)) +
      (c : ℤ) * N₂ ((t : ℤ) - ∑ i, δ i) := by
  rw [pointHilbertFunction_eq_minorHilbertFunction δ α β hα hβ]
  exact minorHilbertFunction_at_degree _ δ (seedMatrix_homogeneous δ α β)
    (seedMatrix_primitive δ α β) t

end Ferrers
namespace ColumnFerrers

theorem seedMatrix_maximalMinorIdeal_eq_pointIdeal (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    maximalMinorIdeal (seedMatrix ε α β) = pointIdeal K (pointCoordinates ε α β) := by
  change ChoppedPlane.cofactorIdeal (seedMatrix ε α β) = _
  rw [seedMatrix_cofactorIdeal,cofactorIdeal_eq_pointIdeal ε α β hα hβ]

theorem pointHilbertFunction_eq_minorHilbertFunction (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (t : ℕ) :
    pointHilbertFunction K (pointCoordinates ε α β) t =
      minorHilbertFunction (seedMatrix ε α β) (t : ℤ) :=
  pointHilbertFunction_eq_minorHilbertFunction_of_ideal_eq _ _
    (seedMatrix_maximalMinorIdeal_eq_pointIdeal ε α β hα hβ) t

theorem pointHilbertFunction_formula (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) (t : ℕ) :
    (pointHilbertFunction K (pointCoordinates ε α β) t : ℤ) = N₂ t -
      ((c : ℤ)+1) * N₂ ((t : ℤ) - ∑ j, ε j) +
      ∑ j, N₂ ((t : ℤ) - (∑ k, ε k) - ε j) := by
  rw [pointHilbertFunction_eq_minorHilbertFunction ε α β hα hβ]
  exact minorHilbertFunction_columns_at_degree _ ε (seedMatrix_homogeneous ε α β)
    (seedMatrix_primitive ε α β) t

/-- All column-seed cofactors lie in one degree, so chopping there recovers the whole point ideal. -/
theorem choppedIdeal_eq_pointIdeal (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    choppedIdeal K (pointCoordinates ε α β) (∑ j, ε j) =
      pointIdeal K (pointCoordinates ε α β) := by
  apply le_antisymm (choppedIdeal_le_pointIdeal _)
  rw [← cofactorIdeal_eq_pointIdeal ε α β hα hβ]
  apply Ideal.span_le.mpr
  rintro f ⟨k,rfl⟩
  apply Ideal.subset_span
  let g : Forms K 3 (∑ j, ε j) :=
    ⟨cofactorProduct ε α β k,cofactorProduct_homogeneous ε α β k⟩
  change g.val ∈ (pointDegreePiece K (pointCoordinates ε α β) (∑ j, ε j)).map
    (Forms K 3 (∑ j, ε j)).subtype
  apply Submodule.mem_map.mpr
  refine ⟨g,?_,rfl⟩
  apply (homogeneous_mem_pointIdeal_iff _ g).mp
  exact cofactorIdeal_le_pointIdeal ε α β (Ideal.subset_span ⟨k,rfl⟩)

theorem choppedHilbertFunction_eq_pointHilbertFunction (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (t : ℕ) :
    choppedHilbertFunction (pointCoordinates ε α β) (∑ j, ε j) t =
      pointHilbertFunction K (pointCoordinates ε α β) t :=
  generatedHilbertFunction_eq_pointHilbertFunction_of_ideal_eq _ _
    (choppedIdeal_eq_pointIdeal ε α β hα hβ) t

/-- Before the generating degree, the column seed has no nonzero equations. -/
theorem pointHilbertFunction_below_generatingDegree (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    {t : ℕ} (ht : t < ∑ j, ε j) :
    pointHilbertFunction K (pointCoordinates ε α β) t = N t := by
  have h := pointHilbertFunction_formula ε α β hα hβ t
  have hnat : (t : ℤ) < ((∑ j, ε j : ℕ) : ℤ) := by exact_mod_cast ht
  have hneg : (t : ℤ) - ((∑ j, ε j : ℕ) : ℤ) < 0 := sub_neg.mpr hnat
  have hj (j : Fin c) : N₂ ((t : ℤ) - (∑ k, ε k) - ε j) = 0 :=
    N₂_neg (by have := ε j; omega)
  simp_rw [hj] at h
  rw [N₂_neg hneg,N₂_nat] at h
  simp only [mul_zero,sub_zero,Finset.sum_const_zero,add_zero] at h
  exact_mod_cast h

/-- Hilbert–Burch and the selected-cell count give actual degree-`d` interpolation. -/
theorem pointHilbertFunction_at_generatingDegree (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hε : ∀ j, 0 < ε j)
    (hcard : Fintype.card (SelectedIndex ε) = N (∑ j, ε j) - (c+1)) :
    pointHilbertFunction K (pointCoordinates ε α β) (∑ j, ε j) =
      Fintype.card (SelectedIndex ε) := by
  have h := pointHilbertFunction_formula ε α β hα hβ (∑ j, ε j)
  have hj (j : Fin c) : N₂ (-(ε j : ℤ)) = 0 := by
    apply N₂_neg
    have hh : (0 : ℤ) < ε j := by exact_mod_cast hε j
    omega
  simp only [sub_self,zero_sub] at h
  simp_rw [hj] at h
  have hz : N₂ (0 : ℤ) = 1 := by norm_num [N₂,N]
  rw [hz,N₂_nat] at h
  simp only [Finset.sum_const_zero,add_zero,mul_one] at h
  omega

theorem pointEvaluation_surjective_at_generatingDegree (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hε : ∀ j, 0 < ε j)
    (hcard : Fintype.card (SelectedIndex ε) = N (∑ j, ε j) - (c+1)) :
    Function.Surjective (pointEvaluation K (pointCoordinates ε α β) (∑ j, ε j)) :=
  pointEvaluation_surjective_of_hilbert_eq _
    (pointHilbertFunction_at_generatingDegree ε α β hα hβ hε hcard)

/-- This explicit distinct configuration has the full Hilbert function of general points. -/
theorem fullPointHilbertFunction (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) (hε : ∀ j, 0 < ε j)
    (hcard : Fintype.card (SelectedIndex ε) = N (∑ j, ε j) - (c+1)) (t : ℕ) :
    pointHilbertFunction K (pointCoordinates ε α β) t =
      min (N t) (Fintype.card (SelectedIndex ε)) := by
  by_cases ht : t < ∑ j, ε j
  · have hf := pointHilbertFunction_below_generatingDegree ε α β hα hβ ht
    have hle := pointHilbertFunction_le (d := t) (pointCoordinates ε α β)
    change _ ≤ min (N t) _ at hle
    rw [hf] at hle ⊢
    exact le_antisymm hle (min_le_left _ _)
  · have hf := pointHilbertFunction_constant_above (pointCoordinates ε α β)
      (Nat.le_of_not_gt ht) (pointHilbertFunction_at_generatingDegree ε α β hα hβ hε hcard)
    have hle := pointHilbertFunction_le (d := t) (pointCoordinates ε α β)
    change _ ≤ min (N t) _ at hle
    rw [hf] at hle ⊢
    exact le_antisymm hle (min_le_right _ _)

end ColumnFerrers
end ChoppedPlane
