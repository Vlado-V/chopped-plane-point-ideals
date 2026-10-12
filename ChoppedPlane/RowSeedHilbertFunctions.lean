module

public import ChoppedPlane.SeedHilbertFunctions
public import ChoppedPlane.FerrersCounts

@[expose] public section

/-! Full general-point Hilbert functions of the positive row-profile seeds. -/
noncomputable section
namespace ChoppedPlane.Ferrers
open MvPolynomial Module
variable {K : Type*} [Field K] {c d : ℕ}

def quadraticRowCount (δ : Fin (c+1) → ℕ) : ℕ :=
  (Finset.univ.filter (fun i => δ i = 2)).card

theorem pointHilbertFunction_below_generatingDegree (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2)
    {t : ℕ} (ht : t < d) :
    pointHilbertFunction K (pointCoordinates δ α β) t = N t := by
  have h := pointHilbertFunction_formula δ α β hα hβ t
  rw [hsum] at h
  have hnat : (t : ℤ) < d := by exact_mod_cast ht
  have hneg : (t : ℤ) - ((d+2 : ℕ) : ℤ) < 0 := by omega
  have hi (i : Fin (c+1)) : N₂ ((t : ℤ) - ((d+2 : ℕ) : ℤ) + δ i) = 0 := by
    apply N₂_neg
    rcases hδ i with hh | hh <;> rw [hh] <;> omega
  simp_rw [hi] at h
  rw [N₂_neg hneg,N₂_nat] at h
  simp only [Finset.sum_const_zero,sub_zero,mul_zero,add_zero] at h
  exact_mod_cast h

theorem pointHilbertFunction_at_generatingDegree (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2)
    (hcard : Fintype.card (SelectedIndex δ) = N d - quadraticRowCount δ) :
    pointHilbertFunction K (pointCoordinates δ α β) d = Fintype.card (SelectedIndex δ) := by
  classical
  have h := pointHilbertFunction_formula δ α β hα hβ d
  rw [hsum] at h
  have hneg : (d : ℤ) - ((d+2 : ℕ) : ℤ) < 0 := by omega
  have hi (i : Fin (c+1)) :
      N₂ ((d : ℤ) - ((d+2 : ℕ) : ℤ) + δ i) = if δ i = 2 then 1 else 0 := by
    rcases hδ i with hh | hh
    · rw [hh]
      have ht : (d : ℤ) - ((d+2 : ℕ) : ℤ) + 1 = -1 := by omega
      norm_num [ht,N₂]
    · rw [hh]
      have ht : (d : ℤ) - ((d+2 : ℕ) : ℤ) + 2 = 0 := by omega
      norm_num [ht,N₂,N]
  simp_rw [hi] at h
  rw [N₂_neg hneg,N₂_nat] at h
  have hcount : (∑ i : Fin (c+1), if δ i = 2 then (1 : ℤ) else 0) =
      (quadraticRowCount δ : ℤ) := by
    simp [quadraticRowCount]
  rw [hcount] at h
  simp only [mul_zero,add_zero] at h
  omega

theorem pointEvaluation_surjective_at_generatingDegree (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2)
    (hcard : Fintype.card (SelectedIndex δ) = N d - quadraticRowCount δ) :
    Function.Surjective (pointEvaluation K (pointCoordinates δ α β) d) :=
  pointEvaluation_surjective_of_hilbert_eq _
    (pointHilbertFunction_at_generatingDegree δ α β hα hβ hδ hsum hcard)

theorem fullPointHilbertFunction (δ : Fin (c+1) → ℕ) (α β : RootIndex δ → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2)
    (hcard : Fintype.card (SelectedIndex δ) = N d - quadraticRowCount δ) (t : ℕ) :
    pointHilbertFunction K (pointCoordinates δ α β) t =
      min (N t) (Fintype.card (SelectedIndex δ)) := by
  by_cases ht : t < d
  · have hf := pointHilbertFunction_below_generatingDegree δ α β hα hβ hδ hsum ht
    have hle := pointHilbertFunction_le (d := t) (pointCoordinates δ α β)
    change _ ≤ min (N t) _ at hle
    rw [hf] at hle ⊢
    exact le_antisymm hle (min_le_left _ _)
  · have hf := pointHilbertFunction_constant_above (pointCoordinates δ α β)
      (Nat.le_of_not_gt ht) (pointHilbertFunction_at_generatingDegree δ α β hα hβ hδ hsum hcard)
    have hle := pointHilbertFunction_le (d := t) (pointCoordinates δ α β)
    change _ ≤ min (N t) _ at hle
    rw [hf] at hle ⊢
    exact le_antisymm hle (min_le_right _ _)

/-- For one/two row weights the displayed grid count follows from the degree sum. -/
theorem selected_card_one_two (δ : Fin (c+1) → ℕ)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2) :
    Fintype.card (SelectedIndex δ) = N d - quadraticRowCount δ := by
  classical
  have hi (i : Fin (c+1)) : δ i ^ 2 = δ i + 2 * (if δ i = 2 then 1 else 0) := by
    rcases hδ i with hh | hh <;> simp [hh]
  have hsquares : (∑ i, δ i ^ 2) = d+2+2*quadraticRowCount δ := by
    calc
      _ = ∑ i, (δ i + 2 * (if δ i = 2 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hi i
      _ = (∑ i, δ i) + 2 * ∑ i, (if δ i = 2 then 1 else 0) := by
        rw [Finset.sum_add_distrib,Finset.mul_sum]
      _ = _ := by simp [hsum,quadraticRowCount]
  exact selected_card_of_sums δ d (quadraticRowCount δ) hsum hsquares

/-- The explicit positive-row seed interpolates all its points in degree `d`. -/
theorem pointEvaluation_surjective_one_two (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2) :
    Function.Surjective (pointEvaluation K (pointCoordinates δ α β) d) :=
  pointEvaluation_surjective_at_generatingDegree δ α β hα hβ hδ hsum
    (selected_card_one_two δ hδ hsum)

/-- Every split row seed with one/two weights has the full Hilbert function of general points. -/
theorem fullPointHilbertFunction_one_two (δ : Fin (c+1) → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (hδ : ∀ i, δ i = 1 ∨ δ i = 2) (hsum : (∑ i, δ i) = d+2) (t : ℕ) :
    pointHilbertFunction K (pointCoordinates δ α β) t =
      min (N t) (Fintype.card (SelectedIndex δ)) :=
  fullPointHilbertFunction δ α β hα hβ hδ hsum (selected_card_one_two δ hδ hsum) t

end ChoppedPlane.Ferrers
