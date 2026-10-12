module

public import ChoppedPlane.ColumnSeedWitness
public import ChoppedPlane.GenericIntermediate

@[expose] public section

/-! Complete generic conclusion in the branch with no additional generators. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K] [CharZero K]

/-- The column-weighted split grid proves the full theorem when `a ≤ 0`,
including the actual ideal equality and least positive filling degree. -/
theorem genericChoppedConclusion_nonpositive
    (d p : ℕ) (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : 3 ≤ N d - p) (ha : aCount d (N d - p) ≤ 0) :
    GenericChoppedConclusion K d p := by
  classical
  let r := N d - p
  have hrd : r ≤ d := (generator_count_bounds (by omega) hlo hhi).2
  have hpr : N d - r = p := by dsimp [r]; omega
  have hlow : d + 2 ≤ 2 * r := by dsimp [r, aCount] at *; omega
  obtain ⟨b, _, hs, _, _, hb⟩ := ColumnFerrers.exists_columnSeedWitness
    (K := K) (show 1 ≤ r from by dsimp [r]; omega) (show r ≤ d + 1 by omega) hlow
  let a : PointCoordinates K p := castPointCoordinates hpr b
  have hsa : Function.Surjective (pointEvaluation K a d) := by
    simpa only [a, surjective_castPointCoordinates] using hs
  have hcut : cutoff d (N d - p) = 1 := cutoff_eq_one_of_aCount_nonpos hr ha
  apply genericChoppedConclusion_intermediate_of_witness d p hd hlo hhi hr a hsa
  intro e he
  have hchop : choppedHilbertFunction a d (d + e) = p := by
    rw [show choppedHilbertFunction a d (d + e) = choppedHilbertFunction b d (d + e) from
      choppedHilbertFunction_castPointCoordinates hpr b d (d + e), hb, hpr]
    apply min_eq_right
    exact hhi.le.trans (by dsimp [N]; exact Nat.choose_le_choose 2 (by omega))
  rw [hchop]
  by_cases he0 : e = 0
  · subst e
    simp [N]
    dsimp [N] at hhi
    omega
  · exact ((intermediate_max_eq_point_iff hhi hr (by omega)).mpr (by rw [hcut]; omega)).symm

end ChoppedPlane
