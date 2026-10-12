module

public import ChoppedPlane.GenericIntermediate
public import ChoppedPlane.PointBaseChange

@[expose] public section

/-! Finite actual point witnesses over an extension field imply every
conclusion over the original characteristic-zero field. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K L : Type*} [Field K] [Field L]

/-- The matrix witnesses may supply a different point configuration in each
of the finitely many relevant degrees, and may be built over an extension.
They still yield one nonempty open over the original field, valid in all degrees. -/
theorem genericChoppedConclusion_of_extension_witnesses [CharZero K]
    (k : K →+* L) (d p : ℕ) (hd : 2 ≤ d)
    (hlo : N (d - 1) < p) (hhi : p < N d) (hr : 3 ≤ N d - p)
    (hw : ∀ e, e ≤ cutoff d (N d - p) →
      ∃ a : PointCoordinates L p,
        Function.Surjective (pointEvaluation L a d) ∧
        choppedHilbertFunction a d (d + e) ≤
          max p (N (d + e) - (N d - p) * N e)) :
    GenericChoppedConclusion K d p := by
  classical
  let c := cutoff d (N d - p)
  choose a₀ hs hupper using fun j : Fin (c + 1) =>
    hw j.val (by have hj := j.isLt; dsimp [c] at *; omega)
  obtain ⟨D, hD, hgood⟩ := choppedHilbertFunction_descend k (show p ≤ (d + 2).choose 2 from hhi.le)
    (fun j : Fin (c + 1) => j.val) a₀ hs
  obtain ⟨G, hG, hgeneral⟩ := generic_pointHilbertFunction (K := K) p
  have hDne : D ≠ 0 := by
    obtain ⟨a, ha⟩ := hD
    intro hz
    rw [hz, map_zero] at ha
    exact ha rfl
  have hGne : G ≠ 0 := by
    obtain ⟨a, ha⟩ := hG
    intro hz
    rw [hz, map_zero] at ha
    exact ha rfl
  have hex : ∃ a : PointCoordinates K p, eval a (D * G) ≠ 0 := by
    by_contra! hz
    exact mul_ne_zero hDne hGne (MvPolynomial.funext hz)
  refine ⟨D * G, hex, fun a ha => ?_⟩
  have hparts : eval a D ≠ 0 ∧ eval a G ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using ha
  obtain ⟨hsa, hlea⟩ := hgood a hparts.1
  obtain ⟨hdist, hpoint⟩ := hgeneral a hparts.2
  have hpoint' : ∀ t, pointHilbertFunction K a t = min (N t) p := by
    simpa only [N] using hpoint
  have hfinite : ∀ e, e ≤ cutoff d (N d - p) →
      choppedHilbertFunction a d (d + e) =
        max p (N (d + e) - (N d - p) * N e) := by
    intro e he
    let j : Fin (c + 1) := ⟨e, by dsimp [c]; omega⟩
    have hu := (hlea j).trans (hupper j)
    have hpd : pointHilbertFunction K a d = p := by
      rw [hpoint', min_eq_right hhi.le]
    have hk : finrank K (pointDegreePiece K a d) = N d - p := by
      rw [pointDegreePiece_finrank, hpd]
      rfl
    have hl := choppedHilbertFunction_lower_bounds (d := d) (e := e) a
    rw [pointHilbertFunction_above_intermediate a hhi hpoint', hk] at hl
    exact le_antisymm hu hl
  exact mainConclusion_of_intermediate_formula a hd hlo hhi hr hdist hpoint'
    (intermediate_formula_of_finite_witness a hhi hr hpoint' hsa hfinite)

end ChoppedPlane
