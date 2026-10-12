module

public import ChoppedPlane.Statement
public import ChoppedPlane.GeneralPoints
public import ChoppedPlane.Propagation

@[expose] public section

/-!
# The two ranges outside the intermediate point count

These are the complete conclusions of Theorem 1.1 when evaluation is already
surjective one degree below the chop, or when the chopped equation space is
zero. The construction uses one genuine nonempty polynomial open.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- Equality of actual ideal pieces identifies the two quotient dimensions. -/
theorem choppedHilbertFunction_eq_point_of_piece_eq {p d t : ℕ}
    (a : PointCoordinates K p) (h : ChopEqualsPointPiece K a d t) :
    choppedHilbertFunction a d t = pointHilbertFunction K a t := by
  have hker : LinearMap.ker (formToRingQuotient t (pointDegreeSpace K a d)) =
      pointDegreePiece K a t := by
    ext f
    change Ideal.Quotient.mk (choppedIdeal K a d) f.val = 0 ↔
      f ∈ pointDegreePiece K a t
    rw [Ideal.Quotient.eq_zero_iff_mem, h f, homogeneous_mem_pointIdeal_iff]
  change finrank K (LinearMap.range (formToRingQuotient t (pointDegreeSpace K a d))) = _
  rw [pointHilbertFunction, ← hker]
  exact (formToRingQuotient t (pointDegreeSpace K a d)).quotKerEquivRange.finrank_eq.symm

/-- A degree chop always agrees with the original point ideal in its own
generating degree. -/
theorem pointDegreeSpace_eq_chop_generating_degree {p d : ℕ}
    (a : PointCoordinates K p) :
    pointDegreeSpace K a d = idealDegreeSpace (choppedIdeal K a d) d := by
  apply le_antisymm
  · intro f hf
    exact ⟨pointDegreeSpace_homogeneous a hf, Ideal.subset_span hf⟩
  · intro f hf
    rw [pointDegreeSpace_eq_idealDegreeSpace]
    exact ⟨hf.1, choppedIdeal_le_pointIdeal a hf.2⟩

/-- Interpolation one degree below the chop makes its homogeneous pieces
agree with the point ideal in all degrees above the chop. -/
theorem chopEqualsPointPiece_of_interpolation {p d : ℕ} (a : PointCoordinates K p)
    (hd : 1 ≤ d)
    (hsurj : Function.Surjective (pointEvaluation K a (d - 1))) :
    ∀ t, d ≤ t → ChopEqualsPointPiece K a d t := by
  have hall := pointDegreeSpace_eq_of_degree_eq a hd hsurj
    (choppedIdeal K a d) (choppedIdeal_le_pointIdeal a)
    (pointDegreeSpace_eq_chop_generating_degree a)
  intro t ht f
  have heq := hall t ht
  rw [pointDegreeSpace_eq_idealDegreeSpace] at heq
  have hh := congrArg (fun U : Submodule K (Poly K 3) => f.val ∈ U) heq
  simpa [idealDegreeSpace, f.property] using hh.symm

/-- The dimension of ternary forms increases strictly at every positive degree. -/
theorem N_pred_lt {d : ℕ} (hd : 1 ≤ d) : N (d - 1) < N d := by
  have hs := N_succ (d - 1)
  rw [show d - 1 + 1 = d by omega] at hs
  omega

/-- The entire main conclusion follows in the range `p ≤ N(d-1)` from the
point Hilbert function on a single configuration. -/
theorem mainConclusion_of_small_point_count {p d : ℕ} (a : PointCoordinates K p)
    (hd : 1 ≤ d) (hp : p ≤ N (d - 1)) (hdist : DistinctPoints K a)
    (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p) :
    MainConclusion K a d := by
  have hpNd : p < N d := hp.trans_lt (N_pred_lt hd)
  have hprev : pointHilbertFunction K a (d - 1) = p := by
    rw [hpoint, min_eq_right hp]
  have hsurj := pointEvaluation_surjective_of_hilbert_eq a hprev
  have hequal := chopEqualsPointPiece_of_interpolation a hd hsurj
  refine ⟨hdist, hpoint, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < d
    · rw [choppedHilbertFunction_below_degree a ht]
      simp [expectedChoppedHilbertFunction, ht, N]
    · rw [choppedHilbertFunction_eq_point_of_piece_eq a (hequal t (by omega))]
      have hconst := pointHilbertFunction_constant_above a
        (show d - 1 ≤ t by omega) hprev
      simpa [expectedChoppedHilbertFunction, ht, not_le.mpr hpNd, hp] using hconst
  · intro hn
    omega
  · intro _
    exact hequal
  · intro hn
    omega

/-- The entire main conclusion follows in the range `N(d) ≤ p` from the
point Hilbert function on a single configuration. -/
theorem mainConclusion_of_large_point_count {p d : ℕ} (a : PointCoordinates K p)
    (hd : 1 ≤ d) (hp : N d ≤ p) (hdist : DistinctPoints K a)
    (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p) :
    MainConclusion K a d := by
  have hdim : pointHilbertFunction K a d = (d + 2).choose 2 := by
    rw [hpoint, min_eq_left hp]
    rfl
  have hi : Function.Injective (pointEvaluation K a d) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    change finrank K (pointDegreePiece K a d) = 0
    rw [pointDegreePiece_finrank, hdim, Nat.sub_self]
  have hpPrev : N (d - 1) < p := (N_pred_lt hd).trans_le hp
  refine ⟨hdist, hpoint, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [choppedHilbertFunction_of_injective a hi]
    by_cases ht : t < d
    · simp [expectedChoppedHilbertFunction, ht, N]
    · rw [expectedChoppedHilbertFunction, ite_eq_right ht, ite_eq_left hp]
      rfl
  · intro _
    exact choppedIdeal_eq_bot_of_injective a hi
  · intro hn
    omega
  · intro _ hn
    omega

/-- A single nonempty principal open proves every conclusion in the two
point-count ranges outside `N(d-1) < p < N(d)`. -/
theorem genericChoppedConclusion_outside_intermediate [CharZero K]
    (d p : ℕ) (hd : 1 ≤ d) (houtside : p ≤ N (d - 1) ∨ N d ≤ p) :
    GenericChoppedConclusion K d p := by
  obtain ⟨D, hD, hgood⟩ := generic_pointHilbertFunction (K := K) p
  refine ⟨D, hD, ?_⟩
  intro a ha
  obtain ⟨hdist, hpoint⟩ := hgood a ha
  have hh : ∀ t, pointHilbertFunction K a t = min (N t) p := by
    simpa [N] using hpoint
  rcases houtside with hp | hp
  · exact mainConclusion_of_small_point_count a hd hp hdist hh
  · exact mainConclusion_of_large_point_count a hd hp hdist hh

end ChoppedPlane
