module

public import ChoppedPlane.GeneralPoints
public import ChoppedPlane.PrincipalChop
public import ChoppedPlane.Statement

@[expose] public section

/-! The complete main conclusion in the one-generator intermediate range.
Generality is supplied by an explicitly constructed nonempty polynomial open
for the actual point evaluations. No Hilbert-function or regular-sequence
assumption is added to the theorem. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K] {d p : ℕ}

/-- Every distinct configuration with the usual point Hilbert function obeys
all conclusions of Theorem 1.1 in the one-generator range. -/
theorem mainConclusion_one_generator (a : PointCoordinates K p)
    (hd : 1 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : N d - p = 1) (hdist : DistinctPoints K a)
    (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p) :
    MainConclusion K a d := by
  have hdim : finrank K (pointDegreePiece K a d) = 1 := by
    rw [pointDegreePiece_finrank, hpoint d, min_eq_right hhi.le]
    exact hr
  obtain ⟨f, hf, hspace, hIdeal, hregular, hcoeff⟩ :=
    principal_chop_conclusion a (by omega : 0 < d) hdim
  refine ⟨hdist, hpoint, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < d
    · simpa only [expectedChoppedHilbertFunction, ht, ite_true, N] using
        choppedHilbertFunction_below_degree a ht
    · have hseries := congrArg Int.toNat (hcoeff t)
      simpa [expectedChoppedHilbertFunction, ht, not_le.mpr hhi,
        not_le.mpr hlo, hr, completeIntersectionCoefficient] using hseries
  · intro h
    omega
  · intro h
    omega
  · intro _ _
    dsimp only
    rw [hr]
    constructor
    · intro _
      exact principal_chop_regular_generators a (by omega : 0 < d) hdim
    · intro h
      omega

/-- The full one-generator case holds on one actual nonempty principal open,
with every homogeneous degree covered simultaneously. -/
theorem genericChoppedConclusion_one_generator [CharZero K]
    (hd : 1 ≤ d) (_hp : 1 ≤ p) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : N d - p = 1) : GenericChoppedConclusion K d p := by
  obtain ⟨D, hD, hgood⟩ := generic_pointHilbertFunction (K := K) p
  refine ⟨D, hD, ?_⟩
  intro a ha
  obtain ⟨hdist, hpoint⟩ := hgood a ha
  apply mainConclusion_one_generator a hd hlo hhi hr hdist
  simpa only [N] using hpoint

end ChoppedPlane
