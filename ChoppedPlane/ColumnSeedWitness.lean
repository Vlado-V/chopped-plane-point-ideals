module

public import ChoppedPlane.ColumnFerrersCounts
public import ChoppedPlane.ColumnFerrersAffineQuotient
public import ChoppedPlane.SeedHilbertFunctions

@[expose] public section

/-!
A concrete witness for the range with no extra generators: canonical separated
roots in the column-graded Ferrers matrix produce exactly `N d - r` distinct
points, their general-point Hilbert function, and their degree-`d` chop.
-/
noncomputable section
namespace ChoppedPlane
variable {K : Type*} [Field K] {p q : ℕ}

/-- Transport the length of an ordered configuration along a proved equality. -/
def castPointCoordinates (h : p = q) (a : PointCoordinates K p) : PointCoordinates K q := h ▸ a

omit [Field K] in
@[simp] theorem distinct_castPointCoordinates (h : p = q) (a : PointCoordinates K p) :
    DistinctPoints K (castPointCoordinates h a) ↔ DistinctPoints K a := by cases h; rfl

@[simp] theorem surjective_castPointCoordinates (h : p = q) (a : PointCoordinates K p) (d : ℕ) :
    Function.Surjective (pointEvaluation K (castPointCoordinates h a) d) ↔
      Function.Surjective (pointEvaluation K a d) := by cases h; rfl

@[simp] theorem pointHilbertFunction_castPointCoordinates (h : p = q)
    (a : PointCoordinates K p) (t : ℕ) :
    pointHilbertFunction K (castPointCoordinates h a) t = pointHilbertFunction K a t := by
  cases h
  rfl

@[simp] theorem choppedHilbertFunction_castPointCoordinates (h : p = q)
    (a : PointCoordinates K p) (d t : ℕ) :
    choppedHilbertFunction (castPointCoordinates h a) d t = choppedHilbertFunction a d t := by
  cases h
  rfl

@[simp] theorem choppedIdeal_castPointCoordinates (h : p = q)
    (a : PointCoordinates K p) (d : ℕ) :
    choppedIdeal K (castPointCoordinates h a) d = choppedIdeal K a d := by cases h; rfl

@[simp] theorem pointIdeal_castPointCoordinates (h : p = q) (a : PointCoordinates K p) :
    pointIdeal K (castPointCoordinates h a) = pointIdeal K a := by cases h; rfl

private theorem castPointCoordinates_properties (h : p = q) (a : PointCoordinates K p)
    (d n : ℕ) :
    (DistinctPoints K (castPointCoordinates h a) ∧
      Function.Surjective (pointEvaluation K (castPointCoordinates h a) d) ∧
      choppedIdeal K (castPointCoordinates h a) d = pointIdeal K (castPointCoordinates h a) ∧
      (∀ t, pointHilbertFunction K (castPointCoordinates h a) t = min (N t) n) ∧
      (∀ t, choppedHilbertFunction (castPointCoordinates h a) d t = min (N t) n)) ↔
    (DistinctPoints K a ∧ Function.Surjective (pointEvaluation K a d) ∧
      choppedIdeal K a d = pointIdeal K a ∧
      (∀ t, pointHilbertFunction K a t = min (N t) n) ∧
      (∀ t, choppedHilbertFunction a d t = min (N t) n)) := by
  cases h
  rfl

namespace ColumnFerrers
variable [Infinite K]

/-- A fixed displayed configuration: the same canonical separated roots are
used in the vertical and horizontal directions. -/
def canonicalColumnCoordinates (d r : ℕ) :
    PointCoordinates K (Fintype.card (SelectedIndex (columnProfile (r - 1) (d + 1 - r)))) :=
  pointCoordinates (columnProfile (r - 1) (d + 1 - r))
    (Ferrers.canonicalRoots (K := K) _) (Ferrers.canonicalRoots (K := K) _)

/-- The canonical seed realizes the general-point Hilbert function in every
degree, and the chop already equals its actual saturated point ideal. -/
theorem canonicalColumnCoordinates_properties {d r : ℕ}
    (hr : 1 ≤ r) (hupper : r ≤ d + 1) (hlower : d + 2 ≤ 2 * r) :
    DistinctPoints K (canonicalColumnCoordinates (K := K) d r) ∧
    Function.Surjective (pointEvaluation K (canonicalColumnCoordinates (K := K) d r) d) ∧
    choppedIdeal K (canonicalColumnCoordinates (K := K) d r) d =
      pointIdeal K (canonicalColumnCoordinates (K := K) d r) ∧
    (∀ t, pointHilbertFunction K (canonicalColumnCoordinates (K := K) d r) t =
      min (N t) (N d - r)) ∧
    (∀ t, choppedHilbertFunction (canonicalColumnCoordinates (K := K) d r) d t =
      min (N t) (N d - r)) := by
  let ε := columnProfile (r - 1) (d + 1 - r)
  let α : RootIndex ε → K := Ferrers.canonicalRoots ε
  have hα : Function.Injective α := Ferrers.canonicalRoots_injective ε
  have hε : ∀ j, 0 < ε j := columnProfile_pos _ _
  have hq : d + 1 - r ≤ r - 1 := by omega
  have hsum : (∑ j, ε j) = d := by
    dsimp [ε]
    rw [columnProfile_sum _ _ hq]
    omega
  have hc : r - 1 + 1 = r := by omega
  have hcount : Fintype.card (SelectedIndex ε) = N d - r :=
    columnProfile_selected_card hr hupper hlower
  have hcard : Fintype.card (SelectedIndex ε) = N (∑ j, ε j) - (r - 1 + 1) := by
    rw [hsum, hc]
    exact hcount
  have hfull (t : ℕ) : pointHilbertFunction K (pointCoordinates ε α α) t =
      min (N t) (N d - r) := by
    rw [fullPointHilbertFunction ε α α hα hα hε hcard t, hcount]
  change DistinctPoints K (pointCoordinates ε α α) ∧
    Function.Surjective (pointEvaluation K (pointCoordinates ε α α) d) ∧
    choppedIdeal K (pointCoordinates ε α α) d = pointIdeal K (pointCoordinates ε α α) ∧
    (∀ t, pointHilbertFunction K (pointCoordinates ε α α) t = min (N t) (N d - r)) ∧
    (∀ t, choppedHilbertFunction (pointCoordinates ε α α) d t = min (N t) (N d - r))
  refine ⟨distinct_pointCoordinates ε α α hα hα, ?_, ?_, hfull, ?_⟩
  · exact hsum ▸ pointEvaluation_surjective_at_generatingDegree ε α α hα hα hε hcard
  · simpa only [hsum] using choppedIdeal_eq_pointIdeal ε α α hα hα
  · intro t
    have hh := choppedHilbertFunction_eq_pointHilbertFunction ε α α hα hα t
    rw [hsum] at hh
    exact hh.trans (hfull t)

/-- The same explicit seed, with its length transported to precisely `N d - r`. -/
def columnSeedCoordinates (d r : ℕ) (hr : 1 ≤ r)
    (hupper : r ≤ d + 1) (hlower : d + 2 ≤ 2 * r) : PointCoordinates K (N d - r) :=
  castPointCoordinates (columnProfile_selected_card hr hupper hlower)
    (canonicalColumnCoordinates (K := K) d r)

theorem columnSeedCoordinates_properties {d r : ℕ} (hr : 1 ≤ r)
    (hupper : r ≤ d + 1) (hlower : d + 2 ≤ 2 * r) :
    DistinctPoints K (columnSeedCoordinates (K := K) d r hr hupper hlower) ∧
    Function.Surjective (pointEvaluation K (columnSeedCoordinates (K := K) d r hr hupper hlower) d) ∧
    choppedIdeal K (columnSeedCoordinates (K := K) d r hr hupper hlower) d =
      pointIdeal K (columnSeedCoordinates (K := K) d r hr hupper hlower) ∧
    (∀ t, pointHilbertFunction K (columnSeedCoordinates (K := K) d r hr hupper hlower) t =
      min (N t) (N d - r)) ∧
    (∀ t, choppedHilbertFunction (columnSeedCoordinates (K := K) d r hr hupper hlower) d t =
      min (N t) (N d - r)) := by
  exact (castPointCoordinates_properties (columnProfile_selected_card hr hupper hlower)
    (canonicalColumnCoordinates (K := K) d r) d (N d - r)).mpr
    (canonicalColumnCoordinates_properties (K := K) hr hupper hlower)

/-- Existence on the paper's exact number of ordered points, witnessed by the
displayed canonical-root matrix construction. -/
theorem exists_columnSeedWitness {d r : ℕ} (hr : 1 ≤ r)
    (hupper : r ≤ d + 1) (hlower : d + 2 ≤ 2 * r) :
    ∃ a : PointCoordinates K (N d - r), DistinctPoints K a ∧
      Function.Surjective (pointEvaluation K a d) ∧
      choppedIdeal K a d = pointIdeal K a ∧
      (∀ t, pointHilbertFunction K a t = min (N t) (N d - r)) ∧
      (∀ t, choppedHilbertFunction a d t = min (N t) (N d - r)) :=
  ⟨columnSeedCoordinates d r hr hupper hlower,
    columnSeedCoordinates_properties hr hupper hlower⟩

end ColumnFerrers
end ChoppedPlane
