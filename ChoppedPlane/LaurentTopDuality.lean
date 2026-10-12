module

public import ChoppedPlane.LaurentWeightedPairing
public import ChoppedPlane.LaurentChartComplex

@[expose] public section

/-! The factorial-weighted perfect pairing on the actual graded top Laurent
representatives. Its composition with the actual chart projection is
surjective and has exactly the actual chart difference as kernel. -/
noncomputable section
namespace ChoppedPlane.LaurentChartComplex
open LaurentPairing Module
variable {K : Type*} [Field K] {J : Type*}

/-- Actual finite top grade perfectly dual to the complementary polynomial
grade, with literal auxiliary factorial weights. -/
def topGradeAuxiliaryResidueDualEquiv [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    topGrade (K := K) (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r) ≃ₗ[K]
      Module.Dual K (positiveGrade (K := K) (auxiliaryGeneratorWeights g t) r) :=
  (topGradeNegativeEquiv (K := K) (auxiliaryGeneratorWeights g t) r).trans
    (auxiliaryResidueDualEquiv g r t)

/-- The actual overlap-to-dual map, obtained by top Laurent projection and
the literal factorial-weighted residue pairing. -/
def topAuxiliaryResidueMap [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    overlapGrade (K := K) (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r) →ₗ[K]
      Module.Dual K (positiveGrade (K := K) (auxiliaryGeneratorWeights g t) r) :=
  (topGradeAuxiliaryResidueDualEquiv g r t).toLinearMap.comp
    (topProjection (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r))

theorem topAuxiliaryResidueMap_surjective [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    Function.Surjective (topAuxiliaryResidueMap (K := K) g r t) :=
  (topGradeAuxiliaryResidueDualEquiv g r t).surjective.comp
    (topProjection_surjective (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r))

/-- The actual chart boundaries are exactly the kernel of the surjective
perfect residue map, proving the top cohomology quotient interpretation. -/
theorem ker_topAuxiliaryResidueMap [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ) :
    LinearMap.ker (topAuxiliaryResidueMap (K := K) g r t) =
      LinearMap.range (chartDifference (K := K)
        (fun i : J × Sym (Fin 3) t => 2 - g i.1) (-r)) := by
  rw [← ker_topProjection]
  ext p
  simp only [LinearMap.mem_ker, topAuxiliaryResidueMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  exact (topGradeAuxiliaryResidueDualEquiv g r t).map_eq_zero_iff

end ChoppedPlane.LaurentChartComplex
