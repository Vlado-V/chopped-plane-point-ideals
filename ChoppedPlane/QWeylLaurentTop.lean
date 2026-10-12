module

public import ChoppedPlane.QWeylLaurentOperatorGrading
public import ChoppedPlane.QWeylLaurentExactness
public import ChoppedPlane.ConcreteCechDuality
public import ChoppedPlane.ProfileLaurentKernel

@[expose] public section

/-!
# The actual profile multiplier on the finite top Laurent quotient

The top multiplier is literal negative-exponent projection of the actual
cyclic-module multiplier.  Its injectivity follows from the proved unit-chart
cross exactness and the actual global polynomial directional kernel.
-/

noncomputable section
namespace ChoppedPlane.QWeyl

open LaurentPairing LaurentChartComplex ConcreteCech GradedLocalExactness
variable {K : Type*} [Field K]

/-- The actual multiplier from dual coefficient degree `-(r+1)` to `-r`. -/
def profileLaurentTopMultiply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (n : ℕ) :
    topGrade (K := K) (auxiliaryDualWeights s n) (-(r + 1)) →ₗ[K]
      topGrade (K := K) (auxiliaryDualWeights s (n + 1)) (-r) :=
  topMap (auxiliaryDualWeights s n) (auxiliaryDualWeights s (n + 1))
    (-(r + 1)) (-r) (profileLaurentMultiply q hq s n) (by
      intro p hp
      have hd : -(r + 1) + 1 = -r := by omega
      simpa only [hd] using
        profileLaurentMultiply_mem_overlapGrade q hq s n (-(r + 1)) p hp)

@[simp] theorem profileLaurentTopMultiply_val (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (r : ℤ) (n : ℕ)
    (p : topGrade (K := K) (auxiliaryDualWeights s n) (-(r + 1))) :
    (profileLaurentTopMultiply q hq s r n p).val =
      freeNegativePart (profileLaurentMultiply q hq s n p.val) :=
  topMap_val _ _ _ _ _ _ p

/-- The genuine graded `u` chart cross kernel has a graded linear-form preimage. -/
theorem profileLaurentCross_uChart_graded_preimage
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ uChartGrade (auxiliaryDualWeights s (n + 1)) k)
    (hQp : profileLaurentCross q hq s (n + 1) p = 0) :
    ∃ x, x ∈ uChartGrade (auxiliaryDualWeights s n) (k - 1) ∧
      profileLaurentMultiply q hq s n x = p := by
  apply uChart_preimage_by_projection (auxiliaryDualWeights s n)
    (auxiliaryDualWeights s (n + 1)) (profileLaurentMultiply q hq s n)
    (profileLaurentMultiply_mem_overlapGrade q hq s n) k p hp
  apply profileLaurentCross_uChart_preimage q hq s n p _ hQp
  rw [uChartGrade_eq_overlap_inf_range] at hp
  exact hp.2

/-- The same graded local exactness on the genuine `v` chart. -/
theorem profileLaurentCross_vChart_graded_preimage
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ vChartGrade (auxiliaryDualWeights s (n + 1)) k)
    (hQp : profileLaurentCross q hq s (n + 1) p = 0) :
    ∃ x, x ∈ vChartGrade (auxiliaryDualWeights s n) (k - 1) ∧
      profileLaurentMultiply q hq s n x = p := by
  apply vChart_preimage_by_projection (auxiliaryDualWeights s n)
    (auxiliaryDualWeights s (n + 1)) (profileLaurentMultiply q hq s n)
    (profileLaurentMultiply_mem_overlapGrade q hq s n) k p hp
  apply profileLaurentCross_vChart_preimage q hq s n p _ hQp
  rw [vChartGrade_eq_overlap_inf_range] at hp
  exact hp.2

/-- Concrete two-chart duality: the actual polynomial dual derivative kernel
controls injectivity of the actual finite top Laurent multiplier. -/
theorem profileLaurentTopMultiply_injective_of_dualDifferential
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℤ) (n : ℕ)
    (hinj : Function.Injective
      (operatorDifferential (gradedProfileDualOperators q s ((n + 1 : ℕ) - r)) n)) :
    Function.Injective (profileLaurentTopMultiply q hq s r n) := by
  apply topMap_injective_of_cross
    (auxiliaryDualWeights s n) (auxiliaryDualWeights s (n + 1))
    (auxiliaryDualWeights s (n + 1)) (-(r + 1)) (-r) ((n + 1 : ℕ) - r)
    (profileLaurentMultiply q hq s n) (profileLaurentCross q hq s (n + 1))
    (profileLaurentDirectional q hq s n)
  · intro p hp
    have hd : -r + ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) - r := by omega
    simpa only [hd] using profileLaurentCross_mem_uChartGrade q hq s (n + 1) (-r) p hp
  · intro p hp
    have hd : -r + ((n + 1 : ℕ) : ℤ) = ((n + 1 : ℕ) : ℤ) - r := by omega
    simpa only [hd] using profileLaurentCross_mem_vChartGrade q hq s (n + 1) (-r) p hp
  · exact profileLaurentCross_multiply_zero q hq s n
  · exact profileLaurentDirectional_cross_zero q hq s n
  · intro p hp hzero
    exact profileLaurentMultiply_injective q hq s n (hzero.trans (map_zero _).symm)
  · exact profileLaurentDirectional_positive_kernel_zero q hq s ((n + 1 : ℕ) - r) n hinj
  · intro p hp hzero
    obtain ⟨x,hx,hLx⟩ := profileLaurentCross_uChart_graded_preimage q hq s n (-r) p hp hzero
    refine ⟨x, ?_, hLx⟩
    have hd : -r - 1 = -(r + 1) := by omega
    simpa only [hd] using hx
  · intro p hp hzero
    obtain ⟨x,hx,hLx⟩ := profileLaurentCross_vChart_graded_preimage q hq s n (-r) p hp hzero
    refine ⟨x, ?_, hLx⟩
    have hd : -r - 1 = -(r + 1) := by omega
    simpa only [hd] using hx

variable [CharZero K]

/-- At every positive critical auxiliary degree, the actual top Laurent
multiplier is injective, for all three residue profiles. -/
theorem profileLaurentTopMultiply_critical_injective
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (r : ℕ)
    (hn : 0 < profileCriticalDegree s r) :
    Function.Injective (profileLaurentTopMultiply q hq s (r : ℤ)
      (profileCriticalDegree s r - 1)) := by
  apply profileLaurentTopMultiply_injective_of_dualDifferential
  have hd : ((profileCriticalDegree s r - 1 + 1 : ℕ) : ℤ) =
      (profileCriticalDegree s r : ℤ) := by omega
  rw [hd]
  exact profileCriticalDualDifferential_injective q hq s r hn

end ChoppedPlane.QWeyl
