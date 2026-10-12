module

public import ChoppedPlane.QWeylGrading
public import ChoppedPlane.LinearMatrix

@[expose] public section

/-! Exact coefficient degrees at the two critical twists of the cubic
excess-three witnesses. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open Module
variable {K : Type*} [Field K]

/-- The dimension of the degree-r piece of a profile. -/
def profileRows (s : CubicProfile) (r : ℕ) : ℕ := 3*r+3-profileIndex s

/-- The auxiliary degree of the differential dual to the lower critical
matrix twist. -/
def profileCriticalDegree (s : CubicProfile) (r : ℕ) : ℕ := 2*profileRows s r/3

theorem profileRows_pos (s : CubicProfile) (r : ℕ) : 0 < profileRows s r := by
  cases s <;> simp only [profileRows, profileIndex] <;> omega

theorem profileRows_succ (s : CubicProfile) (r : ℕ) :
    profileRows s (r+1) = profileRows s r+3 := by
  cases s <;> simp only [profileRows, profileIndex] <;> omega

theorem finrank_gradedProfile_eq_rows (s : CubicProfile) (r : ℕ) :
    finrank K (GradedBinaryVector (K := K) (generatorWeights s) (r : ℤ)) =
      profileRows s r := finrank_gradedProfile_nat s r

/-- All positive row counts are represented, including the two small cases. -/
theorem exists_profileRows (a : ℕ) (ha : 0 < a) :
    ∃ s : CubicProfile, ∃ r : ℕ, profileRows s r = a := by
  by_cases h0 : a%3 = 0
  · refine ⟨.degreeThree, a/3-1, ?_⟩
    simp only [profileRows, profileIndex]
    omega
  · by_cases h1 : a%3 = 1
    · refine ⟨.degreeOne, a/3, ?_⟩
      simp only [profileRows, profileIndex]
      omega
    · refine ⟨.degreeTwo, a/3, ?_⟩
      simp only [profileRows, profileIndex]
      omega

/-- The original quartic pullback lies strictly below every symmetric-kernel
generator at the upper critical differential degree. -/
theorem profile_right_degree_bound (s : CubicProfile) (r : ℕ) (i : Fin 3) :
    4*(r : ℤ)+(3-(profileIndex s : ℤ)) <
      2*((profileCriticalDegree s r : ℤ)+1)+(generatorWeights s i : ℤ) := by
  cases s <;> fin_cases i <;>
    norm_num [profileCriticalDegree, profileRows, profileIndex, generatorWeights] <;> omega

/-- The lower critical transpose uses the actual dual module in total degree
n-r. Its quartic pullback is below every degree-2n kernel generator. -/
theorem profile_left_dual_degree_bound (s : CubicProfile) (r : ℕ) (i : Fin 3) :
    4*((profileCriticalDegree s r : ℤ)-(r : ℤ))-(3-(profileIndex s : ℤ)) <
      2*(profileCriticalDegree s r : ℤ)+(dualGeneratorWeights s i : ℤ) := by
  cases s <;> fin_cases i <;>
    norm_num [profileCriticalDegree, profileRows, profileIndex, dualGeneratorWeights, generatorWeights] <;> omega

/-- The divisible-by-three case is square at the lower critical twist and
can use the original module's injectivity directly. -/
theorem profile_square_degree_bound (r : ℕ) (i : Fin 3) :
    4*(r : ℤ)+3 < 2*(profileCriticalDegree .degreeThree r : ℤ)+
      (generatorWeights .degreeThree i : ℤ) := by
  fin_cases i <;>
    norm_num [profileCriticalDegree, profileRows, profileIndex, generatorWeights] <;> omega

end ChoppedPlane.QWeyl
