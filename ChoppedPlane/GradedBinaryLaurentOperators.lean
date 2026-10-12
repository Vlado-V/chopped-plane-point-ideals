module

public import ChoppedPlane.GradedBinaryLaurent
public import ChoppedPlane.QWeylLaurentGrading

@[expose] public section

/-! The literal polynomial coefficient embedding commutes with the actual
coordinate and primal/dual cyclic operators. -/

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial LaurentPairing LaurentChartComplex
variable {K : Type*} [Field K]

def binaryLaurentExponent : (Fin 2 →₀ ℕ) →+ (ℤ × ℤ) where
  toFun s := ((s 0 : ℤ), (s 1 : ℤ))
  map_zero' := by simp
  map_add' s t := by simp

theorem binaryLaurentEmbedding_eq_mapDomain :
    binaryLaurentEmbedding (K := K) =
      AddMonoidAlgebra.mapDomainAlgHom K K binaryLaurentExponent := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change binaryLaurentEmbedding (X (0 : Fin 2) : BinaryRing K) = _
    rw [binaryLaurentEmbedding_X_zero (K := K)]
    change U = AddMonoidAlgebra.mapDomain binaryLaurentExponent
      (AddMonoidAlgebra.single (Finsupp.single 0 1) 1)
    simp [binaryLaurentExponent, U]
  · change binaryLaurentEmbedding (X (1 : Fin 2) : BinaryRing K) = _
    rw [binaryLaurentEmbedding_X_one (K := K)]
    change V = AddMonoidAlgebra.mapDomain binaryLaurentExponent
      (AddMonoidAlgebra.single (Finsupp.single 1 1) 1)
    simp [binaryLaurentExponent, V]

@[simp] theorem binaryLaurentEmbedding_monomial (s : Fin 2 →₀ ℕ) (c : K) :
    binaryLaurentEmbedding (monomial s c) =
      AddMonoidAlgebra.single ((s 0 : ℤ), (s 1 : ℤ)) c := by
  rw [binaryLaurentEmbedding_eq_mapDomain]
  change AddMonoidAlgebra.mapDomain binaryLaurentExponent (AddMonoidAlgebra.single s c) = _
  simp [binaryLaurentExponent]

/-- Componentwise actual polynomial evaluation, written in Laurent coefficients. -/
def vectorLaurentEmbedding : BinaryVector K →ₗ[K] FreeLaurent K (Fin 3) :=
  (freeLaurentEquiv (K := K) (ι := Fin 3)).symm.toLinearMap.comp
    (LinearMap.pi fun i => binaryLaurentEmbedding.toLinearMap.comp (LinearMap.proj i))

@[simp] theorem freeLaurentEquiv_vectorLaurentEmbedding (m : BinaryVector K)
    (i : Fin 3) :
    freeLaurentEquiv (vectorLaurentEmbedding m) i = binaryLaurentEmbedding (m i) := by
  simp [vectorLaurentEmbedding]

@[simp] theorem binaryVectorCoefficients_single (i : Fin 3) (s : Fin 2 →₀ ℕ) (c : K) :
    binaryVectorCoefficients (Pi.single i (monomial s c)) = Finsupp.single (i, s) c := by
  classical
  ext ⟨j,t⟩
  by_cases hj : j = i
  · subst j
    simp [binaryVectorCoefficients_apply, coeff_monomial, Finsupp.single_apply]
  · simp [binaryVectorCoefficients_apply, hj]

@[simp] theorem binaryVectorCoefficients_symm_single
    (i : Fin 3) (s : Fin 2 →₀ ℕ) (c : K) :
    binaryVectorCoefficients.symm (Finsupp.single (i, s) c) = Pi.single i (monomial s c) := by
  apply binaryVectorCoefficients.injective
  simp

/-- Literal coefficient flattening is exactly the componentwise ring embedding. -/
theorem binaryVectorLaurent_eq_vectorLaurentEmbedding :
    binaryVectorLaurent (K := K) = vectorLaurentEmbedding := by
  have h : (binaryVectorLaurent (K := K)).comp binaryVectorCoefficients.symm.toLinearMap =
      vectorLaurentEmbedding.comp binaryVectorCoefficients.symm.toLinearMap := by
    apply Finsupp.lhom_ext
    rintro ⟨i,s⟩ c
    simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      binaryVectorCoefficients_symm_single]
    apply freeLaurentEquiv.injective
    funext j
    ext e
    by_cases hj : j = i
    · subst j
      simp [binaryVectorLaurent, binaryVectorExponent,
        freeLaurentEquiv_coeff, Finsupp.single_apply]
    · simp [binaryVectorLaurent, binaryVectorExponent,
        freeLaurentEquiv_coeff, hj]
  apply LinearMap.ext
  intro m
  have hm := LinearMap.congr_fun h (binaryVectorCoefficients m)
  simpa using hm

@[simp] theorem freeLaurentEquiv_binaryVectorLaurent (m : BinaryVector K) (i : Fin 3) :
    freeLaurentEquiv (binaryVectorLaurent m) i = binaryLaurentEmbedding (m i) := by
  rw [binaryVectorLaurent_eq_vectorLaurentEmbedding]
  exact freeLaurentEquiv_vectorLaurentEmbedding m i

theorem binaryVectorLaurent_scalar (f : BinaryRing K) (m : BinaryVector K) :
    binaryVectorLaurent (f • m) = laurentScalar (binaryLaurentEmbedding f) (binaryVectorLaurent m) := by
  apply freeLaurentEquiv.injective
  funext i
  simp [Pi.smul_apply, smul_eq_mul]

theorem binaryVectorLaurent_cyclicZDual (q : K) (s : CubicProfile) (m : BinaryVector K) :
    binaryVectorLaurent (cyclicZDual (profileFactors q s) m) =
      laurentCyclicZDual q s (binaryVectorLaurent m) := by
  apply freeLaurentEquiv.injective
  funext i
  fin_cases i <;> simp [cyclicZDual]

/-- The source permutation of the forward cyclic action. -/
def cyclicPrimalSource : Fin 3 → Fin 3 := ![2, 0, 1]

/-- The actual forward cyclic Laurent action, on the original generator shifts. -/
def laurentCyclicZ (q : K) (s : CubicProfile) :
    FreeLaurent K (Fin 3) →ₗ[K] FreeLaurent K (Fin 3) :=
  laurentOperator
    (fun i => binaryLaurentEmbedding (profileFactors q s (cyclicPrimalSource i)))
    cyclicPrimalSource

@[simp] theorem freeLaurentEquiv_laurentCyclicZ (q : K) (s : CubicProfile)
    (p : FreeLaurent K (Fin 3)) :
    freeLaurentEquiv (laurentCyclicZ q s p) =
      cyclicZ (fun j => binaryLaurentEmbedding (profileFactors q s j))
        (freeLaurentEquiv p) := by
  funext i
  fin_cases i <;> simp [laurentCyclicZ, cyclicPrimalSource, cyclicZ]

theorem binaryVectorLaurent_cyclicZ (q : K) (s : CubicProfile) (m : BinaryVector K) :
    binaryVectorLaurent (cyclicZ (profileFactors q s) m) =
      laurentCyclicZ q s (binaryVectorLaurent m) := by
  apply freeLaurentEquiv.injective
  funext i
  fin_cases i <;> simp [cyclicZ]

theorem cyclicPrimalLaurent_degree (s : CubicProfile) (i : Fin 3) :
    (profileFactorDegrees s (cyclicPrimalSource i) : ℤ) + (generatorWeights s i : ℤ) =
      1 + (generatorWeights s (cyclicPrimalSource i) : ℤ) := by
  cases s <;> fin_cases i <;>
    norm_num [generatorWeights, cyclicPrimalSource, profileFactorDegrees]

theorem laurentCyclicZ_mem_overlapGrade (q : K) (s : CubicProfile)
    (k : ℤ) (p : FreeLaurent K (Fin 3))
    (hp : p ∈ overlapGrade (fun i => (generatorWeights s i : ℤ)) k) :
    laurentCyclicZ q s p ∈
      overlapGrade (fun i => (generatorWeights s i : ℤ)) (k + 1) :=
  laurentOperator_mem_overlapGrade _ _ _ _ 1
    (fun i => (profileFactorDegrees s (cyclicPrimalSource i) : ℤ))
    (fun i => profileFactors_laurent_mem q s (cyclicPrimalSource i))
    (cyclicPrimalLaurent_degree s) k p hp

theorem gradedBinaryLaurentEquiv_coordinate (j : Fin 2) (w : Fin 3 → ℕ)
    (t : ℤ) (m : GradedBinaryVector (K := K) w t) :
    (gradedBinaryLaurentEquiv w (t + 1) (gradedBinaryCoordinate j w t m)).val =
      laurentScalar (binaryLaurentEmbedding (X j : BinaryRing K))
        (gradedBinaryLaurentEquiv w t m).val := by
  simp only [gradedBinaryLaurentEquiv_apply, gradedBinaryCoordinate_val,
    binaryVectorLaurent_scalar]

theorem gradedBinaryLaurentEquiv_Z (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (generatorWeights s) t) :
    (gradedBinaryLaurentEquiv (generatorWeights s) (t + 1) (gradedProfileZ q s t m)).val =
      laurentCyclicZ q s (gradedBinaryLaurentEquiv (generatorWeights s) t m).val := by
  simp only [gradedBinaryLaurentEquiv_apply, gradedProfileZ_val, binaryVectorLaurent_cyclicZ]

theorem gradedBinaryLaurentEquiv_ZDual (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t) :
    (gradedBinaryLaurentEquiv (dualGeneratorWeights s) (t + 1)
      (gradedProfileZDual q s t m)).val =
      laurentCyclicZDual q s
        (gradedBinaryLaurentEquiv (dualGeneratorWeights s) t m).val := by
  simp only [gradedBinaryLaurentEquiv_apply, gradedProfileZDual_val,
    binaryVectorLaurent_cyclicZDual]

end ChoppedPlane.QWeyl
