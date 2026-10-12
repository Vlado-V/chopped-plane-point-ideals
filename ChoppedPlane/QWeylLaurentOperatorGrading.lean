module

public import ChoppedPlane.QWeylLaurentOperators

@[expose] public section

/-! Coefficient-degree closure of the actual Laurent cross, multiplication
and directional operators.  The weights are the literal dual generator
weights and the three actions are the actual coordinates and cyclic root. -/

noncomputable section
namespace ChoppedPlane.QWeyl

open LaurentPairing LaurentChartComplex FiniteCech SymmetricDerivative

variable {K : Type*} [Field K]

@[simp] theorem chartLaurentU_smul (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : Fin 3 → BinaryLaurent K) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    chartU (binaryChartLaurentMap (K := K)) • m = fun i => U * m i := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  change cyclicCoefficientHom ((binaryChartLaurentMap (K := K)) (binaryCubic K))
    ((binaryChartLaurentMap (K := K)) (binaryU K)) • m = _
  rw [cyclicModule_coefficient_smul]
  funext i
  simp

@[simp] theorem chartLaurentV_smul (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : Fin 3 → BinaryLaurent K) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    chartV (binaryChartLaurentMap (K := K)) • m = fun i => V * m i := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  change cyclicCoefficientHom ((binaryChartLaurentMap (K := K)) (binaryCubic K))
    ((binaryChartLaurentMap (K := K)) (binaryV K)) • m = _
  rw [cyclicModule_coefficient_smul]
  funext i
  simp

@[simp] theorem chartLaurentZ_smul (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : Fin 3 → BinaryLaurent K) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    chartZ (binaryChartLaurentMap (K := K)) • m =
      cyclicZDual (fun i => binaryLaurentEmbedding (profileFactors q s i)) m := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  exact cyclicModule_root_smul ((binaryChartLaurentMap (K := K)) (binaryCubic K))
    (chartDualZ (binaryChartLaurentMap (K := K)) q s)
    (chartDualZ_cube (binaryChartLaurentMap (K := K)) q hq s) m

private theorem chartLaurentLinearForm_degree_one
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (G : ℤ → Submodule K (Fin 3 → BinaryLaurent K))
    (hU : ∀ k m, m ∈ G k → (fun i => U * m i) ∈ G (k + 1))
    (hV : ∀ k m, m ∈ G k → (fun i => V * m i) ∈ G (k + 1))
    (hZ : ∀ k m, m ∈ G k →
      cyclicZDual (fun i => binaryLaurentEmbedding (profileFactors q s i)) m ∈ G (k + 1)) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    ∀ k i m, m ∈ G k → chartLinearForm (binaryChartLaurentMap (K := K)) i • m ∈ G (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  intro k i m hm
  fin_cases i
  · simpa [chartLinearForm] using hU k m hm
  · simpa [chartLinearForm] using hV k m hm
  · simpa [chartLinearForm] using hZ k m hm

theorem chartLaurentLinearForm_degree_one_overlap
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    ∀ (k : ℤ) (i : Fin 3) (m : Fin 3 → BinaryLaurent K), m ∈ vectorOverlapGrade (fun j => (dualGeneratorWeights s j : ℤ)) k →
      chartLinearForm (binaryChartLaurentMap (K := K)) i • m ∈
        vectorOverlapGrade (fun j => (dualGeneratorWeights s j : ℤ)) (k + 1) := by
  exact chartLaurentLinearForm_degree_one q hq s
    (vectorOverlapGrade (fun j => (dualGeneratorWeights s j : ℤ)))
    (fun k m hm => scalar_mem_vectorOverlapGrade U 1 U_mem_polynomialLaurentGrade _ k m hm)
    (fun k m hm => scalar_mem_vectorOverlapGrade V 1 V_mem_polynomialLaurentGrade _ k m hm)
    (fun k m hm => cyclicZDual_mem_vectorOverlapGrade q s k m hm)

theorem chartLaurentLinearForm_degree_one_uChart
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    ∀ (k : ℤ) (i : Fin 3) (m : Fin 3 → BinaryLaurent K), m ∈ vectorUChartGrade (fun j => (dualGeneratorWeights s j : ℤ)) k →
      chartLinearForm (binaryChartLaurentMap (K := K)) i • m ∈
        vectorUChartGrade (fun j => (dualGeneratorWeights s j : ℤ)) (k + 1) := by
  exact chartLaurentLinearForm_degree_one q hq s
    (vectorUChartGrade (fun j => (dualGeneratorWeights s j : ℤ)))
    (fun k m hm => scalar_mem_vectorUChartGrade U 1 U_mem_polynomialLaurentGrade _ k m hm)
    (fun k m hm => scalar_mem_vectorUChartGrade V 1 V_mem_polynomialLaurentGrade _ k m hm)
    (fun k m hm => cyclicZDual_mem_vectorUChartGrade q s k m hm)

theorem chartLaurentLinearForm_degree_one_vChart
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
    ∀ (k : ℤ) (i : Fin 3) (m : Fin 3 → BinaryLaurent K), m ∈ vectorVChartGrade (fun j => (dualGeneratorWeights s j : ℤ)) k →
      chartLinearForm (binaryChartLaurentMap (K := K)) i • m ∈
        vectorVChartGrade (fun j => (dualGeneratorWeights s j : ℤ)) (k + 1) := by
  exact chartLaurentLinearForm_degree_one q hq s
    (vectorVChartGrade (fun j => (dualGeneratorWeights s j : ℤ)))
    (fun k m hm => scalar_mem_vectorVChartGrade U 1 U_mem_polynomialLaurentGrade _ k m hm)
    (fun k m hm => scalar_mem_vectorVChartGrade V 1 V_mem_polynomialLaurentGrade _ k m hm)
    (fun k m hm => cyclicZDual_mem_vectorVChartGrade q s k m hm)

theorem profileLaurentCross_mem_overlapGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n))
    (hp : p ∈ overlapGrade (auxiliaryDualWeights s n) k) :
    profileLaurentCross q hq s n p ∈ overlapGrade (auxiliaryDualWeights s n) (k + n) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_overlap_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + n) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentCross]
  exact finiteCross_crossMatrix_mem_coefficientGrade
    (fun j => (vectorOverlapGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartU (binaryChartLaurentMap (K := K))) (chartV (binaryChartLaurentMap (K := K))) (chartZ (binaryChartLaurentMap (K := K)))
    (chartLaurentLinearForm_degree_one_overlap q hq s) k n _
    ((auxiliaryLaurentVectorEquiv_overlap_iff _ k p).mp hp)

theorem profileLaurentCross_mem_uChartGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n))
    (hp : p ∈ uChartGrade (auxiliaryDualWeights s n) k) :
    profileLaurentCross q hq s n p ∈ uChartGrade (auxiliaryDualWeights s n) (k + n) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_uChart_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + n) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentCross]
  exact finiteCross_crossMatrix_mem_coefficientGrade
    (fun j => (vectorUChartGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartU (binaryChartLaurentMap (K := K))) (chartV (binaryChartLaurentMap (K := K))) (chartZ (binaryChartLaurentMap (K := K)))
    (chartLaurentLinearForm_degree_one_uChart q hq s) k n _
    ((auxiliaryLaurentVectorEquiv_uChart_iff _ k p).mp hp)

theorem profileLaurentCross_mem_vChartGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n))
    (hp : p ∈ vChartGrade (auxiliaryDualWeights s n) k) :
    profileLaurentCross q hq s n p ∈ vChartGrade (auxiliaryDualWeights s n) (k + n) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_vChart_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + n) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentCross]
  exact finiteCross_crossMatrix_mem_coefficientGrade
    (fun j => (vectorVChartGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartU (binaryChartLaurentMap (K := K))) (chartV (binaryChartLaurentMap (K := K))) (chartZ (binaryChartLaurentMap (K := K)))
    (chartLaurentLinearForm_degree_one_vChart q hq s) k n _
    ((auxiliaryLaurentVectorEquiv_vChart_iff _ k p).mp hp)

theorem profileLaurentMultiply_mem_overlapGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n))
    (hp : p ∈ overlapGrade (auxiliaryDualWeights s n) k) :
    profileLaurentMultiply q hq s n p ∈
      overlapGrade (auxiliaryDualWeights s (n + 1)) (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_overlap_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + 1) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentMultiply]
  exact finiteMultiply_mem_coefficientGrade
    (fun j => (vectorOverlapGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartLinearForm (binaryChartLaurentMap (K := K))) (chartLaurentLinearForm_degree_one_overlap q hq s)
    k n _ ((auxiliaryLaurentVectorEquiv_overlap_iff _ k p).mp hp)

theorem profileLaurentMultiply_mem_uChartGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n))
    (hp : p ∈ uChartGrade (auxiliaryDualWeights s n) k) :
    profileLaurentMultiply q hq s n p ∈
      uChartGrade (auxiliaryDualWeights s (n + 1)) (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_uChart_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + 1) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentMultiply]
  exact finiteMultiply_mem_coefficientGrade
    (fun j => (vectorUChartGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartLinearForm (binaryChartLaurentMap (K := K))) (chartLaurentLinearForm_degree_one_uChart q hq s)
    k n _ ((auxiliaryLaurentVectorEquiv_uChart_iff _ k p).mp hp)

theorem profileLaurentMultiply_mem_vChartGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n))
    (hp : p ∈ vChartGrade (auxiliaryDualWeights s n) k) :
    profileLaurentMultiply q hq s n p ∈
      vChartGrade (auxiliaryDualWeights s (n + 1)) (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_vChart_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + 1) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentMultiply]
  exact finiteMultiply_mem_coefficientGrade
    (fun j => (vectorVChartGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartLinearForm (binaryChartLaurentMap (K := K))) (chartLaurentLinearForm_degree_one_vChart q hq s)
    k n _ ((auxiliaryLaurentVectorEquiv_vChart_iff _ k p).mp hp)

theorem profileLaurentDirectional_mem_overlapGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ overlapGrade (auxiliaryDualWeights s (n + 1)) k) :
    profileLaurentDirectional q hq s n p ∈
      overlapGrade (auxiliaryDualWeights s n) (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_overlap_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + 1) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentDirectional]
  exact finiteDirectional_mem_coefficientGrade
    (fun j => (vectorOverlapGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartLinearForm (binaryChartLaurentMap (K := K))) (chartLaurentLinearForm_degree_one_overlap q hq s)
    k n _ ((auxiliaryLaurentVectorEquiv_overlap_iff _ k p).mp hp)

theorem profileLaurentDirectional_mem_uChartGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ uChartGrade (auxiliaryDualWeights s (n + 1)) k) :
    profileLaurentDirectional q hq s n p ∈
      uChartGrade (auxiliaryDualWeights s n) (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_uChart_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + 1) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentDirectional]
  exact finiteDirectional_mem_coefficientGrade
    (fun j => (vectorUChartGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartLinearForm (binaryChartLaurentMap (K := K))) (chartLaurentLinearForm_degree_one_uChart q hq s)
    k n _ ((auxiliaryLaurentVectorEquiv_uChart_iff _ k p).mp hp)

theorem profileLaurentDirectional_mem_vChartGrade
    (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) (k : ℤ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ vChartGrade (auxiliaryDualWeights s (n + 1)) k) :
    profileLaurentDirectional q hq s n p ∈
      vChartGrade (auxiliaryDualWeights s n) (k + 1) := by
  let := chartDualModuleStructure (binaryChartLaurentMap (K := K)) q hq s
  apply (auxiliaryLaurentVectorEquiv_vChart_iff
    (fun i => (dualGeneratorWeights s i : ℤ)) (k + 1) _).mpr
  simp only [auxiliaryLaurentVectorEquiv_profileLaurentDirectional]
  exact finiteDirectional_mem_coefficientGrade
    (fun j => (vectorVChartGrade (fun i => (dualGeneratorWeights s i : ℤ)) j).toAddSubgroup)
    (chartLinearForm (binaryChartLaurentMap (K := K))) (chartLaurentLinearForm_degree_one_vChart q hq s)
    k n _ ((auxiliaryLaurentVectorEquiv_vChart_iff _ k p).mp hp)

end ChoppedPlane.QWeyl
