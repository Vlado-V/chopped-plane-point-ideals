module

public import ChoppedPlane.QWeylChartFiniteMaps
public import ChoppedPlane.QWeylLaurentGrading

@[expose] public section

/-!
# Finite operators on the actual binary charts and overlap

The generic cyclic chart operators specialize to the literal `u` chart,
`v` chart, and binary Laurent overlap. The chart embeddings are injective
coefficient maps and commute with cross multiplication and differentiation.
-/

noncomputable section
namespace ChoppedPlane.QWeyl

open BinaryChartRings LaurentPairing

variable {K : Type*} [Field K]

theorem binaryChartLaurentMap_eq_binaryLaurentEmbedding :
    binaryChartLaurentMap (K := K) = binaryLaurentEmbedding := rfl

abbrev UChartFiniteVector (K : Type*) [Field K] (n : ℕ) :=
  ChartFiniteVector (URing K) n

abbrev VChartFiniteVector (K : Type*) [Field K] (n : ℕ) :=
  ChartFiniteVector (VRing K) n

abbrev OverlapFiniteVector (K : Type*) [Field K] (n : ℕ) :=
  ChartFiniteVector (BinaryLaurent K) n

abbrev uFiniteCross (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteCross (binaryUChart (K := K)) q hq s n

abbrev vFiniteCross (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteCross (binaryVChart (K := K)) q hq s n

abbrev overlapFiniteCross (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteCross (binaryChartLaurentMap (K := K)) q hq s n

abbrev uFiniteMultiply (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteMultiply (binaryUChart (K := K)) q hq s n

abbrev vFiniteMultiply (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) (n : ℕ) :=
  chartFiniteMultiply (binaryVChart (K := K)) q hq s n

abbrev overlapFiniteMultiply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteMultiply (binaryChartLaurentMap (K := K)) q hq s n

abbrev uFiniteDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteDirectional (binaryUChart (K := K)) q hq s n

abbrev vFiniteDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteDirectional (binaryVChart (K := K)) q hq s n

abbrev overlapFiniteDirectional (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :=
  chartFiniteDirectional (binaryChartLaurentMap (K := K)) q hq s n

/-- Embed finite auxiliary coefficient vectors from the actual `u` chart. -/
abbrev uFiniteEmbedding (n : ℕ) :=
  chartFiniteBaseChange (uEmbedding (K := K)) n

/-- Embed finite auxiliary coefficient vectors from the actual `v` chart. -/
abbrev vFiniteEmbedding (n : ℕ) :=
  chartFiniteBaseChange (vEmbedding (K := K)) n

@[simp] theorem uFiniteEmbedding_apply (n : ℕ) (c : UChartFiniteVector K n)
    (i : Sym (Fin 3) n) (j : Fin 3) :
    uFiniteEmbedding n c i j = uEmbedding (c i j) := rfl

@[simp] theorem vFiniteEmbedding_apply (n : ℕ) (c : VChartFiniteVector K n)
    (i : Sym (Fin 3) n) (j : Fin 3) :
    vFiniteEmbedding n c i j = vEmbedding (c i j) := rfl

theorem uFiniteEmbedding_injective (n : ℕ) :
    Function.Injective (uFiniteEmbedding (K := K) n) := by
  intro c d h
  funext i j
  apply uEmbedding_injective
  exact congrFun (congrFun h i) j

theorem vFiniteEmbedding_injective (n : ℕ) :
    Function.Injective (vFiniteEmbedding (K := K) n) := by
  intro c d h
  funext i j
  apply vEmbedding_injective
  exact congrFun (congrFun h i) j

theorem uFiniteCross_kernel (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K (n + 1)) :
    uFiniteCross q hq s (n + 1) c = 0 ↔
      c ∈ LinearMap.range (uFiniteMultiply q hq s n) :=
  chartFiniteCross_kernel_u binaryUChart q hq s uUInv (by simp) n c

theorem vFiniteCross_kernel (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K (n + 1)) :
    vFiniteCross q hq s (n + 1) c = 0 ↔
      c ∈ LinearMap.range (vFiniteMultiply q hq s n) :=
  chartFiniteCross_kernel_v binaryVChart q hq s vVInv (by simp) n c

theorem uFiniteMultiply_injective (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :
    Function.Injective (uFiniteMultiply q hq s n) :=
  chartFiniteMultiply_injective_u binaryUChart q hq s uUInv (by simp) n

theorem vFiniteMultiply_injective (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :
    Function.Injective (vFiniteMultiply q hq s n) :=
  chartFiniteMultiply_injective_v binaryVChart q hq s vVInv (by simp) n

/-- The actual Laurent `u` unit is the image of the inverse in the `u` chart. -/
theorem binaryChartLaurentMap_U_mul_inv :
    binaryChartLaurentMap (binaryU K) * uEmbedding (uUInv (K := K)) = 1 := by
  simpa only [map_mul, map_one, uEmbedding_u, binaryChartLaurentMap_binaryU] using
    congrArg (uEmbedding (K := K)) (uU_mul_inv (K := K))

theorem overlapFiniteMultiply_injective (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) :
    Function.Injective (overlapFiniteMultiply q hq s n) :=
  chartFiniteMultiply_injective_u binaryChartLaurentMap q hq s
    (uEmbedding uUInv) binaryChartLaurentMap_U_mul_inv n

theorem overlapFiniteCross_kernel (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : OverlapFiniteVector K (n + 1)) :
    overlapFiniteCross q hq s (n + 1) c = 0 ↔
      c ∈ LinearMap.range (overlapFiniteMultiply q hq s n) :=
  chartFiniteCross_kernel_u binaryChartLaurentMap q hq s
    (uEmbedding uUInv) binaryChartLaurentMap_U_mul_inv n c

theorem uFiniteCross_multiply_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K n) :
    uFiniteCross q hq s (n + 1) (uFiniteMultiply q hq s n c) = 0 :=
  (uFiniteCross_kernel q hq s n _).mpr ⟨c, rfl⟩

theorem vFiniteCross_multiply_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K n) :
    vFiniteCross q hq s (n + 1) (vFiniteMultiply q hq s n c) = 0 :=
  (vFiniteCross_kernel q hq s n _).mpr ⟨c, rfl⟩

theorem overlapFiniteCross_multiply_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : OverlapFiniteVector K n) :
    overlapFiniteCross q hq s (n + 1) (overlapFiniteMultiply q hq s n c) = 0 :=
  (overlapFiniteCross_kernel q hq s n _).mpr ⟨c, rfl⟩

theorem uFiniteDirectional_cross_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K (n + 1)) :
    uFiniteDirectional q hq s n (uFiniteCross q hq s (n + 1) c) = 0 :=
  chartFiniteDirectional_cross_zero binaryUChart q hq s n c

theorem vFiniteDirectional_cross_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K (n + 1)) :
    vFiniteDirectional q hq s n (vFiniteCross q hq s (n + 1) c) = 0 :=
  chartFiniteDirectional_cross_zero binaryVChart q hq s n c

theorem overlapFiniteDirectional_cross_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : OverlapFiniteVector K (n + 1)) :
    overlapFiniteDirectional q hq s n (overlapFiniteCross q hq s (n + 1) c) = 0 :=
  chartFiniteDirectional_cross_zero binaryChartLaurentMap q hq s n c

section CharacteristicZero

variable [CharZero K]

theorem uFiniteDirectional_kernel (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K (n + 1)) :
    uFiniteDirectional q hq s n c = 0 ↔
      c ∈ LinearMap.range (uFiniteCross q hq s (n + 1)) :=
  chartFiniteDirectional_kernel_u binaryUChart q hq s uUInv (by simp) n c

theorem vFiniteDirectional_kernel (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K (n + 1)) :
    vFiniteDirectional q hq s n c = 0 ↔
      c ∈ LinearMap.range (vFiniteCross q hq s (n + 1)) :=
  chartFiniteDirectional_kernel_v binaryVChart q hq s vVInv (by simp) n c

theorem overlapFiniteDirectional_kernel (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : OverlapFiniteVector K (n + 1)) :
    overlapFiniteDirectional q hq s n c = 0 ↔
      c ∈ LinearMap.range (overlapFiniteCross q hq s (n + 1)) :=
  chartFiniteDirectional_kernel_u binaryChartLaurentMap q hq s
    (uEmbedding uUInv) binaryChartLaurentMap_U_mul_inv n c

end CharacteristicZero

/-- The actual `u` chart embedding commutes with the finite cross operator. -/
theorem uFiniteCross_embedding (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K n) :
    uFiniteEmbedding n (uFiniteCross q hq s n c) =
      overlapFiniteCross q hq s n (uFiniteEmbedding n c) := by
  simpa only [uEmbedding_comp_binaryUChart] using
    chartFiniteCross_baseChange binaryUChart uEmbedding q hq s n c

/-- The actual `v` chart embedding commutes with the finite cross operator. -/
theorem vFiniteCross_embedding (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K n) :
    vFiniteEmbedding n (vFiniteCross q hq s n c) =
      overlapFiniteCross q hq s n (vFiniteEmbedding n c) := by
  simpa only [vEmbedding_comp_binaryVChart] using
    chartFiniteCross_baseChange binaryVChart vEmbedding q hq s n c

theorem uFiniteMultiply_embedding (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K n) :
    uFiniteEmbedding (n + 1) (uFiniteMultiply q hq s n c) =
      overlapFiniteMultiply q hq s n (uFiniteEmbedding n c) := by
  simpa only [uEmbedding_comp_binaryUChart] using
    chartFiniteMultiply_baseChange binaryUChart uEmbedding q hq s n c

theorem vFiniteMultiply_embedding (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K n) :
    vFiniteEmbedding (n + 1) (vFiniteMultiply q hq s n c) =
      overlapFiniteMultiply q hq s n (vFiniteEmbedding n c) := by
  simpa only [vEmbedding_comp_binaryVChart] using
    chartFiniteMultiply_baseChange binaryVChart vEmbedding q hq s n c

theorem uFiniteDirectional_embedding (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : UChartFiniteVector K (n + 1)) :
    uFiniteEmbedding n (uFiniteDirectional q hq s n c) =
      overlapFiniteDirectional q hq s n (uFiniteEmbedding (n + 1) c) := by
  simpa only [uEmbedding_comp_binaryUChart] using
    chartFiniteDirectional_baseChange binaryUChart uEmbedding q hq s n c

theorem vFiniteDirectional_embedding (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) (c : VChartFiniteVector K (n + 1)) :
    vFiniteEmbedding n (vFiniteDirectional q hq s n c) =
      overlapFiniteDirectional q hq s n (vFiniteEmbedding (n + 1) c) := by
  simpa only [vEmbedding_comp_binaryVChart] using
    chartFiniteDirectional_baseChange binaryVChart vEmbedding q hq s n c

end ChoppedPlane.QWeyl
