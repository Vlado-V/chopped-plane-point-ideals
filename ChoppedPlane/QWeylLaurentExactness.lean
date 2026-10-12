module

public import ChoppedPlane.QWeylLaurentOperators
public import ChoppedPlane.QWeylActualChartMaps
public import ChoppedPlane.GradedLocalExactness

@[expose] public section

/-! Local exactness and operator identities on the actual flattened Laurent modules. -/

noncomputable section
namespace ChoppedPlane.QWeyl

open LaurentPairing LaurentChartComplex FiniteCech SymmetricDerivative BinaryChartRings
variable {K : Type*} [Field K]

@[simp] theorem auxiliaryLaurentVectorEquiv_uFreeEmbedding (n : ℕ)
    (c : Fin 3 × Sym (Fin 3) n → URing K) :
    auxiliaryLaurentVectorEquiv (uFreeEmbedding c) =
      uFiniteEmbedding n (fun j i => c (i,j)) := by
  funext j i
  change freeLaurentEquiv (uFreeEmbedding c) (i,j) = _
  rw [freeLaurentEquiv_uFreeEmbedding]
  rfl

@[simp] theorem auxiliaryLaurentVectorEquiv_vFreeEmbedding (n : ℕ)
    (c : Fin 3 × Sym (Fin 3) n → VRing K) :
    auxiliaryLaurentVectorEquiv (vFreeEmbedding c) =
      vFiniteEmbedding n (fun j i => c (i,j)) := by
  funext j i
  change freeLaurentEquiv (vFreeEmbedding c) (i,j) = _
  rw [freeLaurentEquiv_vFreeEmbedding]
  rfl

/-- The actual flattened linear-form operator is injective on the overlap. -/
theorem profileLaurentMultiply_injective (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ) : Function.Injective (profileLaurentMultiply q hq s n) := by
  intro p q' hpq
  apply auxiliaryLaurentVectorEquiv.injective
  apply overlapFiniteMultiply_injective q hq s n
  have h := congrArg auxiliaryLaurentVectorEquiv hpq
  simpa only [auxiliaryLaurentVectorEquiv_profileLaurentMultiply] using h

/-- The flattened actual cross substitution kills actual linear-form multiples. -/
theorem profileLaurentCross_multiply_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) n)) :
    profileLaurentCross q hq s (n + 1) (profileLaurentMultiply q hq s n p) = 0 := by
  apply auxiliaryLaurentVectorEquiv.injective
  rw [auxiliaryLaurentVectorEquiv_profileLaurentCross,
    auxiliaryLaurentVectorEquiv_profileLaurentMultiply, map_zero]
  exact overlapFiniteCross_multiply_zero q hq s n _

/-- The actual directional derivative kills the flattened actual cross image. -/
theorem profileLaurentDirectional_cross_zero (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1))) :
    profileLaurentDirectional q hq s n (profileLaurentCross q hq s (n + 1) p) = 0 := by
  apply auxiliaryLaurentVectorEquiv.injective
  rw [auxiliaryLaurentVectorEquiv_profileLaurentDirectional,
    auxiliaryLaurentVectorEquiv_profileLaurentCross, map_zero]
  exact overlapFiniteDirectional_cross_zero q hq s n _

/-- Ungraded `u`-chart kernel elements have actual chart linear-form preimages. -/
theorem profileLaurentCross_uChart_preimage (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ LinearMap.range (uFreeEmbedding (K := K)))
    (hQp : profileLaurentCross q hq s (n + 1) p = 0) :
    ∃ x : FreeLaurent K (Fin 3 × Sym (Fin 3) n),
      x ∈ LinearMap.range (uFreeEmbedding (K := K)) ∧ profileLaurentMultiply q hq s n x = p := by
  obtain ⟨c,rfl⟩ := hp
  have hz : uFiniteCross q hq s (n + 1) (fun j i => c (i,j)) = 0 := by
    apply uFiniteEmbedding_injective (n + 1)
    rw [map_zero, uFiniteCross_embedding]
    have h := congrArg auxiliaryLaurentVectorEquiv hQp
    simpa only [auxiliaryLaurentVectorEquiv_profileLaurentCross,
      auxiliaryLaurentVectorEquiv_uFreeEmbedding, map_zero] using h
  obtain ⟨d,hd⟩ := (uFiniteCross_kernel q hq s n _).mp hz
  refine ⟨uFreeEmbedding (fun ij => d ij.2 ij.1), ⟨_,rfl⟩, ?_⟩
  apply auxiliaryLaurentVectorEquiv.injective
  rw [auxiliaryLaurentVectorEquiv_profileLaurentMultiply,
    auxiliaryLaurentVectorEquiv_uFreeEmbedding, auxiliaryLaurentVectorEquiv_uFreeEmbedding]
  rw [← uFiniteMultiply_embedding]
  exact congrArg (uFiniteEmbedding (n + 1)) hd

/-- Ungraded `v`-chart kernel elements have actual chart linear-form preimages. -/
theorem profileLaurentCross_vChart_preimage (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (n : ℕ)
    (p : FreeLaurent K (Fin 3 × Sym (Fin 3) (n + 1)))
    (hp : p ∈ LinearMap.range (vFreeEmbedding (K := K)))
    (hQp : profileLaurentCross q hq s (n + 1) p = 0) :
    ∃ x : FreeLaurent K (Fin 3 × Sym (Fin 3) n),
      x ∈ LinearMap.range (vFreeEmbedding (K := K)) ∧ profileLaurentMultiply q hq s n x = p := by
  obtain ⟨c,rfl⟩ := hp
  have hz : vFiniteCross q hq s (n + 1) (fun j i => c (i,j)) = 0 := by
    apply vFiniteEmbedding_injective (n + 1)
    rw [map_zero, vFiniteCross_embedding]
    have h := congrArg auxiliaryLaurentVectorEquiv hQp
    simpa only [auxiliaryLaurentVectorEquiv_profileLaurentCross,
      auxiliaryLaurentVectorEquiv_vFreeEmbedding, map_zero] using h
  obtain ⟨d,hd⟩ := (vFiniteCross_kernel q hq s n _).mp hz
  refine ⟨vFreeEmbedding (fun ij => d ij.2 ij.1), ⟨_,rfl⟩, ?_⟩
  apply auxiliaryLaurentVectorEquiv.injective
  rw [auxiliaryLaurentVectorEquiv_profileLaurentMultiply,
    auxiliaryLaurentVectorEquiv_vFreeEmbedding, auxiliaryLaurentVectorEquiv_vFreeEmbedding]
  rw [← vFiniteMultiply_embedding]
  exact congrArg (vFiniteEmbedding (n + 1)) hd

end ChoppedPlane.QWeyl
