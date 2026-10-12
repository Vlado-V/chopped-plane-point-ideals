module

public import ChoppedPlane.LaurentPairing

@[expose] public section

/-!
# Actual rings for the two binary Laurent charts

The `u` chart allows arbitrary integral powers of `u` and nonnegative powers
of `v`; the `v` chart has the opposite convention.  Their injective algebra
maps into the binary Laurent ring have precisely the chart subspaces used by
the coefficient residue complex.
-/

noncomputable section
namespace ChoppedPlane.BinaryChartRings

open LaurentPairing

variable {K : Type*} [Field K]

abbrev URing (K : Type*) [Field K] := AddMonoidAlgebra K (ℤ × ℕ)
abbrev VRing (K : Type*) [Field K] := AddMonoidAlgebra K (ℕ × ℤ)

def uIndex : ℤ × ℕ →+ ℤ × ℤ where
  toFun e := (e.1, e.2)
  map_zero' := rfl
  map_add' e f := by simp

def vIndex : ℕ × ℤ →+ ℤ × ℤ where
  toFun e := (e.1, e.2)
  map_zero' := rfl
  map_add' e f := by simp

theorem uIndex_injective : Function.Injective uIndex := by
  intro e f h
  apply Prod.ext
  · simpa [uIndex] using congrArg (fun e : ℤ × ℤ => e.1) h
  · simpa [uIndex] using congrArg (fun e : ℤ × ℤ => e.2) h

theorem vIndex_injective : Function.Injective vIndex := by
  intro e f h
  apply Prod.ext
  · simpa [vIndex] using congrArg (fun e : ℤ × ℤ => e.1) h
  · simpa [vIndex] using congrArg (fun e : ℤ × ℤ => e.2) h

def uEmbedding : URing K →ₐ[K] BinaryLaurent K :=
  AddMonoidAlgebra.mapDomainAlgHom K K uIndex

def vEmbedding : VRing K →ₐ[K] BinaryLaurent K :=
  AddMonoidAlgebra.mapDomainAlgHom K K vIndex

theorem uEmbedding_injective : Function.Injective (uEmbedding (K := K)) :=
  AddMonoidAlgebra.mapDomain_injective uIndex_injective

theorem vEmbedding_injective : Function.Injective (vEmbedding (K := K)) :=
  AddMonoidAlgebra.mapDomain_injective vIndex_injective

theorem range_uIndex : Set.range uIndex = {e : ℤ × ℤ | 0 ≤ e.2} := by
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    exact Int.natCast_nonneg p.2
  · intro he
    exact ⟨(e.1, e.2.toNat), Prod.ext rfl (Int.toNat_of_nonneg he)⟩

theorem range_vIndex : Set.range vIndex = {e : ℤ × ℤ | 0 ≤ e.1} := by
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    exact Int.natCast_nonneg p.1
  · intro he
    exact ⟨(e.1.toNat, e.2), Prod.ext (Int.toNat_of_nonneg he) rfl⟩

theorem range_uEmbedding : LinearMap.range (uEmbedding (K := K)).toLinearMap = chartU := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro e he
    change q.coeff.mapDomain uIndex e = 0
    exact Finsupp.mapDomain_of_notMem_range q.coeff e (by simpa [range_uIndex] using he)
  · intro hp
    have hs : (p.coeff.support : Set (ℤ × ℤ)) ⊆ Set.range uIndex := by
      intro e he
      rw [range_uIndex]
      by_contra hn
      have hz := AddMonoidAlgebra.mem_supported'.mp hp e hn
      exact (Finsupp.mem_support_iff.mp he) hz
    refine ⟨AddMonoidAlgebra.comapDomain uIndex uIndex_injective p, ?_⟩
    exact AddMonoidAlgebra.mapDomain_comapDomain hs uIndex_injective

theorem range_vEmbedding : LinearMap.range (vEmbedding (K := K)).toLinearMap = chartV := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply AddMonoidAlgebra.mem_supported'.mpr
    intro e he
    change q.coeff.mapDomain vIndex e = 0
    exact Finsupp.mapDomain_of_notMem_range q.coeff e (by simpa [range_vIndex] using he)
  · intro hp
    have hs : (p.coeff.support : Set (ℤ × ℤ)) ⊆ Set.range vIndex := by
      intro e he
      rw [range_vIndex]
      by_contra hn
      have hz := AddMonoidAlgebra.mem_supported'.mp hp e hn
      exact (Finsupp.mem_support_iff.mp he) hz
    refine ⟨AddMonoidAlgebra.comapDomain vIndex vIndex_injective p, ?_⟩
    exact AddMonoidAlgebra.mapDomain_comapDomain hs vIndex_injective

def uU : URing K := AddMonoidAlgebra.single (1, 0) 1
def vU : URing K := AddMonoidAlgebra.single (0, 1) 1
def uUInv : URing K := AddMonoidAlgebra.single (-1, 0) 1

def uV : VRing K := AddMonoidAlgebra.single (1, 0) 1
def vV : VRing K := AddMonoidAlgebra.single (0, 1) 1
def vVInv : VRing K := AddMonoidAlgebra.single (0, -1) 1

@[simp] theorem uU_mul_inv : uU (K := K) * uUInv = 1 := by
  simp [uU, uUInv, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  rfl

@[simp] theorem vV_mul_inv : vV (K := K) * vVInv = 1 := by
  simp [vV, vVInv, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
  rfl

@[simp] theorem uEmbedding_u : uEmbedding (uU (K := K)) = U := by
  simp [uEmbedding, uU, U, uIndex]

@[simp] theorem uEmbedding_v : uEmbedding (vU (K := K)) = V := by
  simp [uEmbedding, vU, V, uIndex]

@[simp] theorem vEmbedding_u : vEmbedding (uV (K := K)) = U := by
  simp [vEmbedding, uV, U, vIndex]

@[simp] theorem vEmbedding_v : vEmbedding (vV (K := K)) = V := by
  simp [vEmbedding, vV, V, vIndex]

end ChoppedPlane.BinaryChartRings
