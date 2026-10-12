module

public import ChoppedPlane.GradedPresentation
public import ChoppedPlane.FerrersGrid
public import Mathlib

@[expose] public section

/-!
# A binary degree cut for the actual Ferrers seed

The ideal at infinity contains both pure powers of the total row degree.
Every binary monomial of twice that degree is divisible by one of those powers.
-/

noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K]

/-- Two pure powers force every sufficiently high binary homogeneous piece
into an ideal. -/
theorem binary_degree_cut_of_pure_powers (I : Ideal (Poly K 2)) (D t : ℕ)
    (hx : (X 0 : Poly K 2) ^ D ∈ I) (hy : (X 1 : Poly K 2) ^ D ∈ I)
    (ht : 2 * D ≤ t) (f : Forms K 2 t) : f.val ∈ I := by
  classical
  rw [f.val.as_sum]
  apply I.sum_mem
  intro d hd
  have hdegree : d.degree = t := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      f.property (mem_support_iff.mp hd)
  have hsum : d 0 + d 1 = t := by
    simpa [Finsupp.degree_eq_sum, Fin.sum_univ_two] using hdegree
  have hdvd (i : Fin 2) (hi : D ≤ d i) :
      (X i : Poly K 2) ^ D ∣ monomial d (f.val.coeff d) := by
    rw [X_pow_eq_monomial, monomial_dvd_monomial]
    exact ⟨Or.inr (Finsupp.single_le_iff.mpr hi), one_dvd _⟩
  by_cases hxdeg : D ≤ d 0
  · exact I.mem_of_dvd (hdvd 0 hxdeg) hx
  · have hydeg : D ≤ d 1 := by omega
    exact I.mem_of_dvd (hdvd 1 hydeg) hy

namespace Ferrers
variable {c : ℕ}

/-- Mapping a Ferrers cofactor equation maps it into the actual binary
maximal-minor ideal. -/
theorem infinityMap_mem_maximalMinorIdeal (δ : Fin (c + 1) → ℕ)
    (α β : RootIndex δ → K) {p : Poly K 3} (hp : p ∈ cofactorIdeal δ α β) :
    infinityMap p ∈ maximalMinorIdeal ((seedMatrix δ α β).map infinityMap) := by
  rw [← seedMatrix_cofactorIdeal] at hp
  obtain ⟨v, hv⟩ := (mem_cofactorIdeal_iff (seedMatrix δ α β) p).mp hp
  change infinityMap p ∈ ChoppedPlane.cofactorIdeal ((seedMatrix δ α β).map infinityMap)
  apply (mem_cofactorIdeal_iff _ _).mpr
  exact ⟨fun i => infinityMap (v i), by rw [cofactorMap_map, hv]⟩

/-- The vertical pure power lies in the restricted seed's minor ideal. -/
theorem seed_infinity_X_zero_pow_mem (δ : Fin (c + 1) → ℕ)
    (α β : RootIndex δ → K) :
    (X 0 : Poly K 2) ^ (∑ i, δ i) ∈
      maximalMinorIdeal ((seedMatrix δ α β).map infinityMap) := by
  have h := infinityMap_mem_maximalMinorIdeal δ α β (totalFirst_mem δ α β)
  simpa only [map_prod, infinityMap_rowFirst, Finset.prod_pow_eq_pow_sum] using h

/-- The horizontal pure power lies in the restricted seed's minor ideal. -/
theorem seed_infinity_X_one_pow_mem (δ : Fin (c + 1) → ℕ)
    (α β : RootIndex δ → K) :
    (X 1 : Poly K 2) ^ (∑ i, δ i) ∈
      maximalMinorIdeal ((seedMatrix δ α β).map infinityMap) := by
  have h := infinityMap_mem_maximalMinorIdeal δ α β (totalSecond_mem δ α β)
  simpa only [map_prod, infinityMap_rowSecond, Finset.prod_pow_eq_pow_sum] using h

/-- Every binary form of twice the total row degree belongs to the restricted
Ferrers seed's maximal-minor ideal. No distinctness assumptions are needed. -/
theorem seed_binary_degree_cut (δ : Fin (c + 1) → ℕ)
    (α β : RootIndex δ → K) (f : Forms K 2 (2 * ∑ i, δ i)) :
    f.val ∈ maximalMinorIdeal ((seedMatrix δ α β).map infinityMap) := by
  exact binary_degree_cut_of_pure_powers _ _ _
    (seed_infinity_X_zero_pow_mem δ α β) (seed_infinity_X_one_pow_mem δ α β)
    le_rfl f

/-- Restricting the seed preserves its row degrees. -/
theorem seed_infinity_homogeneous (δ : Fin (c + 1) → ℕ)
    (α β : RootIndex δ → K) (i : Fin (c + 1)) (j : Fin c) :
    (((seedMatrix δ α β).map infinityMap) i j).IsHomogeneous (δ i) := by
  classical
  rw [seedMatrix_map_infinity]
  unfold ferrersBidiagonal
  split_ifs
  · exact isHomogeneous_X_pow _ _
  · exact isHomogeneous_X_pow _ _
  · exact isHomogeneous_zero (Fin 2) K (δ i)

/-- The binary graded cofactor map is onto at the explicit degree cut. -/
theorem seed_infinity_gradedCofactorMap_surjective (δ : Fin (c + 1) → ℕ)
    (α β : RootIndex δ → K) :
    Function.Surjective (gradedCofactorMap ((seedMatrix δ α β).map infinityMap)
      δ (seed_infinity_homogeneous δ α β)
      (((2 * ∑ i, δ i : ℕ) : ℤ) - (∑ i, δ i : ℕ))) := by
  apply LinearMap.range_eq_top.mp
  rw [gradedCofactorMap_range_eq_idealPiece]
  apply top_unique
  intro f _
  change f.val ∈ maximalMinorIdeal ((seedMatrix δ α β).map infinityMap)
  have hshift : (((2 * ∑ i, δ i : ℕ) : ℤ) - (∑ i, δ i : ℕ)) +
      (∑ i, δ i : ℕ) = ((2 * ∑ i, δ i : ℕ) : ℤ) := by omega
  have hf : f.val ∈ Forms K 2 (2 * ∑ i, δ i) := by
    simpa only [hshift, signedForms_nat] using f.property
  exact seed_binary_degree_cut δ α β ⟨f.val, hf⟩

end Ferrers
end ChoppedPlane
