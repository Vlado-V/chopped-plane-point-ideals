module

public import ChoppedPlane.Quotient

@[expose] public section

/-! A homogeneous vector below the degree of every matrix entry cannot be a
polynomial combination of its columns. This is the degree obstruction after
coprime localization descent in the odd-rank construction. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial

variable {K : Type*} [Field K] {n : ℕ} {ι κ : Type*} [Fintype κ]

/-- Polynomial coefficients cannot lower the homogeneous degree of a family
of homogeneous columns. -/
theorem homogeneous_vector_zero_of_lower_degree
    (B : Matrix ι κ (Poly K n)) (δ : κ → ℕ) (t : ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (δ j))
    (ht : ∀ j, t < δ j)
    (f : ι → Poly K n) (hf : ∀ i, (f i).IsHomogeneous t)
    (v : κ → Poly K n) (h : B.mulVec v = f) : f = 0 := by
  funext i
  have heq := congrArg (homogeneousComponent t) (congrFun h i)
  rw [homogeneousComponent_eq_self (hf i)] at heq
  simp only [Matrix.mulVec, dotProduct, map_sum] at heq
  have hz : ∀ j, homogeneousComponent t (B i j * v j) = 0 :=
    fun j => homogeneousComponent_mul_eq_zero_of_lt t (ht j) _ _ (hB i j)
  simpa only [hz, Finset.sum_const_zero, Pi.zero_apply] using heq.symm

/-- A finite family of homogeneous vector columns obeys the same obstruction. -/
theorem homogeneous_sum_zero_of_lower_degree
    (B : κ → ι → Poly K n) (δ : κ → ℕ) (t : ℕ)
    (hB : ∀ i j, (B j i).IsHomogeneous (δ j))
    (ht : ∀ j, t < δ j)
    (f : ι → Poly K n) (hf : ∀ i, (f i).IsHomogeneous t)
    (v : κ → Poly K n) (h : ∀ i, ∑ j, B j i * v j = f i) : f = 0 := by
  exact homogeneous_vector_zero_of_lower_degree (fun i j => B j i) δ t hB ht f hf v
    (funext h)

end ChoppedPlane
