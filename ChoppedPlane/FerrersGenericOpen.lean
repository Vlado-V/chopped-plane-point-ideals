module

public import ChoppedPlane.GenericHilbertBurchOpen
public import ChoppedPlane.FerrersInfinityCut

@[expose] public section

/-! The explicit Ferrers matrix discharges the universal infinity rank witness. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K] {c : ℕ}

def ferrersSeedRowMatrix (δ : Fin (c + 1) → ℕ)
    (α β : Ferrers.RootIndex δ → K) : HomogeneousRowMatrix K δ :=
  fun i j => ⟨Ferrers.seedMatrix δ α β i j,
    Ferrers.seedMatrix_homogeneous δ α β i j⟩

@[simp] theorem rowMatrixVal_ferrersSeedRowMatrix (δ : Fin (c + 1) → ℕ)
    (α β : Ferrers.RootIndex δ → K) :
    rowMatrixVal δ (ferrersSeedRowMatrix δ α β) = Ferrers.seedMatrix δ α β := rfl

/-- The infinity degree-cut open is nonempty at every Ferrers specialization. -/
theorem ferrers_universalInfinity_degree_cut_principal_open
    (δ : Fin (c + 1) → ℕ) (α β : Ferrers.RootIndex δ → K) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      eval (rowMatrixCoordinates δ (ferrersSeedRowMatrix δ α β)) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 → ∀ f : Forms K 2 (2 * ∑ i, δ i),
        f.val ∈ maximalMinorIdeal (universalInfinityMatrix δ u) := by
  apply universalInfinity_degree_cut_principal_open δ (2 * ∑ i, δ i)
    (ferrersSeedRowMatrix δ α β)
  simpa only [rowMatrixVal_ferrersSeedRowMatrix] using
    Ferrers.seed_infinity_gradedCofactorMap_surjective δ α β

end ChoppedPlane
