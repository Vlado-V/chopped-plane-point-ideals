module

public import ChoppedPlane.MatrixWitness
public import ChoppedPlane.RankOpen

@[expose] public section

/-!
# Independent coefficients and the all-twist rank open

The parameters are the coefficients of every entry of a genuine matrix of
linear forms.  Two finite determinant conditions at the numerical crossing
give all twists simultaneously.  The witness theorem for even column excess
is unconditional; the general helper explicitly asks for an actual matrix
witness, rather than assuming a generic-rank conclusion.
-/

noncomputable section

namespace ChoppedPlane

open Module MvPolynomial

variable (K : Type*) [Field K]

/-- One independent scalar parameter for every monomial coefficient of every entry. -/
abbrev LinearMatrixParameter (a c : ℕ) := Fin a × Fin c × Sym (Fin 3) 1

/-- The universal matrix, specialized at its entry coefficients. -/
def universalLinearMatrix (a c : ℕ) :
    (LinearMatrixParameter a c → K) →ₗ[K] LinearMatrix K a c where
  toFun u i j := ∑ b, u (i, j, b) • formsBasis K 3 1 b
  map_add' u v := by
    funext i j
    change (∑ b, (u (i, j, b) + v (i, j, b)) • formsBasis K 3 1 b) =
      (∑ b, u (i, j, b) • formsBasis K 3 1 b) +
        (∑ b, v (i, j, b) • formsBasis K 3 1 b)
    simp only [add_smul, Finset.sum_add_distrib]
  map_smul' k u := by
    funext i j
    change (∑ b, (k * u (i, j, b)) • formsBasis K 3 1 b) =
      k • ∑ b, u (i, j, b) • formsBasis K 3 1 b
    simp only [Finset.smul_sum, smul_smul]

/-- Every linear matrix is obtained by specializing the universal coefficients. -/
def linearMatrixCoordinates {a c : ℕ} (L : LinearMatrix K a c) :
    LinearMatrixParameter a c → K := fun p => (formsBasis K 3 1).repr (L p.1 p.2.1) p.2.2

@[simp] theorem universalLinearMatrix_coordinates {a c : ℕ} (L : LinearMatrix K a c) :
    universalLinearMatrix K a c (linearMatrixCoordinates K L) = L := by
  funext i j
  change (∑ b, (formsBasis K 3 1).repr (L i j) b • formsBasis K 3 1 b) = L i j
  exact (formsBasis K 3 1).sum_repr (L i j)

variable {K} {a c : ℕ}

/-- Matrix multiplication at a fixed vector is linear in the entries. -/
def linearMatrixApplyParameter (t : ℕ) (v : MatrixSource K c t) :
    LinearMatrix K a c →ₗ[K] MatrixTarget K a t where
  toFun L := linearMatrixMap L t v
  map_add' L M := by
    ext i
    simp [linearMatrixMap, add_mul, Finset.sum_add_distrib]
  map_smul' k L := by
    ext i
    simp [linearMatrixMap, Finset.smul_sum]

/-- Any polynomial family of entries gives polynomial multiplication maps. -/
theorem linearMatrixMap_polynomial_family {ι : Type*}
    (F : (ι → K) → LinearMatrix K a c) (hF : IsPolynomialFamily F) (t : ℕ) :
    IsPolynomialFamily (fun u => linearMatrixMap (F u) t) := by
  apply isPolynomialFamily_linearMap
  intro v
  exact hF.linear_comp (linearMatrixApplyParameter t v)

/-- Every twist of the universal multiplication map has polynomial coefficients. -/
theorem universalLinearMatrixMap_isPolynomialFamily (a c t : ℕ) :
    IsPolynomialFamily (fun u : LinearMatrixParameter a c → K =>
      linearMatrixMap (universalLinearMatrix K a c u) t) := by
  classical
  apply isPolynomialFamily_linearMap
  intro v
  exact isPolynomialFamily_linear
    ((linearMatrixApplyParameter t v).comp (universalLinearMatrix K a c))

/-- A witness in any polynomial parameter family persists in every twist on
one finite determinant open. This allows the linear block to share parameters
with the quadratic rows of a Hilbert--Burch matrix. -/
theorem linearMatrixFamily_allTwists_principal_open {ι : Type*}
    (F : (ι → K) → LinearMatrix K a c) (hF : IsPolynomialFamily F)
    (hac : a < c) (u₀ : ι → K) (h₀ : ∀ t, LinearMatrixMaximalRank (F u₀) t) :
    ∃ D : MvPolynomial ι K, eval u₀ D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 → ∀ t, LinearMatrixMaximalRank (F u) t := by
  let q := linearMatrixCriticalTwist a c
  obtain ⟨D₀, hD₀, hleft⟩ := rank_polynomial_principal_open
    (fun u => linearMatrixMap (F u) (q - 1))
    (linearMatrixMap_polynomial_family F hF (q - 1)) u₀
  obtain ⟨D₁, hD₁, hright⟩ := rank_polynomial_principal_open
    (fun u => linearMatrixMap (F u) q)
    (linearMatrixMap_polynomial_family F hF q) u₀
  have hmax (t : ℕ) {u : ι → K}
      (h : finrank K (linearMatrixMap (F u₀) t).range ≤
        finrank K (linearMatrixMap (F u) t).range) :
      LinearMatrixMaximalRank (F u) t := by
    have hw := h₀ t
    dsimp [LinearMatrixMaximalRank] at hw ⊢
    rw [hw] at h
    exact le_antisymm
      (le_min (LinearMap.finrank_range_le _) (Submodule.finrank_le _)) h
  refine ⟨D₀ * D₁, by simpa using mul_ne_zero hD₀ hD₁, ?_⟩
  intro u hu
  have hu₀ : eval u D₀ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hu)).1
  have hu₁ : eval u D₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hu)).2
  exact linearMatrixMaximalRank_all_of_numeric_critical_checks _ hac
    (fun _ => hmax (q - 1) (hleft u hu₀)) (hmax q (hright u hu₁))

/-- A surjective coefficient family can use a witness built in a different
coordinate system, and obtains a nonempty all-twist principal open. -/
theorem linearMatrixFamily_allTwists_principal_open_of_surjective {ι : Type*}
    (F : (ι → K) → LinearMatrix K a c) (hF : IsPolynomialFamily F)
    (hFsurj : Function.Surjective F) (hac : a < c)
    (hw : ∃ L : LinearMatrix K a c, ∀ t, LinearMatrixMaximalRank L t) :
    ∃ D : MvPolynomial ι K, (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t, LinearMatrixMaximalRank (F u) t := by
  obtain ⟨L, hL⟩ := hw
  obtain ⟨u₀, hu₀⟩ := hFsurj L
  obtain ⟨D, hD, h⟩ := linearMatrixFamily_allTwists_principal_open F hF hac u₀
    (by simpa only [hu₀] using hL)
  exact ⟨D, ⟨u₀, hD⟩, h⟩

/-- A maximal-rank witness supplies a determinant open of maximal-rank maps. -/
theorem universalLinearMatrix_maximalRank_principal_open
    (L : LinearMatrix K a c) (t : ℕ) (hL : LinearMatrixMaximalRank L t) :
    ∃ D : MvPolynomial (LinearMatrixParameter a c) K,
      eval (linearMatrixCoordinates K L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        LinearMatrixMaximalRank (universalLinearMatrix K a c u) t := by
  obtain ⟨D, hD, h⟩ := rank_polynomial_principal_open
    (fun u => linearMatrixMap (universalLinearMatrix K a c u) t)
    (universalLinearMatrixMap_isPolynomialFamily a c t) (linearMatrixCoordinates K L)
  refine ⟨D, hD, fun u hu => ?_⟩
  have hlow := h u hu
  rw [universalLinearMatrix_coordinates] at hlow
  dsimp [LinearMatrixMaximalRank] at hL ⊢
  rw [hL] at hlow
  exact le_antisymm
    (le_min (LinearMap.finrank_range_le _) (Submodule.finrank_le _)) hlow

/-- The critical pair has constant maximum attainable ranks on one nonempty open. -/
theorem universalLinearMatrix_critical_maximum_open [Infinite K] (a c : ℕ) :
    ∃ D : MvPolynomial (LinearMatrixParameter a c) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ L : LinearMatrix K a c,
        (finrank K (linearMatrixMap L (linearMatrixCriticalTwist a c - 1)).range ≤
          finrank K (linearMatrixMap (universalLinearMatrix K a c u)
            (linearMatrixCriticalTwist a c - 1)).range) ∧
        (finrank K (linearMatrixMap L (linearMatrixCriticalTwist a c)).range ≤
          finrank K (linearMatrixMap (universalLinearMatrix K a c u)
            (linearMatrixCriticalTwist a c)).range) := by
  classical
  let q := linearMatrixCriticalTwist a c
  obtain ⟨u₀, D₀, hD₀, hmax₀, heq₀⟩ := maximum_rank_polynomial_principal_open
    (fun u => linearMatrixMap (universalLinearMatrix K a c u) (q - 1))
    (universalLinearMatrixMap_isPolynomialFamily a c (q - 1))
  obtain ⟨u₁, D₁, hD₁, hmax₁, heq₁⟩ := maximum_rank_polynomial_principal_open
    (fun u => linearMatrixMap (universalLinearMatrix K a c u) q)
    (universalLinearMatrixMap_isPolynomialFamily a c q)
  have hz₀ : D₀ ≠ 0 := by intro hz; simp [hz] at hD₀
  have hz₁ : D₁ ≠ 0 := by intro hz; simp [hz] at hD₁
  obtain ⟨u, hu⟩ := nonempty_principal_intersection
    (fun i : Fin 2 => if i = 0 then D₀ else D₁)
    (fun i => by split_ifs <;> assumption)
  have hu₀ : eval u D₀ ≠ 0 := by simpa using hu 0
  have hu₁ : eval u D₁ ≠ 0 := by simpa using hu 1
  refine ⟨D₀ * D₁, ⟨u, by simpa using mul_ne_zero hu₀ hu₁⟩, ?_⟩
  intro v hv L
  have hv₀ : eval v D₀ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hv)).1
  have hv₁ : eval v D₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hv)).2
  constructor
  · rw [heq₀ v hv₀]
    have h := hmax₀ (linearMatrixCoordinates K L)
    rw [universalLinearMatrix_coordinates] at h
    exact h
  · rw [heq₁ v hv₁]
    have h := hmax₁ (linearMatrixCoordinates K L)
    rw [universalLinearMatrix_coordinates] at h
    exact h

/-- One actual all-twist witness produces one nonempty determinant open for all twists. -/
theorem universalLinearMatrix_allTwists_principal_open
    (hac : a < c) (L : LinearMatrix K a c)
    (hL : ∀ t, LinearMatrixMaximalRank L t) :
    ∃ D : MvPolynomial (LinearMatrixParameter a c) K,
      eval (linearMatrixCoordinates K L) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K a c u) t := by
  let q := linearMatrixCriticalTwist a c
  obtain ⟨D₀, hD₀, h₀⟩ := universalLinearMatrix_maximalRank_principal_open L
    (q - 1) (hL (q - 1))
  obtain ⟨D₁, hD₁, h₁⟩ := universalLinearMatrix_maximalRank_principal_open L q (hL q)
  refine ⟨D₀ * D₁, by simpa using mul_ne_zero hD₀ hD₁, ?_⟩
  intro u hu
  have hu₀ : eval u D₀ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hu)).1
  have hu₁ : eval u D₁ ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hu)).2
  exact linearMatrixMaximalRank_all_of_numeric_critical_checks _ hac
    (fun _ => h₀ u hu₀) (h₁ u hu₁)

/-- Existence of a genuine witness, stated separately from the resulting open. -/
theorem exists_allTwists_principal_open_of_witness
    (hac : a < c) (h : ∃ L : LinearMatrix K a c, ∀ t, LinearMatrixMaximalRank L t) :
    ∃ D : MvPolynomial (LinearMatrixParameter a c) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K a c u) t := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨D, hD, hprop⟩ := universalLinearMatrix_allTwists_principal_open hac L hL
  exact ⟨D, ⟨_, hD⟩, hprop⟩

/-- For every positive even excess, the all-twist maximal-rank open is nonempty. -/
theorem exists_even_allTwists_principal_open (a q : ℕ) (hq : 0 < q) :
    ∃ D : MvPolynomial (LinearMatrixParameter a (a + 2 * q)) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K a (a + 2 * q) u) t :=
  exists_allTwists_principal_open_of_witness (by omega)
    (exists_even_extra_columns_maximalRank a q hq)

/-- At least three columns per row also give an unconditional all-twist open. -/
theorem exists_many_columns_allTwists_principal_open (a c : ℕ)
    (hac : a < c) (hcolumns : 3 * a ≤ c) :
    ∃ D : MvPolynomial (LinearMatrixParameter a c) K,
      (∃ u, eval u D ≠ 0) ∧
      ∀ u, eval u D ≠ 0 → ∀ t,
        LinearMatrixMaximalRank (universalLinearMatrix K a c u) t :=
  exists_allTwists_principal_open_of_witness hac
    (exists_many_columns_maximalRank a c hcolumns)

end ChoppedPlane
