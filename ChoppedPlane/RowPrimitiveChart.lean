module

public import ChoppedPlane.PrimitiveOpen
public import ChoppedPlane.GenericHilbertBurchOpen
public import ChoppedPlane.FerrersInfinityCut
public import ChoppedPlane.PolynomialPi

@[expose] public section

/-! Actual primitive and finite-chart opens for independent row matrices. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K] {c : ℕ}

/-- The explicit split seed, with each entry in its actual form space. -/
def ferrersHomogeneousRowMatrix (δ : Fin (c + 1) → ℕ)
    (α β : Ferrers.RootIndex δ → K) : HomogeneousRowMatrix K δ :=
  fun i j => ⟨Ferrers.seedMatrix δ α β i j, Ferrers.seedMatrix_homogeneous δ α β i j⟩

@[simp] theorem rowMatrixVal_ferrers (δ : Fin (c + 1) → ℕ)
    (α β : Ferrers.RootIndex δ → K) :
    rowMatrixVal δ (ferrersHomogeneousRowMatrix δ α β) = Ferrers.seedMatrix δ α β := rfl

/-- Fixed vertical and horizontal multipliers turn the extreme cofactors into
coprime equal-degree products at the split seed. Their polynomial families
therefore provide a primitive-minor open for arbitrary positive total degree. -/
theorem universalRowMatrix_primitive_principal_open
    (δ : Fin (c + 1) → ℕ) (hdegree : 0 < ∑ i, δ i)
    (α β : Ferrers.RootIndex δ → K) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      eval (rowMatrixCoordinates δ (ferrersHomogeneousRowMatrix δ α β)) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        PrimitiveMaximalMinors (rowMatrixVal δ (universalRowMatrix δ u)) := by
  classical
  let a₀ := rowMatrixCoordinates δ (ferrersHomogeneousRowMatrix δ α β)
  let j : Fin 2 → Fin (c + 1) := fun i => if i = 0 then Fin.last c else 0
  let g : Fin 2 → Poly K 3 := fun i => if i = 0 then Ferrers.rowFirst δ α (Fin.last c)
    else Ferrers.rowSecond δ β 0
  have hg (i : Fin 2) : (g i).IsHomogeneous (δ (j i)) := by
    by_cases hi : i = 0
    · simpa [g, j, hi] using Ferrers.rowFirst_homogeneous δ α (Fin.last c)
    · simpa [g, j, hi] using Ferrers.rowSecond_homogeneous δ β 0
  let q : (RowMatrixParameter δ → K) → Fin 2 → Forms K 3 (∑ i, δ i) :=
    fun u i => ⟨signedMaximalMinor (rowMatrixVal δ (universalRowMatrix δ u)) (j i) * g i,
      by
        change (signedMaximalMinor (rowMatrixVal δ (universalRowMatrix δ u)) (j i) * g i).IsHomogeneous _
        have hh := (universalRowCofactorForm δ u (j i)).property.mul (hg i)
        have hle : δ (j i) ≤ ∑ i, δ i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
        simpa only [universalRowCofactorForm, Nat.sub_add_cancel hle] using hh⟩
  have hpoly : IsPolynomialFamily q := by
    apply IsPolynomialFamily.finite_pi
    intro i
    let P : Poly K 3 →ₗ[K] Forms K 3 (∑ i, δ i) :=
      (homogeneousComponent (∑ i, δ i)).codRestrict _ (homogeneousComponent_mem _)
    have h := ((universalSignedCofactor_isPolynomialFamily (K := K) δ (j i)).linear_comp
      (polynomialMulRight 3 (g i))).linear_comp P
    convert h using 1
    funext u
    apply Subtype.ext
    exact (homogeneousComponent_eq_self (q u i).property).symm
  have hq : ∀ u i, (q u i).val ∈ cofactorIdeal (rowMatrixVal δ (universalRowMatrix δ u)) := by
    intro u i
    apply Ideal.mul_mem_right
    exact Ideal.subset_span ⟨j i, rfl⟩
  have hq₀ : (q a₀ 0).val =
      (-1 : Poly K 3) ^ c * ∏ i, Ferrers.rowFirst δ α i := by
    simp only [q, a₀, j, g, ite_eq_left rfl, universalRowMatrix_coordinates,
      rowMatrixVal_ferrers, signedMaximalMinor, Fin.val_last, maximalMinor,
      Ferrers.seedMatrix_deletedRow_det, Ferrers.cofactorProduct_last]
    rw [mul_assoc]
    congr 1
    have hfilter : Finset.univ.filter (fun i : Fin (c + 1) => i < Fin.last c) =
        Finset.univ.erase (Fin.last c) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true, ne_eq]
      exact lt_iff_le_and_ne.trans (by simp [Fin.le_last])
    rw [hfilter, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have hq₁ : (q a₀ 1).val = ∏ i, Ferrers.rowSecond δ β i := by
    simp only [q, a₀, j, g, show (1 : Fin 2) ≠ 0 by decide, ite_false,
      universalRowMatrix_coordinates, rowMatrixVal_ferrers, signedMaximalMinor,
      Fin.val_zero, pow_zero, one_mul, maximalMinor,
      Ferrers.seedMatrix_deletedRow_det, Ferrers.cofactorProduct_zero]
    have hfilter : Finset.univ.filter (fun i : Fin (c + 1) => (0 : Fin (c + 1)) < i) =
        Finset.univ.erase 0 := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase,
        and_true, ne_eq]
      exact lt_iff_le_and_ne.trans (by simp [ne_comm])
    rw [hfilter, Finset.prod_erase_mul _ _ (Finset.mem_univ _)]
  have hcop : IsRelPrime (q a₀ 0).val (q a₀ 1).val := by
    rw [hq₀, hq₁]
    apply (isRelPrime_mul_unit_left_left ((isUnit_neg_one : IsUnit (-1 : Poly K 3)).pow _)).mpr
    exact Ferrers.firstProducts_relPrime_secondProducts δ α β _ _
  have hnonzero : (q a₀ 0).val ≠ 0 := by
    rw [hq₀]
    apply mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi hz
    have h := congrArg (eval ![1,0,0]) hz
    simp [Ferrers.rowFirst] at h
  exact primitiveMaximalMinors_principal_open_of_ideal_pair
    (fun u => rowMatrixVal δ (universalRowMatrix δ u)) q hpoly hq
    hdegree a₀ hnonzero hcop

/-- One explicit seed supplies a single open with primitive original and
binary minors and a complete binary degree cut. -/
theorem universalRowMatrix_primitive_cut_principal_open
    (δ : Fin (c + 1) → ℕ) (hdegree : 0 < ∑ i, δ i)
    (α β : Ferrers.RootIndex δ → K) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      eval (rowMatrixCoordinates δ (ferrersHomogeneousRowMatrix δ α β)) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        PrimitiveMaximalMinors (rowMatrixVal δ (universalRowMatrix δ u)) ∧
        PrimitiveMaximalMinors (universalInfinityMatrix δ u) ∧
        ∀ f : Forms K 2 (2 * ∑ i, δ i),
          f.val ∈ maximalMinorIdeal (universalInfinityMatrix δ u) := by
  classical
  obtain ⟨G, hG, hprim⟩ := universalRowMatrix_primitive_principal_open δ hdegree α β
  obtain ⟨H, hH, hcut⟩ := universalInfinity_degree_cut_principal_open δ
    (2 * ∑ i, δ i) (ferrersHomogeneousRowMatrix δ α β) (by
      simpa only [rowMatrixVal_ferrers] using
        Ferrers.seed_infinity_gradedCofactorMap_surjective δ α β)
  refine ⟨G * H, by simpa only [map_mul] using mul_ne_zero hG hH, fun u hu => ?_⟩
  have hparts := mul_ne_zero_iff.mp (by simpa only [map_mul] using hu)
  have hbinary : PrimitiveMaximalMinors (universalInfinityMatrix δ u) := by
    apply primitiveMaximalMinors_of_binary_degree_cut _ _
      (fun f => hcut u hparts.2 f) Ferrers.binary_X_relPrime
  exact ⟨hprim u hparts.1, hbinary, hcut u hparts.2⟩

end ChoppedPlane
