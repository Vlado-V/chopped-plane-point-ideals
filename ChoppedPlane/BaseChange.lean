module

public import ChoppedPlane.RankOpen

@[expose] public section

/-! Rank conditions defined by polynomial matrices descend along field
extensions. A nonzero minor at an extension-field parameter determines a
nonempty principal open over the original infinite field. -/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial Matrix
variable {K L ι m n : Type*} [Field K] [Field L] [Fintype m] [Fintype n]

theorem matrix_det_map {R S j : Type*} [CommRing R] [CommRing S]
    [Fintype j] [DecidableEq j] (k : R →+* S) (A : Matrix j j R) :
    (A.map k).det = k A.det := (k.map_det A).symm

/-- A finite matrix over a field has a nonzero minor of size equal to its rank. -/
theorem exists_rank_minor (A : Matrix m n K) :
    ∃ (rows : Fin A.rank → m) (cols : Fin A.rank → n),
      (A.submatrix rows cols).det ≠ 0 := by
  classical
  have hex := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.col)
  rw [← A.rank_eq_finrank_span_cols] at hex
  obtain ⟨v, hv, _hspan, hli⟩ := hex
  choose cols hcols using hv
  let B : Matrix m (Fin A.rank) K := A.submatrix id cols
  have hBli : LinearIndependent K B.col := by
    have heq : B.col = v := by funext i j; exact congrFun (hcols i) j
    rw [heq]
    exact hli
  have hBrank : B.rank = A.rank := by
    rw [B.rank_eq_finrank_span_cols, finrank_span_eq_card hBli, Fintype.card_fin]
  have hexrow := Submodule.exists_fun_fin_finrank_span_eq K (Set.range B.row)
  rw [← B.rank_eq_finrank_span_row, hBrank] at hexrow
  obtain ⟨w, hw, _hwspan, hwli⟩ := hexrow
  choose rows hrows using hw
  refine ⟨rows, cols, ?_⟩
  have hrow : (A.submatrix rows cols).row = w := by
    funext i j
    exact congrFun (hrows i) j
  have hunit : IsUnit (A.submatrix rows cols) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (hrow.symm ▸ hwli)
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

/-- The rank of a finite matrix is unchanged by an embedding of fields. -/
theorem matrix_rank_map_field (k : K →+* L) (A : Matrix m n K) :
    (A.map k).rank = A.rank := by
  classical
  apply le_antisymm
  · obtain ⟨rows, cols, hminor⟩ := exists_rank_minor (A.map k)
    have hminorK : (A.submatrix rows cols).det ≠ 0 := by
      intro hz
      apply hminor
      rw [show (A.map k).submatrix rows cols = (A.submatrix rows cols).map k by rfl,
        matrix_det_map, hz, map_zero]
    have hh := Matrix.rank_submatrix_le A rows cols
    rwa [Matrix.rank_of_det_ne_zero hminorK, Fintype.card_fin] at hh
  · obtain ⟨rows, cols, hminor⟩ := exists_rank_minor A
    have hminorL : ((A.map k).submatrix rows cols).det ≠ 0 := by
      rw [show (A.map k).submatrix rows cols = (A.submatrix rows cols).map k by rfl,
        matrix_det_map]
      exact fun hz => hminor (k.injective (by simpa using hz))
    have hh := Matrix.rank_submatrix_le (A.map k) rows cols
    rwa [Matrix.rank_of_det_ne_zero hminorL, Fintype.card_fin] at hh

/-- Evaluate a polynomial matrix at a parameter over any field extension. -/
def polynomialMatrixEval (k : K →+* L) (a : ι → L)
    (A : Matrix m n (MvPolynomial ι K)) : Matrix m n L :=
  A.map (eval₂Hom k a)

omit [Fintype m] [Fintype n] in
theorem polynomialMatrixEval_submatrix {r : ℕ} (k : K →+* L) (a : ι → L)
    (A : Matrix m n (MvPolynomial ι K)) (rows : Fin r → m) (cols : Fin r → n) :
    (polynomialMatrixEval k a A).submatrix rows cols =
      (A.submatrix rows cols).map (eval₂Hom k a) := rfl

omit [Fintype m] [Fintype n] in
theorem polynomialMatrixEval_map_parameter (k : K →+* L) (a : ι → K)
    (A : Matrix m n (MvPolynomial ι K)) :
    polynomialMatrixEval k (k ∘ a) A =
      (polynomialMatrixEval (RingHom.id K) a A).map k := by
  ext i j
  exact (eval₂_comp k a (A i j)).symm

/-- At parameters over the original field, evaluation rank is unchanged
after passing to the extension field. -/
theorem polynomialMatrixEval_rank_map_parameter (k : K →+* L) (a : ι → K)
    (A : Matrix m n (MvPolynomial ι K)) :
    (polynomialMatrixEval k (k ∘ a) A).rank =
      (polynomialMatrixEval (RingHom.id K) a A).rank := by
  rw [polynomialMatrixEval_map_parameter, matrix_rank_map_field]

/-- A rank witnessed over an extension field holds on a nonempty principal
open over the original infinite field. No extension parameter has to descend. -/
theorem polynomial_matrix_rank_descent [Infinite K] (k : K →+* L)
    (A : Matrix m n (MvPolynomial ι K)) (a₀ : ι → L) :
    ∃ D : MvPolynomial ι K, (∃ a : ι → K, eval a D ≠ 0) ∧
      ∀ a : ι → K, eval a D ≠ 0 →
        (polynomialMatrixEval k a₀ A).rank ≤
          (polynomialMatrixEval (RingHom.id K) a A).rank := by
  classical
  obtain ⟨rows, cols, hminor⟩ := exists_rank_minor (polynomialMatrixEval k a₀ A)
  let D := (A.submatrix rows cols).det
  have hD : D ≠ 0 := by
    intro hz
    apply hminor
    rw [polynomialMatrixEval_submatrix, matrix_det_map]
    change eval₂Hom k a₀ D = 0
    rw [hz, map_zero]
  have hex : ∃ a : ι → K, eval a D ≠ 0 := by
    by_contra! hz
    exact hD (MvPolynomial.funext hz)
  refine ⟨D, hex, ?_⟩
  intro a ha
  have hminorK : ((polynomialMatrixEval (RingHom.id K) a A).submatrix rows cols).det ≠ 0 := by
    rw [polynomialMatrixEval_submatrix, matrix_det_map]
    exact ha
  have hh := Matrix.rank_submatrix_le (polynomialMatrixEval (RingHom.id K) a A) rows cols
  rwa [Matrix.rank_of_det_ne_zero hminorK, Fintype.card_fin] at hh

omit [Fintype m] [Fintype n] in
/-- Finitely many ranks witnessed over an extension field descend together
to one nonempty principal open, while retaining any prescribed original
nonempty principal-open condition. The matrix sizes may vary with the index. -/
theorem polynomial_matrix_ranks_descent [Infinite K]
    {J : Type*} [Fintype J] {rows cols : J → Type*}
    [∀ j, Fintype (rows j)] [∀ j, Fintype (cols j)]
    (k : K →+* L) (A : ∀ j, Matrix (rows j) (cols j) (MvPolynomial ι K))
    (a₀ : J → ι → L) (Q : MvPolynomial ι K) (hQ : Q ≠ 0) :
    ∃ D : MvPolynomial ι K, (∃ a : ι → K, eval a D ≠ 0) ∧
      ∀ a : ι → K, eval a D ≠ 0 → eval a Q ≠ 0 ∧
        ∀ j, (polynomialMatrixEval k (a₀ j) (A j)).rank ≤
          (polynomialMatrixEval (RingHom.id K) a (A j)).rank := by
  classical
  choose D hD hprop using fun j => polynomial_matrix_rank_descent k (A j) (a₀ j)
  have hne (j : J) : D j ≠ 0 := by
    intro hz
    obtain ⟨a,ha⟩ := hD j
    simp only [hz, map_zero, ne_eq, not_true_eq_false] at ha
  have hprod : Q * ∏ j, D j ≠ 0 :=
    mul_ne_zero hQ (Finset.prod_ne_zero_iff.mpr (fun j _ => hne j))
  have hex : ∃ a : ι → K, eval a (Q * ∏ j, D j) ≠ 0 := by
    by_contra! hz
    exact hprod (MvPolynomial.funext hz)
  refine ⟨Q * ∏ j, D j, hex, ?_⟩
  intro a ha
  have hparts : eval a Q ≠ 0 ∧ ∏ j, eval a (D j) ≠ 0 := by
    simpa only [map_mul, map_prod, mul_ne_zero_iff] using ha
  refine ⟨hparts.1, fun j => hprop j a ?_⟩
  exact Finset.prod_ne_zero_iff.mp hparts.2 j (Finset.mem_univ j)

/-- The adjugate construction of a kernel chart, written entirely over its
coefficient ring, so the same formula can be evaluated after base change. -/
def matrixKernelChart {R : Type*} [CommRing R] [DecidableEq m] [DecidableEq n]
    (E : Matrix m n R) (S : Matrix n m R) : Matrix n n R :=
  (E * S).det • 1 - S * (E * S).adjugate * E

/-- A surjective parameter over the original field supplies a constant
polynomial right-inverse matrix whose chart determinant equals one there. -/
theorem exists_matrix_kernel_chart [DecidableEq m] [DecidableEq n]
    (E : Matrix m n (MvPolynomial ι K)) (a₀ : ι → K)
    (hsurj : Function.Surjective (polynomialMatrixEval (RingHom.id K) a₀ E).mulVecLin) :
    ∃ S : Matrix n m (MvPolynomial ι K), eval a₀ (E * S).det = 1 := by
  let E₀ := polynomialMatrixEval (RingHom.id K) a₀ E
  obtain ⟨s, hs⟩ := E₀.mulVecLin.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let S₀ : Matrix n m K := LinearMap.toMatrix' s
  have hprod₀ : E₀ * S₀ = 1 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_one]
    exact hs
  let S : Matrix n m (MvPolynomial ι K) := S₀.map C
  have hS : S.map (eval a₀) = S₀ := by
    ext i j
    simp [S]
  have hprod : (E * S).map (eval a₀) = 1 := by
    rw [Matrix.map_mul, hS]
    exact hprod₀
  refine ⟨S, ?_⟩
  rw [(eval a₀).map_det]
  change ((E * S).map (eval a₀)).det = 1
  rw [hprod, Matrix.det_one]

/-- Wherever the chart determinant is nonzero, the adjugate chart spans exactly
the kernel and the original map is surjective, over any field. -/
theorem matrixKernelChart_range_ker [DecidableEq m] [DecidableEq n]
    (E : Matrix m n K) (S : Matrix n m K) (hdet : (E * S).det ≠ 0) :
    LinearMap.range (matrixKernelChart E S).mulVecLin = LinearMap.ker E.mulVecLin ∧
      Function.Surjective E.mulVecLin := by
  let T := E * S
  let c := T.det
  have hright (u : m → K) : E.mulVecLin (S.mulVecLin (T.adjugate.mulVecLin u)) = c • u := by
    change E *ᵥ (S *ᵥ (T.adjugate *ᵥ u)) = c • u
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    change (T * T.adjugate) *ᵥ u = _
    rw [Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  have hC (v : n → K) : (matrixKernelChart E S).mulVecLin v =
      c • v - S.mulVecLin (T.adjugate.mulVecLin (E.mulVecLin v)) := by
    simp only [matrixKernelChart, Matrix.mulVecLin_apply, Matrix.sub_mulVec,
      Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, T, c]
  have hker : LinearMap.range (matrixKernelChart E S).mulVecLin ≤ LinearMap.ker E.mulVecLin := by
    rintro _ ⟨v,rfl⟩
    change E.mulVecLin ((matrixKernelChart E S).mulVecLin v) = 0
    rw [hC, map_sub, map_smul, hright, sub_self]
  have hfix (v : n → K) (hv : v ∈ LinearMap.ker E.mulVecLin) :
      (matrixKernelChart E S).mulVecLin v = c • v := by
    rw [hC, show E.mulVecLin v = 0 from hv]
    simp
  refine ⟨le_antisymm hker ?_, ?_⟩
  · intro v hv
    refine ⟨c⁻¹ • v, ?_⟩
    rw [map_smul, hfix v hv, smul_smul, inv_mul_cancel₀ hdet, one_smul]
  · intro u
    refine ⟨c⁻¹ • S.mulVecLin (T.adjugate.mulVecLin u), ?_⟩
    rw [map_smul, hright, smul_smul, inv_mul_cancel₀ hdet, one_smul]

/-- The kernel chart formula commutes with evaluation in every coefficient
field extension. -/
theorem polynomialMatrixEval_kernelChart [DecidableEq m] [DecidableEq n]
    (k : K →+* L) (a : ι → L)
    (E : Matrix m n (MvPolynomial ι K)) (S : Matrix n m (MvPolynomial ι K)) :
    polynomialMatrixEval k a (matrixKernelChart E S) =
      matrixKernelChart (polynomialMatrixEval k a E) (polynomialMatrixEval k a S) := by
  let f := eval₂Hom k a
  change (matrixKernelChart E S).map f = matrixKernelChart (E.map f) (S.map f)
  have hmul : (E * S).map f = E.map f * S.map f := by
    exact Matrix.map_mul
  have hadj : (E * S).adjugate.map f = ((E * S).map f).adjugate := f.map_adjugate _
  have hchart : (matrixKernelChart E S).map f =
      f ((E * S).det) • (1 : Matrix n n L) - S.map f * (E * S).adjugate.map f * E.map f := by
    ext i j
    simp only [matrixKernelChart, Matrix.map_apply, Matrix.sub_apply, map_sub,
      Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero, Matrix.mul_apply, map_sum,
      map_mul, Matrix.map_apply]
  rw [hchart, hadj, ← matrix_det_map f (E * S), hmul]
  rfl

/-- The universal polynomial chart remains a kernel chart over any field
extension, on the original determinant open. -/
theorem polynomial_kernel_chart_baseChange [DecidableEq m] [DecidableEq n]
    (k : K →+* L) (a : ι → L)
    (E : Matrix m n (MvPolynomial ι K)) (S : Matrix n m (MvPolynomial ι K))
    (hdet : eval₂ k a (E * S).det ≠ 0) :
    LinearMap.range (polynomialMatrixEval k a (matrixKernelChart E S)).mulVecLin =
      LinearMap.ker (polynomialMatrixEval k a E).mulVecLin ∧
      Function.Surjective (polynomialMatrixEval k a E).mulVecLin := by
  rw [polynomialMatrixEval_kernelChart]
  apply matrixKernelChart_range_ker
  have hm : (polynomialMatrixEval k a E * polynomialMatrixEval k a S) =
      (E * S).map (eval₂Hom k a) := by
    exact Matrix.map_mul.symm
  rw [hm, matrix_det_map]
  exact hdet

end ChoppedPlane
