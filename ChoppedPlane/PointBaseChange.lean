module

public import ChoppedPlane.BaseChange
public import ChoppedPlane.ChopRankOpen

@[expose] public section

/-! Concrete polynomial evaluation and product matrices in the monomial bases
of homogeneous forms. Their coefficients and ranks can be evaluated over
arbitrary field extensions without an abstract graded-ring base-change API. -/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial Matrix
variable {K L : Type*} [Field K] [Field L] {p n d e : ℕ}

/-- Coefficient extension on genuine homogeneous forms. -/
def formsMap (k : K →+* L) : Forms K n d →ₛₗ[k] Forms L n d where
  toFun f := ⟨map k f.val, f.property.map k⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' c f := by
    apply Subtype.ext
    change map k (c • f.val) = k c • map k f.val
    simp only [smul_eq_C_mul, map_mul, map_C]

@[simp] theorem formsMap_val (k : K →+* L) (f : Forms K n d) :
    (formsMap k f).val = map k f.val := rfl

@[simp] theorem formsMap_basis (k : K →+* L) (i : Sym (Fin n) d) :
    formsMap k (formsBasis K n d i) = formsBasis L n d i := by
  apply Subtype.ext
  exact formsBasis_map K n d k i

/-- The monomial coordinates of coefficient-extended forms are the extended
original coordinates. -/
theorem formsMap_coordinates (k : K →+* L) (f : Forms K n d) (i : Sym (Fin n) d) :
    (formsBasis L n d).repr (formsMap k f) i = k ((formsBasis K n d).repr f i) := by
  classical
  have hform : formsMap k f =
      ∑ j, k ((formsBasis K n d).repr f j) • formsBasis L n d j := by
    conv_lhs => rw [← (formsBasis K n d).sum_repr f]
    simp only [map_sum, map_smulₛₗ, formsMap_basis]
  rw [hform]
  simp [Finsupp.single_apply]

/-- Universal evaluation on affine chart coordinates, with columns indexed
by the actual monomial basis. -/
def pointPolynomialMatrix (K : Type*) [Field K] (p d : ℕ) :
    Matrix (Fin p) (Sym (Fin 3) d) (MvPolynomial (Fin p × Fin 2) K) :=
  fun i j => chartEvaluationPolynomial (formsBasis K 3 d j) i

/-- The universal evaluation matrix specializes to the genuine homogeneous
point evaluation map over every extension field. -/
theorem pointPolynomialMatrix_eval (k : K →+* L) (a : PointCoordinates L p) :
    polynomialMatrixEval k a (pointPolynomialMatrix K p d) =
      LinearMap.toMatrix (formsBasis L 3 d) (Pi.basisFun L (Fin p))
        (pointEvaluation L a d) := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  simp only [Pi.basisFun_repr, pointEvaluation_apply]
  change eval₂ k a (chartEvaluationPolynomial (formsBasis K 3 d j) i) =
    eval (chartPoint L a i) (formsBasis L 3 d j).val
  rw [chartEvaluationPolynomial]
  change (eval₂Hom k a) (eval₂ C ![X (i,0), X (i,1), 1]
    (formsBasis K 3 d j).val) = _
  rw [eval₂_comp_left]
  have hk : (eval₂Hom k a).comp C = k := by ext c; simp
  rw [hk]
  have hv : (eval₂Hom k a) ∘ ![X (i,0), X (i,1), 1] = chartPoint L a i := by
    funext t
    fin_cases t <;> simp [chartPoint]
  rw [hv, ← eval_map, formsBasis_map]

set_option backward.isDefEq.respectTransparency.types false in
theorem pointPolynomialMatrix_coordinates (k : K →+* L) (a : PointCoordinates L p)
    (f : Forms L 3 d) :
    (polynomialMatrixEval k a (pointPolynomialMatrix K p d)).mulVecLin
      ((formsBasis L 3 d).equivFun f) = pointEvaluation L a d f := by
  classical
  apply _root_.funext
  intro i
  have hh := congrFun (LinearMap.toMatrix_mulVec_repr (formsBasis L 3 d)
    (Pi.basisFun L (Fin p)) (pointEvaluation L a d) f) i
  rw [← pointPolynomialMatrix_eval k a] at hh
  simpa only [Basis.equivFun_apply, Pi.basisFun_repr, Matrix.mulVecLin_apply] using hh

theorem pointPolynomialMatrix_surjective_iff (k : K →+* L) (a : PointCoordinates L p) :
    Function.Surjective (polynomialMatrixEval k a (pointPolynomialMatrix K p d)).mulVecLin ↔
      Function.Surjective (pointEvaluation L a d) := by
  let b := formsBasis L 3 d
  constructor
  · intro hs y
    obtain ⟨c,hc⟩ := hs y
    refine ⟨b.equivFun.symm c, ?_⟩
    rw [← pointPolynomialMatrix_coordinates k a, LinearEquiv.apply_symm_apply]
    exact hc
  · intro hs y
    obtain ⟨f,hf⟩ := hs y
    exact ⟨b.equivFun f, (pointPolynomialMatrix_coordinates k a f).trans hf⟩

/-- Evaluation rank is the point Hilbert function, including at parameters
whose coordinates lie in an extension field. -/
theorem pointPolynomialMatrix_rank (k : K →+* L) (a : PointCoordinates L p) :
    (polynomialMatrixEval k a (pointPolynomialMatrix K p d)).rank =
      pointHilbertFunction L a d := by
  classical
  rw [pointPolynomialMatrix_eval,
    Matrix.rank_eq_finrank_range_toLin _ (Pi.basisFun L (Fin p)) (formsBasis L 3 d),
    Matrix.toLin_toMatrix, pointHilbertFunction_eq_rank]

/-- Point Hilbert functions at original-field configurations are unchanged
by coefficient-field extension. -/
theorem pointHilbertFunction_baseChange (k : K →+* L) (a : PointCoordinates K p) :
    pointHilbertFunction L (k ∘ a) d = pointHilbertFunction K a d := by
  rw [← pointPolynomialMatrix_rank k (k ∘ a),
    polynomialMatrixEval_rank_map_parameter,
    pointPolynomialMatrix_rank (RingHom.id K) a]

/-- Constant monomial structure coefficients for multiplying two forms. -/
def formProductCoordinates (K : Type*) [Field K] (d e : ℕ) :
    Matrix (Sym (Fin 3) (d + e)) (Sym (Fin 3) d × Sym (Fin 3) e) K :=
  fun t ij => (formsBasis K 3 (d + e)).repr
    (formProductBilinear (formsBasis K 3 d ij.1) (formsBasis K 3 e ij.2)) t

theorem formProductCoordinates_map (k : K →+* L) :
    (formProductCoordinates K d e).map k = formProductCoordinates L d e := by
  ext t ij
  have hp : formsMap k (formProductBilinear (formsBasis K 3 d ij.1)
      (formsBasis K 3 e ij.2)) =
      formProductBilinear (formsBasis L 3 d ij.1) (formsBasis L 3 e ij.2) := by
    apply Subtype.ext
    simp only [formsMap_val, formProductBilinear_val, map_mul, formsBasis_map]
  change k ((formsBasis K 3 (d + e)).repr _ t) = _
  rw [← formsMap_coordinates, hp]
  rfl

/-- Reconstruct a homogeneous form from one column of a coordinate matrix. -/
def coordinateForm (K : Type*) [Field K] (d : ℕ)
    (M : Matrix (Sym (Fin 3) d) (Sym (Fin 3) d) K) (i : Sym (Fin 3) d) :
    Forms K 3 d := (formsBasis K 3 d).equivFun.symm (M.col i)

/-- The universal matrix of products of the columns of a polynomial kernel
chart with all degree-`e` monomials. -/
def kernelProductPolynomialMatrix {ι : Type*}
    (C : Matrix (Sym (Fin 3) d) (Sym (Fin 3) d) (MvPolynomial ι K)) (e : ℕ) :
    Matrix (Sym (Fin 3) (d + e)) (Sym (Fin 3) d × Sym (Fin 3) e) (MvPolynomial ι K) :=
  fun t ij => ∑ s, C s ij.1 * MvPolynomial.C (formProductCoordinates K d e t (s,ij.2))

/-- Product matrices specialize to the monomial coordinates of actual
products of chart columns, over every extension field. -/
theorem kernelProductPolynomialMatrix_eval {ι : Type*} (k : K →+* L) (a : ι → L)
    (C : Matrix (Sym (Fin 3) d) (Sym (Fin 3) d) (MvPolynomial ι K))
    (t : Sym (Fin 3) (d + e)) (ij : Sym (Fin 3) d × Sym (Fin 3) e) :
    polynomialMatrixEval k a (kernelProductPolynomialMatrix C e) t ij =
      (formsBasis L 3 (d + e)).repr
        (formProductBilinear (coordinateForm L d (polynomialMatrixEval k a C) ij.1)
          (formsBasis L 3 e ij.2)) t := by
  classical
  have hcoeff (s : Sym (Fin 3) d) := congrFun
    (congrFun (formProductCoordinates_map (d := d) (e := e) k) t) (s,ij.2)
  simp only [polynomialMatrixEval, Matrix.map_apply, kernelProductPolynomialMatrix,
    map_sum, map_mul, eval₂Hom_C]
  rw [coordinateForm, Basis.equivFun_symm_apply, map_sum, LinearMap.sum_apply, map_sum]
  simp only [map_smul, LinearMap.smul_apply, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro s _
  exact congrArg (fun c : L => eval₂Hom k a (C s ij.1) * c) (hcoeff s)

/-- Products of spanning first factors with all basis monomials span the
full product space. -/
theorem kernelProductSpace_span_basis {J : Type*} [Fintype J]
    (q : J → Forms K 3 d) :
    Submodule.span K (Set.range (fun ij : J × Sym (Fin 3) e =>
      formProductBilinear (q ij.1) (formsBasis K 3 e ij.2))) =
      kernelProductSpace (formProductBilinear (K := K) (n := 3) (d := d) (e := e))
        (Submodule.span K (Set.range q)) := by
  classical
  let B := formProductBilinear (K := K) (n := 3) (d := d) (e := e)
  rw [← range_kernelProductMap_eq B q _ rfl]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i,j⟩,rfl⟩
    exact ⟨Pi.single i (formsBasis K 3 e j), kernelProductMap_single B q i _⟩
  · rintro _ ⟨w,rfl⟩
    rw [kernelProductMap_apply]
    apply Submodule.sum_mem
    intro i _
    rw [← (formsBasis K 3 e).sum_repr (w i), map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_smul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨(i,j),rfl⟩

/-- The rank of the universal product matrix is the dimension of the actual
product space of its chart-column forms, over every extension field. -/
theorem kernelProductPolynomialMatrix_rank {ι : Type*} (k : K →+* L) (a : ι → L)
    (C : Matrix (Sym (Fin 3) d) (Sym (Fin 3) d) (MvPolynomial ι K)) :
    (polynomialMatrixEval k a (kernelProductPolynomialMatrix C e)).rank =
      finrank L (kernelProductSpace
        (formProductBilinear (K := L) (n := 3) (d := d) (e := e))
        (Submodule.span L (Set.range
          (coordinateForm L d (polynomialMatrixEval k a C))))) := by
  classical
  let q := coordinateForm L d (polynomialMatrixEval k a C)
  let v : Sym (Fin 3) d × Sym (Fin 3) e → Forms L 3 (d + e) :=
    fun ij => formProductBilinear (q ij.1) (formsBasis L 3 e ij.2)
  let b := formsBasis L 3 (d + e)
  have hcol : (polynomialMatrixEval k a (kernelProductPolynomialMatrix C e)).col =
      fun ij => b.equivFun (v ij) := by
    funext ij t
    exact kernelProductPolynomialMatrix_eval k a C t ij
  have hspan : Submodule.span L (Set.range (fun ij => b.equivFun (v ij))) =
      (Submodule.span L (Set.range v)).map b.equivFun.toLinearMap := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Matrix.rank_eq_finrank_span_cols, hcol, hspan,
    LinearEquiv.finrank_map_eq, kernelProductSpace_span_basis]

/-- The reconstructed polynomial chart columns span the actual degree
equations over every coefficient extension on the chart determinant open. -/
theorem point_kernel_chart_columns_span (k : K →+* L) (a : PointCoordinates L p)
    (S : Matrix (Sym (Fin 3) d) (Fin p) (MvPolynomial (Fin p × Fin 2) K))
    (hdet : eval₂ k a (pointPolynomialMatrix K p d * S).det ≠ 0) :
    Submodule.span L (Set.range (coordinateForm L d (polynomialMatrixEval k a
      (matrixKernelChart (pointPolynomialMatrix K p d) S)))) = pointDegreePiece L a d := by
  classical
  let E := polynomialMatrixEval k a (pointPolynomialMatrix K p d)
  let C := polynomialMatrixEval k a (matrixKernelChart (pointPolynomialMatrix K p d) S)
  let b := formsBasis L 3 d
  have hcoord (f : Forms L 3 d) : E.mulVecLin (b.equivFun f) = pointEvaluation L a d f := by
    exact pointPolynomialMatrix_coordinates k a f
  have hker : (LinearMap.ker E.mulVecLin).map b.equivFun.symm.toLinearMap =
      pointDegreePiece L a d := by
    ext f
    constructor
    · rintro ⟨c,hc,rfl⟩
      change pointEvaluation L a d (b.equivFun.symm c) = 0
      rw [← hcoord, LinearEquiv.apply_symm_apply]
      exact hc
    · intro hf
      refine ⟨b.equivFun f, ?_, b.equivFun.symm_apply_apply f⟩
      change E.mulVecLin (b.equivFun f) = 0
      rw [hcoord]
      exact hf
  have hchart := (polynomial_kernel_chart_baseChange k a (pointPolynomialMatrix K p d) S hdet).1
  change LinearMap.range C.mulVecLin = LinearMap.ker E.mulVecLin at hchart
  rw [← hker, ← hchart, Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
  rfl

/-- The universal chart product matrix measures the actual chopped Hilbert
function on its determinant open, over every coefficient extension. -/
theorem choppedHilbertFunction_add_matrix_rank (k : K →+* L) (a : PointCoordinates L p)
    (S : Matrix (Sym (Fin 3) d) (Fin p) (MvPolynomial (Fin p × Fin 2) K))
    (hdet : eval₂ k a (pointPolynomialMatrix K p d * S).det ≠ 0) (e : ℕ) :
    choppedHilbertFunction a d (d + e) +
      (polynomialMatrixEval k a (kernelProductPolynomialMatrix
        (matrixKernelChart (pointPolynomialMatrix K p d) S) e)).rank =
      (d + e + 2).choose 2 := by
  rw [kernelProductPolynomialMatrix_rank, point_kernel_chart_columns_span k a S hdet,
    kernelProductSpace_eq_generatedProducts]
  have hh := (generatedProducts (d := d) (pointDegreeSpace L a d) e).finrank_quotient_add_finrank
  rw [generated_finrank_eq_hilbertFunction _ (pointDegreeSpace_homogeneous a) e,
    finrank_plane_forms] at hh
  exact hh

/-- Actual extension-field chopped-Hilbert-function witnesses descend to one
nonempty principal open over the original infinite field. Only finitely many
degrees need witnesses; all rank descent is unconditional linear algebra. -/
theorem choppedHilbertFunction_extension_witnesses [Infinite K]
    {J : Type*} [Fintype J] (k : K →+* L)
    (S : Matrix (Sym (Fin 3) d) (Fin p) (MvPolynomial (Fin p × Fin 2) K))
    (hQ : (pointPolynomialMatrix K p d * S).det ≠ 0)
    (e : J → ℕ) (a₀ : J → PointCoordinates L p)
    (hdet : ∀ j, eval₂ k (a₀ j) (pointPolynomialMatrix K p d * S).det ≠ 0) :
    ∃ D : MvPolynomial (Fin p × Fin 2) K, (∃ a, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointEvaluation K a d) ∧
        ∀ j, choppedHilbertFunction a d (d + e j) ≤
          choppedHilbertFunction (a₀ j) d (d + e j) := by
  classical
  let E := pointPolynomialMatrix K p d
  let C := matrixKernelChart E S
  let F (j : J) := kernelProductPolynomialMatrix C (e j)
  obtain ⟨D, hD, hprop⟩ := polynomial_matrix_ranks_descent k F a₀ (E * S).det hQ
  refine ⟨D, hD, ?_⟩
  intro a ha
  obtain ⟨hQa,hrank⟩ := hprop a ha
  have hs := (polynomial_kernel_chart_baseChange (RingHom.id K) a E S hQa).2
  have hpoint : pointHilbertFunction K a d = p := by
    rw [← pointPolynomialMatrix_rank (RingHom.id K) a]
    change finrank K (LinearMap.range (polynomialMatrixEval (RingHom.id K) a E).mulVecLin) = p
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, finrank_pi, Fintype.card_fin]
  refine ⟨pointEvaluation_surjective_of_hilbert_eq a hpoint, ?_⟩
  intro j
  have hK := choppedHilbertFunction_add_matrix_rank (RingHom.id K) a S hQa (e j)
  have hL := choppedHilbertFunction_add_matrix_rank k (a₀ j) S (hdet j) (e j)
  have hr := hrank j
  change _ + (polynomialMatrixEval (RingHom.id K) a (F j)).rank = _ at hK
  change _ + (polynomialMatrixEval k (a₀ j) (F j)).rank = _ at hL
  omega

/-- Extension witnesses can first be moved into the fixed chart open without
increasing their chopped Hilbert functions. Thus no chart-membership
assumption is required of the supplied extension-field configurations. -/
theorem choppedHilbertFunction_extension_witnesses_of_surjective [Infinite K]
    {J : Type*} [Fintype J] (k : K →+* L)
    (S : Matrix (Sym (Fin 3) d) (Fin p) (MvPolynomial (Fin p × Fin 2) K))
    (hQ : (pointPolynomialMatrix K p d * S).det ≠ 0)
    (e : J → ℕ) (a₀ : J → PointCoordinates L p)
    (hsurj : ∀ j, Function.Surjective (pointEvaluation L (a₀ j) d)) :
    ∃ D : MvPolynomial (Fin p × Fin 2) K, (∃ a, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointEvaluation K a d) ∧
        ∀ j, choppedHilbertFunction a d (d + e j) ≤
          choppedHilbertFunction (a₀ j) d (d + e j) := by
  classical
  let : Infinite L := Infinite.of_injective k k.injective
  let Q := (pointPolynomialMatrix K p d * S).det
  have hQL : map k Q ≠ 0 := fun hz => hQ (MvPolynomial.map_injective k k.injective
    (by simpa only [map_zero] using hz))
  have hchoose (j : J) : ∃ b : PointCoordinates L p, eval₂ k b Q ≠ 0 ∧
      choppedHilbertFunction b d (d + e j) ≤ choppedHilbertFunction (a₀ j) d (d + e j) := by
    obtain ⟨D,hD,hupper⟩ := choppedHilbertFunction_principal_upper (a₀ j) (hsurj j) (e j)
    have hDne : D ≠ 0 := by intro hz; simp only [hz,map_zero,ne_eq,not_true_eq_false] at hD
    have hprod : map k Q * D ≠ 0 := mul_ne_zero hQL hDne
    have hex : ∃ b : PointCoordinates L p, eval b (map k Q * D) ≠ 0 := by
      by_contra! hz
      exact hprod (MvPolynomial.funext hz)
    obtain ⟨b,hb⟩ := hex
    have hparts : eval b (map k Q) ≠ 0 ∧ eval b D ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using hb
    exact ⟨b, by simpa only [eval_map] using hparts.1, (hupper b hparts.2).2⟩
  choose b hb hle using hchoose
  obtain ⟨D,hD,hprop⟩ := choppedHilbertFunction_extension_witnesses k S hQ e b hb
  refine ⟨D,hD,fun a ha => ?_⟩
  obtain ⟨hs,hr⟩ := hprop a ha
  exact ⟨hs,fun j => (hr j).trans (hle j)⟩

/-- Finite actual chopped-Hilbert-function witnesses over any extension field
descend to a common principal open over the original infinite field. -/
theorem choppedHilbertFunction_descend [Infinite K]
    {J : Type*} [Fintype J] (k : K →+* L) (hp : p ≤ (d + 2).choose 2)
    (e : J → ℕ) (a₀ : J → PointCoordinates L p)
    (hsurj : ∀ j, Function.Surjective (pointEvaluation L (a₀ j) d)) :
    ∃ D : MvPolynomial (Fin p × Fin 2) K, (∃ a, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (pointEvaluation K a d) ∧
        ∀ j, choppedHilbertFunction a d (d + e j) ≤
          choppedHilbertFunction (a₀ j) d (d + e j) := by
  classical
  obtain ⟨a,hha⟩ := exists_pointHilbertFunction_maximal (K := K) p d
  rw [min_eq_right hp] at hha
  have hs := pointEvaluation_surjective_of_hilbert_eq a hha
  obtain ⟨S,hS⟩ := exists_matrix_kernel_chart (pointPolynomialMatrix K p d) a
    ((pointPolynomialMatrix_surjective_iff (RingHom.id K) a).mpr hs)
  have hQ : (pointPolynomialMatrix K p d * S).det ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hS
    exact zero_ne_one hS
  exact choppedHilbertFunction_extension_witnesses_of_surjective k S hQ e a₀ hsurj

end ChoppedPlane
