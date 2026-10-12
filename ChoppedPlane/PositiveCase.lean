module

public import ChoppedPlane.PositiveBlockRank
public import ChoppedPlane.PositiveMatrixWitness
public import ChoppedPlane.RowChopPointDegree
public import ChoppedPlane.GenericExtensionConclusion
public import ChoppedPlane.ColumnSeedWitness

@[expose] public section

/-! The positive branch uses actual point configurations obtained by
intersecting the cofactor point open and the linear-block rank open. The
remaining input is an honest matrix witness over an extension field. -/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial
variable {K L : Type*} [Field K] [Field L]

/-- The actual point chop of a positive row matrix has the required Hilbert
function whenever its actual linear block has maximal rank in every twist. -/
theorem positiveRow_points_choppedHilbertFunction
    {r a : ℕ} (hr : 0 < r)
    (B : HomogeneousRowMatrix L (positiveRowProfile r a))
    (hprimitive : PrimitiveMaximalMinors (rowMatrixVal (positiveRowProfile r a) B))
    (z : PointCoordinates L (N (positiveRowGeneratorDegree r a) - r))
    (hpieces : ∀ t, pointDegreePiece L z t =
      idealFormPiece (maximalMinorIdeal (rowMatrixVal (positiveRowProfile r a) B)) t)
    (hmax : ∀ t, LinearMatrixMaximalRank (positiveLinearBlock hr B) t) (e : ℕ) :
    choppedHilbertFunction z (positiveRowGeneratorDegree r a)
        (positiveRowGeneratorDegree r a + e) =
      max (N (positiveRowGeneratorDegree r a) - r)
        (N (positiveRowGeneratorDegree r a + e) - r * N e) := by
  classical
  let d := positiveRowGeneratorDegree r a
  let h := (positiveRowColumns_rows r a hr).symm
  let hB := positiveRowMatrix_standard_homogeneous B
  have hdegree : ∑ i, standardRowDegrees r (positiveRowColumns r a) i = d + 2 := by
    rw [sum_standardRowDegrees h]
    dsimp [d, positiveRowGeneratorDegree]
    omega
  have hrow := rowQuadraticChop_hilbertFunction
    (rowMatrixVal (positiveRowProfile r a) B) h hB hprimitive hdegree e
    (positiveRowLinearBlock_maximalRank hr B hmax e)
  rw [← choppedIdeal_eq_quadraticMinorIdeal
    (rowMatrixVal (positiveRowProfile r a) B) h hB hdegree z hpieces,
    idealQuotientHilbertFunction_choppedIdeal] at hrow
  rw [← minorHilbertFunction_nat] at hrow
  have hf := positiveRow_minorHilbertFunction_formula hr B hprimitive ((d + e : ℕ) : ℤ)
  have hge : ¬ ((d + e : ℕ) : ℤ) < (positiveRowGeneratorDegree r a : ℤ) := by
    dsimp [d]
    omega
  rw [ite_eq_right hge] at hf
  rw [hf] at hrow
  obtain ⟨ha, hc⟩ := positiveRow_counts (a := a) hr
  have hblock := block_dimension_identity d r e
  dsimp [d] at hblock
  rw [ha, hc] at hblock
  rw [hblock] at hrow
  have hle : r ≤ N d := by
    have hd : r ≤ d + 1 := by dsimp [d, positiveRowGeneratorDegree]; omega
    exact hd.trans (N_ge_degree_add_one d)
  have hformula := hilbert_max_nat_identity hle e
  dsimp [d] at hrow hformula
  exact_mod_cast hrow.trans hformula.symm

/-- A genuine all-twist matrix witness over an algebraically closed extension
supplies the full generic positive-branch theorem over the original field. -/
theorem genericChoppedConclusion_positive_of_extension_linear_witness
    [CharZero K] [Infinite L] [IsAlgClosed L]
    (k : K →+* L) (d p : ℕ) (hd : 2 ≤ d)
    (hlo : N (d - 1) < p) (hhi : p < N d) (hr : 3 ≤ N d - p)
    (ha : 0 < aCount d (N d - p))
    (hw : ∃ M : LinearMatrix L (aCount d (N d - p)).toNat
        (positiveRowColumns (N d - p) (aCount d (N d - p)).toNat),
      ∀ t, LinearMatrixMaximalRank M t) :
    GenericChoppedConclusion K d p := by
  classical
  let r := N d - p
  let a := (aCount d r).toNat
  have hr' : 2 ≤ r := by dsimp [r]; omega
  have ha' : (a : ℤ) = aCount d r :=
    Int.toNat_of_nonneg (by change 0 ≤ aCount d (N d - p); omega)
  have hdegree : positiveRowGeneratorDegree r a = d := by
    dsimp [positiveRowGeneratorDegree, aCount] at ha' ⊢
    omega
  have hcount : N (positiveRowGeneratorDegree r a) - r = p := by
    rw [hdegree]
    dsimp [r]
    omega
  obtain ⟨B, z, hprimitive, _, hpieces, hmax, hs, _⟩ :=
    positiveRow_exists_point_matrix_witness (K := L) (a := a) hr' hw
  let z' : PointCoordinates L p := castPointCoordinates hcount z
  have hs' : Function.Surjective (pointEvaluation L z' d) := by
    rw [← hdegree]
    simpa only [z', surjective_castPointCoordinates] using hs
  apply genericChoppedConclusion_of_extension_witnesses k d p hd hlo hhi hr
  intro e _
  refine ⟨z', hs', ?_⟩
  have hf := positiveRow_points_choppedHilbertFunction (by omega : 0 < r)
    B hprimitive z hpieces hmax e
  have hleft := congrArg₂ (fun b t => choppedHilbertFunction z b t)
    hdegree (congrArg (fun b => b + e) hdegree)
  have hright :
      max (N (positiveRowGeneratorDegree r a) - r)
        (N (positiveRowGeneratorDegree r a + e) - r * N e) =
      max p (N (d + e) - r * N e) := by
    rw [hcount, hdegree]
  have hf' := hleft.symm.trans (hf.trans hright)
  rw [show choppedHilbertFunction z' d (d + e) = choppedHilbertFunction z d (d + e) from
    choppedHilbertFunction_castPointCoordinates hcount z d (d + e), hf']

/-- The extension witness can always be sought over the algebraic closure
while the resulting principal open is defined over the original field. -/
theorem genericChoppedConclusion_positive_of_linear_witness [CharZero K]
    (d p : ℕ) (hd : 2 ≤ d)
    (hlo : N (d - 1) < p) (hhi : p < N d) (hr : 3 ≤ N d - p)
    (ha : 0 < aCount d (N d - p))
    (hw : ∃ M : LinearMatrix (AlgebraicClosure K) (aCount d (N d - p)).toNat
        (positiveRowColumns (N d - p) (aCount d (N d - p)).toNat),
      ∀ t, LinearMatrixMaximalRank M t) :
    GenericChoppedConclusion K d p :=
  genericChoppedConclusion_positive_of_extension_linear_witness
    (algebraMap K (AlgebraicClosure K)) d p hd hlo hhi hr ha hw

/-- A uniform genuine linear-matrix witness theorem discharges the only
remaining witness input of the positive branch. -/
theorem genericChoppedConclusion_positive_of_uniform_linear_witness [CharZero K]
    (hlinear : ∀ a c : ℕ, a < c → 2 ≤ c - a →
      ∃ M : LinearMatrix (AlgebraicClosure K) a c,
        ∀ t, LinearMatrixMaximalRank M t)
    (d p : ℕ) (hd : 2 ≤ d)
    (hlo : N (d - 1) < p) (hhi : p < N d) (hr : 3 ≤ N d - p)
    (ha : 0 < aCount d (N d - p)) :
    GenericChoppedConclusion K d p := by
  apply genericChoppedConclusion_positive_of_linear_witness d p hd hlo hhi hr ha
  apply hlinear
  · unfold positiveRowColumns
    omega
  · unfold positiveRowColumns
    omega

end ChoppedPlane
