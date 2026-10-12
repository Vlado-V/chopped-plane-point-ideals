module

public import ChoppedPlane.TraceReduced

@[expose] public section

/-!
# Reducedness on a polynomial discriminant open

Multiplication matrices in a finite algebra determine its trace pairing. The
trace-pairing determinant is a polynomial in their entries. A split finite
algebra has nondegenerate trace pairing, so a split witness supplies a nonempty
principal open of reduced algebras. The denominator-cleared version applies to
multiplication matrices written in a rational chart.
-/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial
variable {K ι κ : Type*} [Field K] [Fintype κ] [DecidableEq κ]

/-- The trace Gram matrix of polynomial multiplication matrices. -/
def polynomialTraceGram (M : κ → Matrix κ κ (MvPolynomial ι K)) :
    Matrix κ κ (MvPolynomial ι K) :=
  Matrix.of fun i j => (M i * M j).trace

/-- The discriminant polynomial in the supplied structure constants. -/
def polynomialTraceDiscriminant (M : κ → Matrix κ κ (MvPolynomial ι K)) :
    MvPolynomial ι K :=
  (polynomialTraceGram M).det

variable (A : (ι → K) → Type*)
  [∀ a, CommRing (A a)] [∀ a, Algebra K (A a)]
  (b : ∀ a, Basis κ K (A a))

/-- Specializing the polynomial trace matrix gives the actual trace pairing
matrix, with the square of any common denominator as scalar factor. -/
theorem polynomialTraceGram_specialize_scaled
    (M : κ → Matrix κ κ (MvPolynomial ι K))
    (a : ι → K) (h : K)
    (hM : ∀ i, (M i).map (eval a) = h • Algebra.leftMulMatrix (b a) (b a i)) :
    (polynomialTraceGram M).map (eval a) =
      (h * h) • (Algebra.traceForm K (A a)).toMatrix (b a) := by
  ext i j
  rw [Matrix.map_apply]
  change eval a ((M i * M j).trace) =
    (h * h) • ((Algebra.traceForm K (A a)).toMatrix (b a) i j)
  rw [AddMonoidHom.map_trace (eval a), Matrix.map_mul (f := eval a), hM i, hM j,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul]
  have hm : Algebra.leftMulMatrix (b a) (b a i * b a j) =
      Algebra.leftMulMatrix (b a) (b a i) * Algebra.leftMulMatrix (b a) (b a j) :=
    map_mul (Algebra.leftMulMatrix (b a)) _ _
  rw [← hm, ← Algebra.trace_eq_matrix_trace (b a), Algebra.traceForm_toMatrix]

/-- The discriminant specializes to the actual trace discriminant multiplied
by the appropriate even power of the chart denominator. -/
theorem polynomialTraceDiscriminant_specialize_scaled
    (M : κ → Matrix κ κ (MvPolynomial ι K))
    (a : ι → K) (h : K)
    (hM : ∀ i, (M i).map (eval a) = h • Algebra.leftMulMatrix (b a) (b a i)) :
    eval a (polynomialTraceDiscriminant M) =
      (h * h) ^ Fintype.card κ * ((Algebra.traceForm K (A a)).toMatrix (b a)).det := by
  unfold polynomialTraceDiscriminant
  rw [(eval a).map_det]
  change ((polynomialTraceGram M).map (eval a)).det = _
  rw [polynomialTraceGram_specialize_scaled A b M a h hM, Matrix.det_smul]

/-- A split witness gives a nonempty open of reduced algebras when a common
polynomial denominator clears their multiplication matrices. -/
theorem reduced_principal_open_of_split_scaled
    (M : κ → Matrix κ κ (MvPolynomial ι K)) (H : MvPolynomial ι K)
    (hM : ∀ a, eval a H ≠ 0 → ∀ i,
      (M i).map (eval a) = (eval a H) • Algebra.leftMulMatrix (b a) (b a i))
    (a₀ : ι → K) (hH₀ : eval a₀ H ≠ 0)
    (e : A a₀ ≃ₐ[K] (κ → K)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → IsReduced (A a) := by
  let G := polynomialTraceDiscriminant M
  have hdet₀ : ((Algebra.traceForm K (A a₀)).toMatrix (b a₀)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b a₀)).mp
      (traceForm_nondegenerate_of_split e)
  have hG₀ : eval a₀ G ≠ 0 := by
    change eval a₀ (polynomialTraceDiscriminant M) ≠ 0
    rw [polynomialTraceDiscriminant_specialize_scaled A b M a₀ (eval a₀ H) (hM a₀ hH₀)]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hH₀ hH₀)) hdet₀
  refine ⟨H * G, ?_, ?_⟩
  · simpa only [map_mul] using mul_ne_zero hH₀ hG₀
  · intro a ha
    have hparts : eval a H ≠ 0 ∧ eval a G ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using ha
    have hGa := hparts.2
    change eval a (polynomialTraceDiscriminant M) ≠ 0 at hGa
    rw [polynomialTraceDiscriminant_specialize_scaled A b M a (eval a H)
      (hM a hparts.1)] at hGa
    exact isReduced_of_traceForm_det_ne_zero (b a) (mul_ne_zero_iff.mp hGa).2

/-- Polynomial multiplication matrices and a split witness give a nonempty
principal open of reduced finite algebras. -/
theorem reduced_principal_open_of_split
    (M : κ → Matrix κ κ (MvPolynomial ι K))
    (hM : ∀ a i, (M i).map (eval a) = Algebra.leftMulMatrix (b a) (b a i))
    (a₀ : ι → K) (e : A a₀ ≃ₐ[K] (κ → K)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → IsReduced (A a) := by
  apply reduced_principal_open_of_split_scaled A b M 1
  · intro a _ i
    simpa only [map_one, one_smul] using hM a i
  · simp
  · exact e

/-- The denominator chart need only carry bases on its own principal open.
This is the form applicable to quotient algebras whose dimensions can change
outside the chart. -/
theorem reduced_principal_open_of_split_chart
    (M : κ → Matrix κ κ (MvPolynomial ι K)) (H : MvPolynomial ι K)
    (bChart : ∀ a, eval a H ≠ 0 → Basis κ K (A a))
    (hM : ∀ a (ha : eval a H ≠ 0) i,
      (M i).map (eval a) = (eval a H) • Algebra.leftMulMatrix (bChart a ha) (bChart a ha i))
    (a₀ : ι → K) (hH₀ : eval a₀ H ≠ 0)
    (e : A a₀ ≃ₐ[K] (κ → K)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → IsReduced (A a) := by
  let G := polynomialTraceDiscriminant M
  have hdet₀ : ((Algebra.traceForm K (A a₀)).toMatrix (bChart a₀ hH₀)).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (bChart a₀ hH₀)).mp
      (traceForm_nondegenerate_of_split e)
  have hG₀ : eval a₀ G ≠ 0 := by
    change eval a₀ (polynomialTraceDiscriminant M) ≠ 0
    rw [polynomialTraceDiscriminant_specialize_scaled (fun _ : ι → K => A a₀)
      (fun _ => bChart a₀ hH₀) M a₀ (eval a₀ H) (hM a₀ hH₀)]
    exact mul_ne_zero (pow_ne_zero _ (mul_ne_zero hH₀ hH₀)) hdet₀
  refine ⟨H * G, ?_, ?_⟩
  · simpa only [map_mul] using mul_ne_zero hH₀ hG₀
  · intro a ha
    have hparts : eval a H ≠ 0 ∧ eval a G ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using ha
    have hGa := hparts.2
    change eval a (polynomialTraceDiscriminant M) ≠ 0 at hGa
    rw [polynomialTraceDiscriminant_specialize_scaled (fun _ : ι → K => A a)
      (fun _ => bChart a hparts.1) M a (eval a H) (hM a hparts.1)] at hGa
    exact isReduced_of_traceForm_det_ne_zero (bChart a hparts.1) (mul_ne_zero_iff.mp hGa).2

end ChoppedPlane
