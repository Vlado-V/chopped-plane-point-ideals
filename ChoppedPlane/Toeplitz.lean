module

public import ChoppedPlane.LinearMatrix
public import ChoppedPlane.ToeplitzBinary
public import ChoppedPlane.ToeplitzDivision
public import Mathlib.Algebra.MvPolynomial.Division

@[expose] public section

/-! An explicit rank-two linear matrix. Its coefficient proof is independent of
Steiner bundles, cohomology, and the characteristic of the coefficient field. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K]

/-- A ternary exponent vector, with coordinates in the order `x,y,z`. -/
def planeExponent (h j k : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 h + Finsupp.single 1 j + Finsupp.single 2 k

@[simp] theorem planeExponent_zero (h j k : ℕ) : planeExponent h j k 0 = h := by
  simp [planeExponent]
@[simp] theorem planeExponent_one (h j k : ℕ) : planeExponent h j k 1 = j := by
  simp [planeExponent]
@[simp] theorem planeExponent_two (h j k : ℕ) : planeExponent h j k 2 = k := by
  simp [planeExponent]
@[simp] theorem degree_planeExponent (h j k : ℕ) :
    (planeExponent h j k).degree = h + j + k := by
  simp [planeExponent]

theorem planeExponent_succ_x (h j k : ℕ) :
    planeExponent (h + 1) j k = Finsupp.single 0 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

theorem planeExponent_succ_y (h j k : ℕ) :
    planeExponent h (j + 1) k = Finsupp.single 1 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

theorem planeExponent_succ_z (h j k : ℕ) :
    planeExponent h j (k + 1) = Finsupp.single 2 1 + planeExponent h j k := by
  ext i
  fin_cases i <;> simp [planeExponent]
  omega

@[simp] theorem coeff_x_at_x_zero (p : Poly K 3) (j k : ℕ) :
    (X 0 * p).coeff (planeExponent 0 j k) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

@[simp] theorem coeff_y_at_y_zero (p : Poly K 3) (h k : ℕ) :
    (X 1 * p).coeff (planeExponent h 0 k) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

@[simp] theorem coeff_z_at_z_zero (p : Poly K 3) (h j : ℕ) :
    (X 2 * p).coeff (planeExponent h j 0) = 0 := by
  simp [coeff_X_mul', Finsupp.mem_support_iff]

@[simp] theorem coeff_y_at_y_succ (p : Poly K 3) (h j k : ℕ) :
    (X 1 * p).coeff (planeExponent h (j+1) k) = p.coeff (planeExponent h j k) := by
  rw [planeExponent_succ_y, coeff_X_mul]

@[simp] theorem coeff_z_at_z_succ (p : Poly K 3) (h j k : ℕ) :
    (X 2 * p).coeff (planeExponent h j (k+1)) = p.coeff (planeExponent h j k) := by
  rw [planeExponent_succ_z, coeff_X_mul]

/-- The coefficient at exponent `x=0` in every noninitial column of a Toeplitz
syzygy vanishes below the critical degree. -/
theorem toeplitz_x_zero_coeff {a t : ℕ} (f : ℕ → Poly K 3)
    (heq : ∀ i < a, X 0 * f i + X 1 * f (i+1) + X 2 * f (i+2) = 0)
    (hta : t < a) (i : ℕ) (hia : i ≤ a) (j : ℕ) (hjt : j ≤ t) :
    (f (i+1)).coeff (planeExponent 0 j (t-j)) = 0 := by
  let A : ℕ → ℕ → K := fun i j => (f (i+1)).coeff (planeExponent 0 j (t-j))
  apply binary_coeff_boundary_zero A _ _ _ hta i hia j hjt
  · intro i hi
    have h := congrArg (fun p : Poly K 3 => p.coeff (planeExponent 0 0 (t+1)))
      (heq i hi)
    simpa [A, AddMonoidAlgebra.coeff_add, Nat.add_assoc] using h
  · intro i hi
    have h := congrArg (fun p : Poly K 3 => p.coeff (planeExponent 0 (t+1) 0))
      (heq i hi)
    simpa [A, AddMonoidAlgebra.coeff_add] using h
  · intro i hi j hj
    have h := congrArg (fun p : Poly K 3 => p.coeff (planeExponent 0 (j+1) (t-j)))
      (heq i hi)
    have hk : t-j = (t-(j+1))+1 := by omega
    simp only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.zero_apply, coeff_x_at_x_zero,
      coeff_y_at_y_succ, zero_add] at h
    rw [hk, coeff_z_at_z_succ] at h
    rw [← hk] at h
    simpa only [A, Nat.add_assoc] using (add_comm _ _).trans h

/-- Every ternary exponent is the tuple of its three coordinates. -/
theorem planeExponent_coordinates (e : Fin 3 →₀ ℕ) :
    planeExponent (e 0) (e 1) (e 2) = e := by
  ext i
  fin_cases i <;> simp

/-- Vanishing of all coefficients with zero `x` exponent is equivalent to
having a factor `x`. -/
theorem x_dvd_of_coeff_x_zero (p : Poly K 3)
    (hz : ∀ j k, p.coeff (planeExponent 0 j k) = 0) : X 0 ∣ p := by
  rw [X_dvd_iff_modMonomial_eq_zero]
  ext e
  by_cases he : e 0 = 0
  · have hle : ¬ Finsupp.single 0 1 ≤ e := by
      intro h
      have hh := h 0
      simp [he] at hh
    rw [coeff_modMonomial_of_not_le p hle, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    have h := hz (e 1) (e 2)
    simpa only [← he, planeExponent_coordinates] using h
  · rw [coeff_modMonomial_of_le p, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    simpa only [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.mpr he

/-- Homogeneous syzygies have a factor `x` in all columns after the first. -/
theorem toeplitz_noninitial_x_dvd {a t : ℕ} (f : ℕ → Poly K 3)
    (hf : ∀ i ≤ a+1, (f i).IsHomogeneous t)
    (heq : ∀ i < a, X 0 * f i + X 1 * f (i+1) + X 2 * f (i+2) = 0)
    (hta : t < a) (i : ℕ) (hia : i ≤ a) : X 0 ∣ f (i+1) := by
  apply x_dvd_of_coeff_x_zero
  intro j k
  by_cases hjk : j+k = t
  · have hh : t-j = k := by omega
    simpa only [hh] using toeplitz_x_zero_coeff f heq hta i hia j (by omega)
  · exact (hf (i+1) (by omega)).coeff_eq_zero (by simpa using hjk)

/-- A low-degree homogeneous polynomial syzygy of the Toeplitz matrix is zero. -/
theorem toeplitz_syzygy_zero {a t : ℕ} (f : ℕ → Poly K 3)
    (hf : ∀ i ≤ a+1, (f i).IsHomogeneous t)
    (heq : ∀ i < a, X 0 * f i + X 1 * f (i+1) + X 2 * f (i+2) = 0)
    (hta : t < a) : ∀ i ≤ a+1, f i = 0 := by
  induction a generalizing t f with
  | zero => omega
  | succ a ih =>
    have hdiv : ∀ i ≤ a+1, X 0 ∣ f (i+1) :=
      fun i hi => toeplitz_noninitial_x_dvd f hf heq hta i hi
    have htail : ∀ i ≤ a+1, f (i+1) = 0 := by
      cases t with
      | zero =>
        intro i hi
        exact homogeneous_zero_of_x_dvd (f (i+1)) (hf (i+1) (by omega)) (hdiv i hi)
      | succ t =>
        let g : ℕ → Poly K 3 := fun i => (f (i+1)).divMonomial (Finsupp.single 0 1)
        have hfg : ∀ i ≤ a+1, X 0 * g i = f (i+1) :=
          fun i hi => x_mul_div_of_x_dvd (f (i+1)) (hdiv i hi)
        have hgh : ∀ i ≤ a+1, (g i).IsHomogeneous t :=
          fun i hi => homogeneous_div_x (f (i+1)) (hf (i+1) (by omega))
        have hgeq : ∀ i < a, X 0 * g i + X 1 * g (i+1) + X 2 * g (i+2) = 0 := by
          intro i hi
          have h := heq (i+1) (by omega)
          rw [← hfg i (by omega), ← hfg (i+1) (by omega),
            ← hfg (i+2) (by omega)] at h
          apply (mul_eq_zero.mp (show X 0 *
            (X 0 * g i + X 1 * g (i+1) + X 2 * g (i+2)) = 0 from ?_)).resolve_left
              (X_ne_zero 0)
          convert h using 1; ring
        have hgz := ih g hgh hgeq (by omega)
        intro i hi
        rw [← hfg i hi, hgz i hi, mul_zero]
    have hf0 : f 0 = 0 := by
      have h := heq 0 (by omega)
      simp only [zero_add, htail 0 (by omega), htail 1 (by omega), mul_zero,
        add_zero] at h
      exact (mul_eq_zero.mp h).resolve_left (X_ne_zero 0)
    intro i hi
    cases i with
    | zero => exact hf0
    | succ i => exact htail i (by omega)

/-- The actual Toeplitz matrix with row entries `x,y,z` in consecutive columns. -/
def toeplitzMatrix (K : Type*) [Field K] (a : ℕ) : LinearMatrix K a (a+2) :=
  fun i j =>
    (if j = (⟨i.val, by omega⟩ : Fin (a+2)) then ⟨X 0, isHomogeneous_X K 0⟩ else 0) +
    (if j = (⟨i.val+1, by omega⟩ : Fin (a+2)) then ⟨X 1, isHomogeneous_X K 1⟩ else 0) +
    (if j = (⟨i.val+2, by omega⟩ : Fin (a+2)) then ⟨X 2, isHomogeneous_X K 2⟩ else 0)

@[simp] theorem toeplitzMatrix_val {a : ℕ} (i : Fin a) (j : Fin (a+2)) :
    (toeplitzMatrix K a i j).val =
      (if j = (⟨i.val, by omega⟩ : Fin (a+2)) then X 0 else 0) +
      (if j = (⟨i.val+1, by omega⟩ : Fin (a+2)) then X 1 else 0) +
      (if j = (⟨i.val+2, by omega⟩ : Fin (a+2)) then X 2 else 0) := by
  classical
  unfold toeplitzMatrix
  split_ifs <;> rfl

@[simp] theorem toeplitzMatrix_map_val {a t : ℕ}
    (v : MatrixSource K (a+2) t) (i : Fin a) :
    (linearMatrixMap (toeplitzMatrix K a) t v i).val =
      X 0 * (v ⟨i.val, by omega⟩).val +
      X 1 * (v ⟨i.val+1, by omega⟩).val +
      X 2 * (v ⟨i.val+2, by omega⟩).val := by
  classical
  simp only [linearMatrixMap_val, toeplitzMatrix_val, add_mul, ite_mul, zero_mul,
    Finset.sum_add_distrib]
  simp

/-- The Toeplitz multiplication map is injective below the critical degree. -/
theorem toeplitzMatrix_injective {a t : ℕ} (hta : t < a) :
    Function.Injective (linearMatrixMap (toeplitzMatrix K a) t) := by
  intro v w hvw
  have hzero : linearMatrixMap (toeplitzMatrix K a) t (v-w) = 0 := by
    rw [map_sub, hvw, sub_self]
  let f : ℕ → Poly K 3 := fun i =>
    if h : i < a+2 then ((v-w) ⟨i,h⟩).val else 0
  have hf : ∀ i ≤ a+1, (f i).IsHomogeneous t := by
    intro i hi
    simp only [f, dite_eq_left (by omega : i < a+2)]
    exact ((v-w) ⟨i,by omega⟩).property
  have heq : ∀ i < a, X 0 * f i + X 1 * f (i+1) + X 2 * f (i+2) = 0 := by
    intro i hi
    have h := congrArg (fun u : MatrixTarget K a t => (u ⟨i,hi⟩).val) hzero
    simpa only [toeplitzMatrix_map_val, Pi.zero_apply, Submodule.coe_zero, f,
      dite_eq_left (by omega : i < a+2), dite_eq_left (by omega : i+1 < a+2),
      dite_eq_left (by omega : i+2 < a+2)] using h
  have hz := toeplitz_syzygy_zero f hf heq hta
  funext i
  apply sub_eq_zero.mp
  apply Subtype.ext
  have h := hz i.val (by omega)
  simpa only [f, dite_eq_left i.isLt, Pi.sub_apply, Submodule.coe_zero] using h

/-- The explicit matrix has maximal rank in every twist, over every field. -/
theorem toeplitzMatrix_maximalRank {a : ℕ} (ha : 0 < a) :
    ∀ t, LinearMatrixMaximalRank (toeplitzMatrix K a) t :=
  linearMatrixMaximalRank_all_of_two_extra_columns (toeplitzMatrix K a) ha
    (toeplitzMatrix_injective (by omega))

/-- An unconditional existence theorem for every positive row count and defect two. -/
theorem exists_two_extra_columns_maximalRank (a : ℕ) (ha : 0 < a) :
    ∃ L : LinearMatrix K a (a+2), ∀ t, LinearMatrixMaximalRank L t :=
  ⟨toeplitzMatrix K a, toeplitzMatrix_maximalRank ha⟩

end ChoppedPlane
