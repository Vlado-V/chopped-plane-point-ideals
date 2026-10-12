module

public import ChoppedPlane.GradedPresentation
public import ChoppedPlane.FerrersGrid
public import ChoppedPlane.RankOpen

@[expose] public section

/-!
# Independent coefficients of a homogeneous Hilbert–Burch matrix

Every coefficient of every entry is an independent parameter.  The actual
cofactors and all their graded multiplication maps are polynomial families.
An explicit surjective restriction at infinity gives a nonempty principal
open on which the binary ideal contains a complete homogeneous component.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module

variable {K : Type*} [Field K] {c : ℕ}

/-- Independent parameters, with the degree depending on the row. -/
abbrev RowMatrixParameter (δ : Fin (c + 1) → ℕ) :=
  Σ i : Fin (c + 1), Fin c × Sym (Fin 3) (δ i)

/-- Matrices with the prescribed homogeneous row degrees. -/
abbrev HomogeneousRowMatrix (K : Type*) [Field K] (δ : Fin (c + 1) → ℕ) :=
  ∀ i : Fin (c + 1), Fin c → Forms K 3 (δ i)

/-- Specialization of the independent entry coefficients. -/
def universalRowMatrix (δ : Fin (c + 1) → ℕ) :
    (RowMatrixParameter δ → K) →ₗ[K] HomogeneousRowMatrix K δ where
  toFun u i j := ∑ s, u ⟨i, j, s⟩ • formsBasis K 3 (δ i) s
  map_add' u v := by
    funext i j
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' k u := by
    funext i j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul,
      RingHom.id_apply]

/-- Coefficients of a given homogeneous row matrix. -/
def rowMatrixCoordinates (δ : Fin (c + 1) → ℕ) (B : HomogeneousRowMatrix K δ) :
    RowMatrixParameter δ → K :=
  fun p => (formsBasis K 3 (δ p.1)).repr (B p.1 p.2.1) p.2.2

@[simp] theorem universalRowMatrix_coordinates (δ : Fin (c + 1) → ℕ)
    (B : HomogeneousRowMatrix K δ) :
    universalRowMatrix δ (rowMatrixCoordinates δ B) = B := by
  funext i j
  exact (formsBasis K 3 (δ i)).sum_repr (B i j)

/-- The same matrix in the ordinary polynomial ring. -/
def rowMatrixVal (δ : Fin (c + 1) → ℕ) (B : HomogeneousRowMatrix K δ) :
    Matrix (Fin (c + 1)) (Fin c) (Poly K 3) := fun i j => (B i j).val

theorem rowMatrixVal_homogeneous (δ : Fin (c + 1) → ℕ)
    (B : HomogeneousRowMatrix K δ) :
    ∀ i j, (rowMatrixVal δ B i j).IsHomogeneous (δ i) := fun i j => (B i j).property

/-- Polynomial specialization with values in any commutative `K`-algebra. -/
def coefficientSpecialization {ι R : Type*} [CommRing R] [Algebra K R]
    (u : ι → K) : MvPolynomial ι R →+* R :=
  eval₂Hom (RingHom.id R) (fun i => algebraMap K R (u i))

/-- A polynomial with algebra-valued coefficients is a polynomial vector
family; no finite-dimensionality of its coefficient algebra is required. -/
theorem coefficientSpecialization_isPolynomialFamily {ι R : Type*}
    [CommRing R] [Algebra K R] (P : MvPolynomial ι R) :
    IsPolynomialFamily (fun u : ι → K => coefficientSpecialization u P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simpa [coefficientSpecialization] using
      (isPolynomialFamily_const (ι := ι) r)
  | add P Q hP hQ => simpa only [map_add] using hP.add hQ
  | mul_X P i hP =>
      simpa [coefficientSpecialization, Algebra.smul_def, mul_comm] using
        (isPolynomialFamily_coordinate (K := K) i).smul hP

/-- Each universal entry, before specialization, is a parameter polynomial
whose coefficients are genuine homogeneous forms. -/
def universalRowEntryPolynomial (δ : Fin (c + 1) → ℕ)
    (i : Fin (c + 1)) (j : Fin c) :
    MvPolynomial (RowMatrixParameter δ) (Poly K 3) :=
  ∑ s, C (formsBasis K 3 (δ i) s).val * X ⟨i, j, s⟩

@[simp] theorem universalRowEntryPolynomial_specialize (δ : Fin (c + 1) → ℕ)
    (u : RowMatrixParameter δ → K) (i : Fin (c + 1)) (j : Fin c) :
    coefficientSpecialization u (universalRowEntryPolynomial δ i j) =
      rowMatrixVal δ (universalRowMatrix δ u) i j := by
  simp [coefficientSpecialization, universalRowEntryPolynomial, rowMatrixVal,
    universalRowMatrix, Algebra.smul_def, mul_comm]

/-- The actual alternating cofactors, as polynomials in independent parameters. -/
def universalSignedCofactorPolynomial (δ : Fin (c + 1) → ℕ)
    (i : Fin (c + 1)) : MvPolynomial (RowMatrixParameter δ) (Poly K 3) :=
  signedMaximalMinor (universalRowEntryPolynomial δ) i

@[simp] theorem universalSignedCofactorPolynomial_specialize
    (δ : Fin (c + 1) → ℕ) (u : RowMatrixParameter δ → K) (i : Fin (c + 1)) :
    coefficientSpecialization u (universalSignedCofactorPolynomial δ i) =
      signedMaximalMinor (rowMatrixVal δ (universalRowMatrix δ u)) i := by
  classical
  simp only [universalSignedCofactorPolynomial, signedMaximalMinor, map_mul,
    map_pow, map_neg, map_one, maximalMinor, RingHom.map_det]
  apply congrArg (fun p : Poly K 3 => (-1) ^ i.val * p)
  apply congrArg Matrix.det
  funext j k
  exact universalRowEntryPolynomial_specialize δ u _ _

/-- Cofactors vary polynomially as vectors in the polynomial ring. -/
theorem universalSignedCofactor_isPolynomialFamily (δ : Fin (c + 1) → ℕ)
    (i : Fin (c + 1)) :
    IsPolynomialFamily (fun u : RowMatrixParameter δ → K =>
      signedMaximalMinor (rowMatrixVal δ (universalRowMatrix δ u)) i) := by
  simpa only [universalSignedCofactorPolynomial_specialize] using
    coefficientSpecialization_isPolynomialFamily (K := K)
      (universalSignedCofactorPolynomial (K := K) δ i)

/-- The cofactor in its precise homogeneous form space. -/
def universalRowCofactorForm (δ : Fin (c + 1) → ℕ)
    (u : RowMatrixParameter δ → K) (i : Fin (c + 1)) :
    Forms K 3 ((∑ j, δ j) - δ i) :=
  ⟨signedMaximalMinor (rowMatrixVal δ (universalRowMatrix δ u)) i,
    signedMaximalMinor_homogeneous_total _ δ (rowMatrixVal_homogeneous δ _) i⟩

/-- Cofactor polynomiality holds in the finite-dimensional homogeneous space. -/
theorem universalRowCofactorForm_isPolynomialFamily (δ : Fin (c + 1) → ℕ)
    (i : Fin (c + 1)) :
    IsPolynomialFamily (fun u : RowMatrixParameter δ → K =>
      universalRowCofactorForm δ u i) := by
  let P : Poly K 3 →ₗ[K] Forms K 3 ((∑ j, δ j) - δ i) :=
    (homogeneousComponent ((∑ j, δ j) - δ i)).codRestrict _
      (homogeneousComponent_mem _)
  have h := (universalSignedCofactor_isPolynomialFamily δ i).linear_comp P
  convert h using 1
  funext u
  apply Subtype.ext
  exact (homogeneousComponent_eq_self
    (universalRowCofactorForm δ u i).property).symm

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Homogeneity of the actual maximal-minor ideal, for arbitrary row degrees. -/
theorem maximalMinorIdeal_homogeneous {n : ℕ}
    (δ : Fin (c + 1) → ℕ)
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (δ i)) :
    (maximalMinorIdeal B).IsHomogeneous (homogeneousSubmodule (Fin n) K) := by
  apply Ideal.homogeneous_span
  rintro f ⟨i, rfl⟩
  exact ⟨_, signedMaximalMinor_homogeneous_total B δ hB i⟩

/-- Projection to a signed homogeneous component, with its actual subtype. -/
def signedProjection (n : ℕ) (t : ℤ) : Poly K n →ₗ[K] signedForms K n t :=
  (signedComponent t).codRestrict _ (signedComponent_mem t)

@[simp] theorem signedProjection_self (n : ℕ) (t : ℤ) (f : signedForms K n t) :
    signedProjection n t f.val = f := by
  apply Subtype.ext
  exact signedComponent_self t f

/-- Multiplication by a fixed polynomial is linear over the coefficient field. -/
def polynomialMulRight (n : ℕ) (p : Poly K n) : Poly K n →ₗ[K] Poly K n where
  toFun f := f * p
  map_add' f g := add_mul f g p
  map_smul' k f := smul_mul_assoc k f p

/-- Every twist of the universal cofactor map has polynomial coefficients. -/
theorem universalRowCofactorMap_isPolynomialFamily (δ : Fin (c + 1) → ℕ)
    (e : ℤ) :
    IsPolynomialFamily (fun u : RowMatrixParameter δ → K =>
      gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
        (rowMatrixVal_homogeneous δ _) e) := by
  classical
  apply isPolynomialFamily_linearMap
  intro v
  have h := IsPolynomialFamily.sum (fun i =>
    (universalSignedCofactor_isPolynomialFamily δ i).linear_comp
      (polynomialMulRight 3 (v i).val))
  have hp := h.linear_comp (signedProjection 3 (e + ∑ i, δ i))
  convert hp using 1
  funext u
  apply Subtype.ext
  change _ = signedComponent _
    (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
      (rowMatrixVal_homogeneous δ _) e v).val
  exact (signedComponent_self _
    (gradedCofactorMap (rowMatrixVal δ (universalRowMatrix δ u)) δ
      (rowMatrixVal_homogeneous δ _) e v)).symm

/-- Restriction to the line at infinity preserves the homogeneous degree. -/
theorem infinityMap_homogeneous {t : ℕ} {f : Poly K 3} (hf : f.IsHomogeneous t) :
    (Ferrers.infinityMap f).IsHomogeneous t := by
  change (eval₂ (C : K →+* Poly K 2) ![X 0, X 1, 0] f).IsHomogeneous t
  have h : (eval₂ (C : K →+* Poly K 2) ![X 0, X 1, 0] f).IsHomogeneous (1 * t) :=
    hf.eval₂ (C : K →+* Poly K 2) ![X 0, X 1, 0]
      (fun k => MvPolynomial.isHomogeneous_C (σ := Fin 2) k)
      (fun i => by
        fin_cases i
        · exact isHomogeneous_X K 0
        · exact isHomogeneous_X K 1
        · exact isHomogeneous_zero (Fin 2) K 1)
  rw [Nat.one_mul] at h
  exact h

/-- Restriction at infinity as a linear map over the original field. -/
def infinityLinear : Poly K 3 →ₗ[K] Poly K 2 where
  toFun := Ferrers.infinityMap
  map_add' f g := map_add _ f g
  map_smul' k f := by simp [Ferrers.infinityMap, Algebra.smul_def]

/-- The universal matrix restricted to `z = 0`. -/
def universalInfinityMatrix (δ : Fin (c + 1) → ℕ)
    (u : RowMatrixParameter δ → K) : Matrix (Fin (c + 1)) (Fin c) (Poly K 2) :=
  (rowMatrixVal δ (universalRowMatrix δ u)).map Ferrers.infinityMap

theorem universalInfinityMatrix_homogeneous (δ : Fin (c + 1) → ℕ)
    (u : RowMatrixParameter δ → K) :
    ∀ i j, (universalInfinityMatrix δ u i j).IsHomogeneous (δ i) :=
  fun i j => infinityMap_homogeneous (rowMatrixVal_homogeneous δ _ i j)

theorem universalInfinitySignedCofactor_isPolynomialFamily
    (δ : Fin (c + 1) → ℕ) (i : Fin (c + 1)) :
    IsPolynomialFamily (fun u : RowMatrixParameter δ → K =>
      signedMaximalMinor (universalInfinityMatrix δ u) i) := by
  simpa only [universalInfinityMatrix, signedMaximalMinor_map, infinityLinear,
    LinearMap.coe_mk, AddHom.coe_mk] using
    (universalSignedCofactor_isPolynomialFamily δ i).linear_comp infinityLinear

/-- The binary cofactor multiplication maps also have polynomial coefficients. -/
theorem universalInfinityCofactorMap_isPolynomialFamily
    (δ : Fin (c + 1) → ℕ) (e : ℤ) :
    IsPolynomialFamily (fun u : RowMatrixParameter δ → K =>
      gradedCofactorMap (universalInfinityMatrix δ u) δ
        (universalInfinityMatrix_homogeneous δ u) e) := by
  classical
  apply isPolynomialFamily_linearMap
  intro v
  have h := IsPolynomialFamily.sum (fun i =>
    (universalInfinitySignedCofactor_isPolynomialFamily δ i).linear_comp
      (polynomialMulRight 2 (v i).val))
  have hp := h.linear_comp (signedProjection 2 (e + ∑ i, δ i))
  convert hp using 1
  funext u
  apply Subtype.ext
  change _ = signedComponent _
    (gradedCofactorMap (universalInfinityMatrix δ u) δ
      (universalInfinityMatrix_homogeneous δ u) e v).val
  exact (signedComponent_self _
    (gradedCofactorMap (universalInfinityMatrix δ u) δ
      (universalInfinityMatrix_homogeneous δ u) e v)).symm

/-- A surjective polynomial map stays surjective on a principal open. -/
theorem surjective_polynomial_principal_open {ι V W : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (A : (ι → K) → (V →ₗ[K] W)) (hA : IsPolynomialFamily A)
    (a₀ : ι → K) (h₀ : Function.Surjective (A a₀)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (A a) := by
  obtain ⟨D, hD, h⟩ := rank_polynomial_principal_open A hA a₀
  refine ⟨D, hD, fun a ha => ?_⟩
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  have hr := h a ha
  rw [LinearMap.range_eq_top.mpr h₀, finrank_top] at hr
  exact hr

/-- An actual binary cofactor-map witness supplies a nonempty degree-cut open.
Its hypothesis is a finite surjectivity calculation at that displayed matrix. -/
theorem universalInfinity_surjective_principal_open
    (δ : Fin (c + 1) → ℕ) (e : ℤ) (B : HomogeneousRowMatrix K δ)
    (hB : Function.Surjective
      (gradedCofactorMap ((rowMatrixVal δ B).map Ferrers.infinityMap) δ
        (fun i j => infinityMap_homogeneous (rowMatrixVal_homogeneous δ B i j)) e)) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      eval (rowMatrixCoordinates δ B) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        Function.Surjective (gradedCofactorMap (universalInfinityMatrix δ u) δ
          (universalInfinityMatrix_homogeneous δ u) e) := by
  apply surjective_polynomial_principal_open _
    (universalInfinityCofactorMap_isPolynomialFamily δ e) (rowMatrixCoordinates δ B)
  simpa only [universalInfinityMatrix, universalRowMatrix_coordinates] using hB

/-- On the degree-cut open every binary form of the specified degree belongs
to the actual maximal-minor ideal at infinity. -/
theorem universalInfinity_degree_cut_principal_open
    (δ : Fin (c + 1) → ℕ) (N : ℕ) (B : HomogeneousRowMatrix K δ)
    (hB : Function.Surjective
      (gradedCofactorMap ((rowMatrixVal δ B).map Ferrers.infinityMap) δ
        (fun i j => infinityMap_homogeneous (rowMatrixVal_homogeneous δ B i j))
        ((N : ℤ) - ∑ i, δ i))) :
    ∃ D : MvPolynomial (RowMatrixParameter δ) K,
      eval (rowMatrixCoordinates δ B) D ≠ 0 ∧
      ∀ u, eval u D ≠ 0 →
        ∀ f : Forms K 2 N, f.val ∈ maximalMinorIdeal (universalInfinityMatrix δ u) := by
  obtain ⟨D, hD, h⟩ := universalInfinity_surjective_principal_open δ
    ((N : ℤ) - ∑ i, δ i) B hB
  refine ⟨D, hD, fun u hu f => ?_⟩
  have hmem : f.val ∈ signedForms K 2 ((N : ℤ) - ∑ i, δ i + ∑ i, δ i) := by
    simpa only [sub_add_cancel, signedForms_nat] using f.property
  let f' : signedForms K 2 ((N : ℤ) - ∑ i, δ i + ∑ i, δ i) := ⟨f.val, hmem⟩
  have hr : f' ∈ (gradedCofactorMap (universalInfinityMatrix δ u) δ
      (universalInfinityMatrix_homogeneous δ u) ((N : ℤ) - ∑ i, δ i)).range := by
    rw [LinearMap.range_eq_top.mpr (h u hu)]
    trivial
  rw [gradedCofactorMap_range_eq_idealPiece] at hr
  exact hr

end ChoppedPlane
