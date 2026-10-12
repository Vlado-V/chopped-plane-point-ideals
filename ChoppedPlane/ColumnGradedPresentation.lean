module

public import ChoppedPlane.GradedPresentation

@[expose] public section

/-! The genuine column-weighted Hilbert–Burch presentation used when all
maximal-minor generators have the same degree. The entries in column `j`
have degree `ε j`; the syzygy coefficient degrees vary with the column. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] {n c : ℕ}

/-- A determinant with homogeneous column weights has their sum as degree. -/
theorem determinant_homogeneous_columns {m : ℕ}
    (B : Matrix (Fin m) (Fin m) (Poly K n)) (ε : Fin m → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) :
    B.det.IsHomogeneous (∑ j, ε j) := by
  have h := determinant_homogeneous_rows B.transpose ε (fun i j => hB j i)
  simpa only [Matrix.det_transpose] using h

/-- Every maximal minor of a column-weighted matrix has the same degree. -/
theorem maximalMinor_homogeneous_columns
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) (i : Fin (c + 1)) :
    (maximalMinor B i).IsHomogeneous (∑ j, ε j) :=
  determinant_homogeneous_columns _ ε (fun j k => hB (i.succAbove j) k)

theorem signedMaximalMinor_homogeneous_columns
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) (i : Fin (c + 1)) :
    (signedMaximalMinor B i).IsHomogeneous (∑ j, ε j) := by
  have hm := maximalMinor_homogeneous_columns B ε hB i
  have hconst : ((-1 : Poly K n) ^ i.val).IsHomogeneous 0 := by
    simpa using (isHomogeneous_C (σ := Fin n) (-1 : K)).pow i.val
  simpa [signedMaximalMinor] using hconst.mul hm

/-- The column-weighted free syzygy piece. -/
abbrev columnForms (K : Type*) [Field K] (n : ℕ) (ε : Fin c → ℕ) (e : ℤ) :=
  ∀ j : Fin c, signedForms K n (e - ε j)

/-- Inclusion of equally graded coefficient vectors into the polynomial module. -/
def signedVectorVal {m : ℕ} {e : ℤ} :
    (Fin m → signedForms K n e) →ₗ[K] (Fin m → Poly K n) where
  toFun v i := (v i).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection to equally graded coefficient vectors. -/
def signedVectorComponent (m : ℕ) (e : ℤ) :
    (Fin m → Poly K n) →ₗ[K] (Fin m → signedForms K n e) where
  toFun v i := ⟨signedComponent e (v i), signedComponent_mem _ _⟩
  map_add' _ _ := by ext i; simp
  map_smul' _ _ := by ext i; simp

@[simp] theorem signedVectorComponent_self (m : ℕ) (e : ℤ)
    (v : Fin m → signedForms K n e) :
    signedVectorComponent m e (signedVectorVal v) = v := by
  funext i
  apply Subtype.ext
  exact signedComponent_self e (v i)

/-- Inclusion of column-shifted syzygy coefficients into the ungraded module. -/
def columnFormsVal {ε : Fin c → ℕ} {e : ℤ} :
    columnForms K n ε e →ₗ[K] (Fin c → Poly K n) where
  toFun v j := (v j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection of polynomial coefficients to their column-dependent degrees. -/
def columnFormsComponent (ε : Fin c → ℕ) (e : ℤ) :
    (Fin c → Poly K n) →ₗ[K] columnForms K n ε e where
  toFun v j := ⟨signedComponent (e - ε j) (v j), signedComponent_mem _ _⟩
  map_add' _ _ := by ext j; simp
  map_smul' _ _ := by ext j; simp

/-- Homogeneous extraction from a column-weighted matrix equation. -/
theorem signedComponent_mulVec_columns
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (e : ℤ) (w : Fin c → Poly K n) (i : Fin (c + 1)) :
    signedComponent e (B.mulVec w i) =
      B.mulVec (columnFormsVal (columnFormsComponent ε e w)) i := by
  simp only [Matrix.mulVec, dotProduct, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change signedComponent e (B i j * w j) =
    B i j * signedComponent (e - ε j) (w j)
  simpa only [sub_add_cancel] using
    signedComponent_mul_form (e - ε j) (B i j) (w j) (hB i j)

/-- The matrix map on the genuine column-shifted homogeneous pieces. -/
def columnGradedMatrixMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) (e : ℤ) :
    columnForms K n ε e →ₗ[K] (Fin (c + 1) → signedForms K n e) where
  toFun w i := ⟨B.mulVec (columnFormsVal w) i, by
    apply (mem_signedForms_iff_component_self _ _).mpr
    rw [signedComponent_mulVec_columns B ε hB]
    change B.mulVec (fun j => signedComponent (e - ε j) (w j).val) i = _
    simp only [signedComponent_self]
    rfl⟩
  map_add' w u := by ext i; simp [Matrix.mulVec, dotProduct, columnFormsVal, mul_add, Finset.sum_add_distrib]
  map_smul' r w := by ext i; simp [Matrix.mulVec, dotProduct, columnFormsVal, Finset.smul_sum]

/-- Homogeneous extraction from a cofactor combination of equal-degree generators. -/
theorem signedComponent_cofactorMap_columns
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (e : ℤ) (v : Fin (c + 1) → Poly K n) :
    signedComponent (e + ∑ j, ε j) (cofactorMap B v) =
      cofactorMap B (signedVectorVal (signedVectorComponent (c + 1) e v)) := by
  simp only [cofactorMap_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact signedComponent_mul_form e (signedMaximalMinor B i) (v i)
    (signedMaximalMinor_homogeneous_columns B ε hB i)

/-- The cofactor map from equal-degree coefficient forms into their target degree. -/
def columnGradedCofactorMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) (e : ℤ) :
    (Fin (c + 1) → signedForms K n e) →ₗ[K] signedForms K n (e + ∑ j, ε j) where
  toFun v := ⟨cofactorMap B (signedVectorVal v), by
    apply (mem_signedForms_iff_component_self _ _).mpr
    rw [signedComponent_cofactorMap_columns B ε hB, signedVectorComponent_self]⟩
  map_add' v w := by
    apply Subtype.ext
    simp only [signedVectorVal, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, Submodule.coe_add]
    exact map_add (cofactorMap B) _ _
  map_smul' r v := by
    apply Subtype.ext
    simp [cofactorMap_apply, signedVectorVal]

/-- Every homogeneous syzygy is obtained from homogeneous coefficients of the
column-dependent degrees, by actual UFD Hilbert–Burch exactness. -/
theorem columnGraded_ker_cofactor_eq_range
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (columnGradedCofactorMap B ε hB e).ker = (columnGradedMatrixMap B ε hB e).range := by
  apply le_antisymm
  · intro v hv
    have hpoly : signedVectorVal v ∈ (cofactorMap B).ker := congrArg Subtype.val hv
    rw [ker_cofactorMap_eq_range B hprimitive] at hpoly
    obtain ⟨w, hw⟩ := hpoly
    change B.mulVec w = signedVectorVal v at hw
    refine ⟨columnFormsComponent ε e w, ?_⟩
    funext i
    apply Subtype.ext
    change B.mulVec (columnFormsVal (columnFormsComponent ε e w)) i = (v i).val
    rw [← signedComponent_mulVec_columns B ε hB, hw]
    exact signedComponent_self e (v i)
  · rintro v ⟨w, rfl⟩
    apply Subtype.ext
    exact cofactorMap_mulVec B (columnFormsVal w)

/-- The graded first map is injective in the column-weighted presentation. -/
theorem columnGradedMatrixMap_injective
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    Function.Injective (columnGradedMatrixMap B ε hB e) := by
  intro w u h
  have hpoly : B.mulVec (columnFormsVal w) = B.mulVec (columnFormsVal u) :=
    congrArg signedVectorVal h
  have hcoeff := mulVec_injective_of_primitive B hprimitive hpoly
  funext j
  apply Subtype.ext
  exact congrFun hcoeff j

/-- The genuine homogeneous maximal-minor ideal piece for column weights. -/
def columnMinorIdealPiece
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ) (e : ℤ) :
    Submodule K (signedForms K n (e + ∑ j, ε j)) :=
  (maximalMinorIdeal B).restrictScalars K |>.comap (signedForms K n (e + ∑ j, ε j)).subtype

/-- The graded cofactor image is the actual homogeneous piece of its ideal. -/
theorem columnGradedCofactorMap_range_eq_idealPiece
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) (e : ℤ) :
    (columnGradedCofactorMap B ε hB e).range = columnMinorIdealPiece B ε e := by
  apply le_antisymm
  · rintro f ⟨v, rfl⟩
    change cofactorMap B (signedVectorVal v) ∈
      Submodule.span (Poly K n) (Set.range (signedMaximalMinor B))
    rw [← cofactorMap_range_eq_span]
    exact ⟨signedVectorVal v, rfl⟩
  · intro f hf
    have hfpoly : f.val ∈ (cofactorMap B).range := by
      rw [cofactorMap_range_eq_span]
      exact hf
    obtain ⟨v, hv⟩ := hfpoly
    refine ⟨signedVectorComponent (c + 1) e v, ?_⟩
    apply Subtype.ext
    change cofactorMap B (signedVectorVal (signedVectorComponent (c + 1) e v)) = f.val
    rw [← signedComponent_cofactorMap_columns B ε hB, hv]
    exact signedComponent_self _ f

/-- The column-dependent source dimension is the sum of its signed form dimensions. -/
theorem finrank_columnPlaneForms (ε : Fin c → ℕ) (e : ℤ) :
    (finrank K (columnForms K 3 ε e) : ℤ) = ∑ j, N₂ (e - ε j) := by
  rw [Module.finrank_pi_fintype, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact finrank_signedPlaneForms (e - ε j)

/-- The actual column-weighted ideal-piece dimension from graded exactness. -/
theorem columnMinorIdealPiece_finrank
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (finrank K (columnMinorIdealPiece B ε e) : ℤ) =
      ((c : ℤ) + 1) * N₂ e - ∑ j, N₂ (e - ε j) := by
  have hdim := (columnGradedCofactorMap B ε hB e).finrank_range_add_finrank_ker
  rw [columnGraded_ker_cofactor_eq_range B ε hB hprimitive,
    LinearMap.finrank_range_of_inj (columnGradedMatrixMap_injective B ε hB hprimitive e),
    columnGradedCofactorMap_range_eq_idealPiece B ε hB] at hdim
  have hmid : (finrank K (Fin (c + 1) → signedForms K 3 e) : ℤ) =
      ((c : ℤ) + 1) * N₂ e := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_signedPlaneForms]
  have hcast := congrArg (fun j : ℕ => (j : ℤ)) hdim
  rw [Nat.cast_add, finrank_columnPlaneForms, hmid] at hcast
  omega

/-- The genuine quotient component has the column-weighted Hilbert–Burch coefficients. -/
theorem columnMinorQuotient_finrank
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (finrank K ((signedForms K 3 (e + ∑ j, ε j)) ⧸ columnMinorIdealPiece B ε e) : ℤ) =
      N₂ (e + ∑ j, ε j) - ((c : ℤ) + 1) * N₂ e + ∑ j, N₂ (e - ε j) := by
  have h := (columnMinorIdealPiece B ε e).finrank_quotient_add_finrank
  have hcast := congrArg (fun j : ℕ => (j : ℤ)) h
  rw [Nat.cast_add, finrank_signedPlaneForms, columnMinorIdealPiece_finrank B ε hB hprimitive] at hcast
  omega

theorem minorFormToRingQuotient_ker_columns
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ) (e : ℤ) :
    (minorFormToRingQuotient B (e + ∑ j, ε j)).ker = columnMinorIdealPiece B ε e := by
  ext f
  change Ideal.Quotient.mk (maximalMinorIdeal B) f.val = 0 ↔ f.val ∈ maximalMinorIdeal B
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The actual polynomial-ring-quotient Hilbert function in every integer degree. -/
theorem minorHilbertFunction_columns_formula
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (minorHilbertFunction B (e + ∑ j, ε j) : ℤ) =
      N₂ (e + ∑ j, ε j) - ((c : ℤ) + 1) * N₂ e + ∑ j, N₂ (e - ε j) := by
  have h := (minorFormToRingQuotient B (e + ∑ j, ε j)).quotKerEquivRange.finrank_eq
  rw [minorFormToRingQuotient_ker_columns] at h
  dsimp only [minorHilbertFunction]
  rw [← h]
  exact columnMinorQuotient_finrank B ε hB hprimitive e

/-- The column-weighted Hilbert function indexed directly by the target degree. -/
theorem minorHilbertFunction_columns_at_degree
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (t : ℤ) :
    (minorHilbertFunction B t : ℤ) = N₂ t - ((c : ℤ) + 1) * N₂ (t - ∑ j, ε j) +
      ∑ j, N₂ (t - (∑ k, ε k) - ε j) := by
  have h := minorHilbertFunction_columns_formula B ε hB hprimitive (t - ∑ j, ε j)
  simpa only [sub_add_cancel] using h


/-- The coefficient-field generator space of the actual cofactor minors. -/
def minorGeneratorSpace
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) : Submodule K (Poly K n) :=
  Submodule.span K (Set.range (signedMaximalMinor B))

/-- Taking the coefficient-field span before the ideal span does not change
which actual ideal is generated by the minors. -/
theorem minorGeneratorSpace_idealSpan
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) :
    Ideal.span (minorGeneratorSpace B : Set (Poly K n)) = maximalMinorIdeal B :=
  Submodule.span_span_of_tower K (Poly K n) _

/-- The generic generated-Hilbert-function API measures the same actual
quotient-ring image as the maximal-minor Hilbert function. -/
theorem generatedHilbertFunction_minorGeneratorSpace
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (t : ℕ) :
    generatedHilbertFunction (minorGeneratorSpace B) t = minorHilbertFunction B t := by
  let E : Forms K n t ≃ₗ[K] signedForms K n (t : ℤ) :=
    LinearEquiv.ofEq _ _ (signedForms_nat t).symm
  let ψ := (minorFormToRingQuotient B (t : ℤ)).comp E.toLinearMap
  have hker : (formToRingQuotient t (minorGeneratorSpace B)).ker = ψ.ker := by
    ext f
    change Ideal.Quotient.mk (Ideal.span (minorGeneratorSpace B : Set (Poly K n))) f.val = 0 ↔
      Ideal.Quotient.mk (maximalMinorIdeal B) (E f).val = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.eq_zero_iff_mem]
    change f.val ∈ Ideal.span (minorGeneratorSpace B : Set (Poly K n)) ↔ f.val ∈ maximalMinorIdeal B
    rw [minorGeneratorSpace_idealSpan]
  have h₁ := (formToRingQuotient t (minorGeneratorSpace B)).finrank_range_add_finrank_ker
  have h₂ := ψ.finrank_range_add_finrank_ker
  rw [hker] at h₁
  have hψ : ψ.range = (minorFormToRingQuotient B (t : ℤ)).range :=
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range E)
  dsimp only [generatedHilbertFunction, minorHilbertFunction]
  rw [← hψ]
  omega

/-- The maximal minors as a genuine family of homogeneous generators of the
common degree `∑ ε`, rather than merely degree labels. -/
def columnMinorGeneratorFamily
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) :
    Fin (c + 1) → Forms K n (∑ j, ε j) :=
  fun i => ⟨signedMaximalMinor B i, signedMaximalMinor_homogeneous_columns B ε hB i⟩

theorem minorGeneratorSpace_homogeneous_columns
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j)) :
    minorGeneratorSpace B ≤ Forms K n (∑ j, ε j) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact signedMaximalMinor_homogeneous_columns B ε hB i

/-- Column-weighted Hilbert–Burch in the generic generated-ideal Hilbert-function API. -/
theorem generatedHilbertFunction_columns_formula
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (ε : Fin c → ℕ)
    (hB : ∀ i j, (B i j).IsHomogeneous (ε j))
    (hprimitive : PrimitiveMaximalMinors B) (t : ℕ) :
    (generatedHilbertFunction (minorGeneratorSpace B) t : ℤ) = N₂ t -
      ((c : ℤ) + 1) * N₂ ((t : ℤ) - ∑ j, ε j) +
      ∑ j, N₂ ((t : ℤ) - (∑ k, ε k) - ε j) := by
  rw [generatedHilbertFunction_minorGeneratorSpace]
  exact minorHilbertFunction_columns_at_degree B ε hB hprimitive t

end ChoppedPlane
