module

public import ChoppedPlane.GradedPresentation
public import ChoppedPlane.Presentation
public import ChoppedPlane.SignedIdealPieces

@[expose] public section

/-! The linear-block quotient of an actual row-weighted Hilbert–Burch
presentation. The row splitting is explicitly constructed from the matrix,
including the two low-degree boundary cases through integer shifts. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
namespace ChoppedPlane
open MvPolynomial Matrix Module
variable {K : Type*} [Field K] {n r a c : ℕ}

/-- Standard row degrees: the first `r` rows are quadratic, the rest linear. -/
def standardRowDegrees (r c : ℕ) : Fin (c + 1) → ℕ :=
  fun i => if i.val < r then 2 else 1

def quadraticRow (h : r + a = c + 1) (i : Fin r) : Fin (c + 1) :=
  Fin.cast h (Fin.castAdd a i)

def linearRow (h : r + a = c + 1) (i : Fin a) : Fin (c + 1) :=
  Fin.cast h (Fin.natAdd r i)

@[simp] theorem standardRowDegrees_quadratic (h : r + a = c + 1) (i : Fin r) :
    standardRowDegrees r c (quadraticRow h i) = 2 := by
  simp [standardRowDegrees, quadraticRow]

@[simp] theorem standardRowDegrees_linear (h : r + a = c + 1) (i : Fin a) :
    standardRowDegrees r c (linearRow h i) = 1 := by
  simp [standardRowDegrees, linearRow]

@[simp] theorem quadratic_row_shift (h : r + a = c + 1) (e : ℤ) (i : Fin r) :
    e - 2 + standardRowDegrees r c (quadraticRow h i) = e := by
  rw [standardRowDegrees_quadratic]
  ring

@[simp] theorem linear_row_shift (h : r + a = c + 1) (e : ℤ) (i : Fin a) :
    e - 2 + standardRowDegrees r c (linearRow h i) = e - 1 := by
  rw [standardRowDegrees_linear]
  ring

/-- Restrict an actual graded row vector to its quadratic and linear rows. -/
def standardRowSplitMap (h : r + a = c + 1) (e : ℤ) :
    rowForms K n (standardRowDegrees r c) (e - 2) →ₗ[K]
      (Fin r → signedForms K n e) × (Fin a → signedForms K n (e - 1)) where
  toFun v :=
    (fun i => ⟨(v (quadraticRow h i)).val, by simpa only [quadratic_row_shift] using (v (quadraticRow h i)).property⟩,
     fun i => ⟨(v (linearRow h i)).val, by simpa only [linear_row_shift] using (v (linearRow h i)).property⟩)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every row is in exactly one of the two explicitly indexed blocks. -/
theorem row_cases (h : r + a = c + 1) (i : Fin (c + 1)) :
    (∃ j : Fin r, quadraticRow h j = i) ∨ (∃ j : Fin a, linearRow h j = i) := by
  let k : Fin (r + a) := Fin.cast h.symm i
  have hk : Fin.cast h k = i := by ext; rfl
  by_cases hi : k.val < r
  · left
    refine ⟨⟨k.val, hi⟩, ?_⟩
    ext
    rfl
  · right
    refine ⟨⟨k.val - r, by have := k.isLt; omega⟩, ?_⟩
    ext
    change r + (i.val - r) = i.val
    have hkr : r ≤ i.val := by simpa [k] using (show r ≤ k.val by omega)
    omega

/-- The row restriction is bijective, with inverse given by appending the two
blocks and transporting their row index. -/
theorem standardRowSplitMap_bijective (h : r + a = c + 1) (e : ℤ) :
    Function.Bijective (standardRowSplitMap (K := K) (n := n) h e) := by
  constructor
  · intro v w hvw
    funext i
    apply Subtype.ext
    rcases row_cases h i with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact congrArg (fun q => (q.1 j).val) hvw
    · exact congrArg (fun q => (q.2 j).val) hvw
  · rintro ⟨v, w⟩
    let f : Fin (c + 1) → Poly K n := fun i =>
      Fin.addCases (fun j => (v j).val) (fun j => (w j).val) (Fin.cast h.symm i)
    have hf (i : Fin (c + 1)) : f i ∈ signedForms K n (e - 2 + standardRowDegrees r c i) := by
      rcases row_cases h i with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [quadratic_row_shift]
        simp [f, quadraticRow]
      · rw [linear_row_shift]
        simp [f, linearRow]
    refine ⟨fun i => ⟨f i, hf i⟩, ?_⟩
    apply Prod.ext
    · funext i
      apply Subtype.ext
      simp [standardRowSplitMap, f, quadraticRow]
    · funext i
      apply Subtype.ext
      simp [standardRowSplitMap, f, linearRow]

/-- The explicitly constructed splitting of the graded free middle term. -/
def standardRowSplitEquiv (h : r + a = c + 1) (e : ℤ) :
    rowForms K n (standardRowDegrees r c) (e - 2) ≃ₗ[K]
      (Fin r → signedForms K n e) × (Fin a → signedForms K n (e - 1)) :=
  LinearEquiv.ofBijective (standardRowSplitMap h e) (standardRowSplitMap_bijective h e)

/-- The actual graded ideal piece, realized as the image of the cofactor map. -/
def rowCofactorImage
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) : Type _ :=
  (gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)).range

instance rowCofactorImageAddCommGroup
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    AddCommGroup (rowCofactorImage (r := r) B hB e) := by
  unfold rowCofactorImage
  infer_instance

instance rowCofactorImageModule
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    Module K (rowCofactorImage (r := r) B hB e) := by
  unfold rowCofactorImage
  infer_instance

instance rowCofactorImageFinite
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    Module.Finite K (rowCofactorImage (r := r) B hB e) := by
  unfold rowCofactorImage
  infer_instance

/-- The cofactor surjection after the explicit quadratic/linear row splitting. -/
def splitCofactorMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    (Fin r → signedForms K n e) × (Fin a → signedForms K n (e - 1)) →ₗ[K]
      rowCofactorImage (r := r) B hB e :=
  (gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)).rangeRestrict.comp
    (standardRowSplitEquiv h e).symm.toLinearMap

/-- The relation map after the same explicit row splitting. -/
def splitRelationMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    (Fin c → signedForms K n (e - 2)) →ₗ[K]
      (Fin r → signedForms K n e) × (Fin a → signedForms K n (e - 1)) :=
  (standardRowSplitEquiv h e).toLinearMap.comp
    (gradedMatrixMap B (standardRowDegrees r c) hB (e - 2))

/-- The split map is an actual presentation of the actual ideal piece. -/
theorem splitCofactorMap_surjective
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    Function.Surjective (splitCofactorMap B h hB e) := by
  intro y
  obtain ⟨v, hv⟩ := y.property
  refine ⟨standardRowSplitEquiv h e v, ?_⟩
  apply Subtype.ext
  change gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)
    ((standardRowSplitEquiv h e).symm (standardRowSplitEquiv h e v)) = y.val
  simpa only [LinearEquiv.symm_apply_apply] using hv

/-- Genuine exactness survives the explicit row splitting. -/
theorem splitCofactorMap_ker
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (splitCofactorMap B h hB e).ker = (splitRelationMap B h hB e).range := by
  ext v
  constructor
  · intro hv
    have hker : (standardRowSplitEquiv h e).symm v ∈
        (gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)).ker := by
      exact congrArg Subtype.val hv
    rw [graded_ker_cofactor_eq_range B (standardRowDegrees r c) hB hprimitive] at hker
    obtain ⟨w, hw⟩ := hker
    refine ⟨w, ?_⟩
    apply (standardRowSplitEquiv h e).symm.injective
    simpa [splitRelationMap] using hw
  · rintro ⟨w, rfl⟩
    apply Subtype.ext
    have hzero : gradedMatrixMap B (standardRowDegrees r c) hB (e - 2) w ∈
        (gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)).ker := by
      rw [graded_ker_cofactor_eq_range B (standardRowDegrees r c) hB hprimitive]
      exact ⟨w, rfl⟩
    change gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)
      ((standardRowSplitEquiv h e).symm
        (standardRowSplitEquiv h e (gradedMatrixMap B (standardRowDegrees r c) hB (e - 2) w))) = 0
    simpa only [LinearEquiv.symm_apply_apply, LinearMap.mem_ker] using hzero

/-- The projected relations are exactly multiplication by the bottom linear block. -/
def rowLinearBlockMap
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    (Fin c → signedForms K n (e - 2)) →ₗ[K] (Fin a → signedForms K n (e - 1)) :=
  (LinearMap.snd K _ _).comp (splitRelationMap B h hB e)

@[simp] theorem rowLinearBlockMap_val
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (e : ℤ) (w : Fin c → signedForms K n (e - 2)) (i : Fin a) :
    (rowLinearBlockMap B h hB e w i).val = ∑ j, B (linearRow h i) j * (w j).val := rfl

/-- A presentation quotient with its ambient module structure fixed. -/
abbrev linearMapChoppedQuotient {V W M : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup M] [Module K M] (φ : V × W →ₗ[K] M) :=
  M ⧸ choppedSubmodule φ

/-- Killing the quadratic-row generators leaves precisely the cokernel of
the actual bottom linear block. This is equation (4.5), in every signed degree. -/
def rowChopQuotientEquivLinearCokernel
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ) :
    (linearMapChoppedQuotient (K := K) (V := Fin r → signedForms K n e) (W := Fin a → signedForms K n (e - 1)) (M := rowCofactorImage (r := r) B hB e) (splitCofactorMap B h hB e)) ≃ₗ[K]
      ((Fin a → signedForms K n (e - 1)) ⧸ (rowLinearBlockMap B h hB e).range) :=
  choppedQuotientEquiv (K := K) (E := Fin c → signedForms K n (e - 2)) (V := Fin r → signedForms K n e) (W := Fin a → signedForms K n (e - 1)) (M := rowCofactorImage (r := r) B hB e) (splitRelationMap B h hB e) (splitCofactorMap B h hB e)
    (splitCofactorMap_surjective B h hB e) (splitCofactorMap_ker B h hB hprimitive e)

/-- The dimension of the genuine linear-block cokernel after killing the
quadratic cofactor generators. -/
theorem rowChopQuotient_finrank_of_maximalRank
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B) (e : ℤ)
    (hmax : finrank K (rowLinearBlockMap B h hB e).range =
      min (finrank K (Fin c → signedForms K 3 (e - 2)))
        (finrank K (Fin a → signedForms K 3 (e - 1)))) :
    (finrank K (linearMapChoppedQuotient (K := K) (V := Fin r → signedForms K 3 e) (W := Fin a → signedForms K 3 (e - 1)) (M := rowCofactorImage (r := r) B hB e) (splitCofactorMap B h hB e)) : ℤ) =
      max ((a : ℤ) * N₂ (e - 1) - (c : ℤ) * N₂ (e - 2)) 0 := by
  rw [(rowChopQuotientEquivLinearCokernel B h hB hprimitive e).finrank_eq, Submodule.finrank_quotient, hmax]
  have hnat : ∀ n m : ℕ, ((n - min m n : ℕ) : ℤ) = max ((n : ℤ) - m) 0 := by
    intro n m
    have heq : n - min m n = n - m := by omega
    rw [heq]
    have hcast := cast_max_sub 0 n m
    simpa only [max_eq_right (Nat.zero_le (n - m)), Nat.cast_zero, max_comm] using hcast
  rw [hnat]
  have hdim (k : ℕ) (t : ℤ) : (finrank K (Fin k → signedForms K 3 t) : ℤ) = (k : ℤ) * N₂ t := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_signedPlaneForms]
  rw [hdim, hdim]


/-- Sum over all rows as the sums over the two explicit blocks. -/
theorem sum_standard_rows {M : Type*} [AddCommMonoid M]
    (h : r + a = c + 1) (f : Fin (c + 1) → M) :
    (∑ i, f i) = (∑ i : Fin r, f (quadraticRow h i)) +
      ∑ i : Fin a, f (linearRow h i) := by
  calc
    (∑ i, f i) = ∑ i : Fin (r + a), f (Fin.cast h i) := (Fin.sum_congr' f h).symm
    _ = _ := Fin.sum_univ_add _

theorem sum_standardRowDegrees (h : r + a = c + 1) :
    ∑ i, standardRowDegrees r c i = 2 * r + a := by
  rw [sum_standard_rows h]
  simp
  omega

/-- The actual homogeneous cofactor generators of the quadratic-row chop. -/
def quadraticMinorSpace
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1) :
    Submodule K (Poly K n) :=
  Submodule.span K (Set.range (fun i : Fin r => signedMaximalMinor B (quadraticRow h i)))

/-- The actual ideal generated by those quadratic-row cofactors. -/
def quadraticMinorIdeal
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1) : Ideal (Poly K n) :=
  Ideal.span (Set.range (fun i : Fin r => signedMaximalMinor B (quadraticRow h i)))

theorem quadraticMinorSpace_idealSpan
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1) :
    Ideal.span (quadraticMinorSpace B h : Set (Poly K n)) = quadraticMinorIdeal B h :=
  Submodule.span_span_of_tower K (Poly K n) _

theorem quadraticMinorIdeal_le_maximalMinorIdeal
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1) :
    quadraticMinorIdeal B h ≤ maximalMinorIdeal B := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Ideal.subset_span ⟨quadraticRow h i, rfl⟩

theorem quadraticMinor_homogeneous
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (i : Fin r) :
    (signedMaximalMinor B (quadraticRow h i)).IsHomogeneous d := by
  simpa [hdegree] using
    signedMaximalMinor_homogeneous_total B (standardRowDegrees r c) hB (quadraticRow h i)

theorem quadraticMinorSpace_homogeneous
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) :
    quadraticMinorSpace B h ≤ Forms K n d := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact quadraticMinor_homogeneous B h hB hdegree i

/-- A coefficient vector supported in the quadratic block maps to precisely
its polynomial combination of the quadratic cofactors. -/
theorem splitCofactorMap_quadratic_val
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (e : ℤ) (v : Fin r → signedForms K n e) :
    (splitCofactorMap B h hB e (v, 0)).val.val =
      ∑ i : Fin r, signedMaximalMinor B (quadraticRow h i) * (v i).val := by
  let E := standardRowSplitEquiv (K := K) (n := n) h e
  have htop (i : Fin r) : ((E.symm (v, 0)) (quadraticRow h i)).val = (v i).val :=
    congrArg (fun q => (q.1 i).val) (E.apply_symm_apply (v, 0))
  have hbottom (i : Fin a) : ((E.symm (v, 0)) (linearRow h i)).val = 0 :=
    congrArg (fun q => (q.2 i).val) (E.apply_symm_apply (v, 0))
  change cofactorMap B (rowFormsVal (E.symm (v, 0))) = _
  rw [cofactorMap_apply, sum_standard_rows h]
  simp only [rowFormsVal, LinearMap.coe_mk, AddHom.coe_mk, htop, hbottom,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- An arbitrary finite polynomial combination. -/
def finitePolynomialCombination {q : ℕ} (g : Fin q → Poly K n) :
    (Fin q → Poly K n) →ₗ[Poly K n] Poly K n where
  toFun v := ∑ i, g i * v i
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' s v := by simp [Finset.mul_sum, mul_left_comm]

@[simp] theorem finitePolynomialCombination_apply {q : ℕ}
    (g : Fin q → Poly K n) (v : Fin q → Poly K n) :
    finitePolynomialCombination g v = ∑ i, g i * v i := rfl

theorem finitePolynomialCombination_range {q : ℕ} (g : Fin q → Poly K n) :
    (finitePolynomialCombination g).range = Ideal.span (Set.range g) := by
  apply le_antisymm
  · rintro f ⟨v, rfl⟩
    change (∑ i, g i * v i) ∈ Ideal.span (Set.range g)
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [Pi.single_apply]

/-- The submodule killed in the split presentation is exactly the actual
quadratic-minor ideal piece. This identifies the chop, not only its dimension. -/
theorem mem_rowChoppedSubmodule_iff
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2)
    (e : ℤ) (f : rowCofactorImage (r := r) B hB e) :
    f ∈ choppedSubmodule (K := K) (M := rowCofactorImage (r := r) B hB e) (splitCofactorMap B h hB e) ↔
      f.val.val ∈ quadraticMinorIdeal B h := by
  constructor
  · rintro ⟨v, hv⟩
    change splitCofactorMap B h hB e (v, 0) = f at hv
    have hpoly := congrArg (fun q : rowCofactorImage (r := r) B hB e => q.val.val) hv
    rw [splitCofactorMap_quadratic_val] at hpoly
    rw [← hpoly]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · intro hf
    let g : Fin r → Poly K n := fun i => signedMaximalMinor B (quadraticRow h i)
    have hfcomb : f.val.val ∈ (finitePolynomialCombination g).range := by
      rw [finitePolynomialCombination_range]
      exact hf
    obtain ⟨v, hv⟩ := hfcomb
    have hproj : (∑ i, g i * signedComponent e (v i)) = f.val.val := by
      have ht : e - 2 + (∑ i, standardRowDegrees r c i : ℕ) = e + (d : ℤ) := by
        rw [hdegree]
        push_cast
        ring
      calc
        (∑ i, g i * signedComponent e (v i)) =
            signedComponent (e + d) (finitePolynomialCombination g v) := by
          simp only [finitePolynomialCombination_apply, map_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact (signedComponent_mul_form e (g i) (v i)
            (quadraticMinor_homogeneous B h hB hdegree i)).symm
        _ = signedComponent (e + d) f.val.val := by rw [hv]
        _ = f.val.val := by
          rw [← ht]
          exact signedComponent_self _ f.val
    let w : Fin r → signedForms K n e := fun i => ⟨signedComponent e (v i), signedComponent_mem _ _⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    change (splitCofactorMap B h hB e (w, 0)).val.val = f.val.val
    rw [splitCofactorMap_quadratic_val]
    exact hproj

/-- The actual cofactor image is the actual maximal-minor ideal piece. -/
def rowCofactorImageEquivSignedIdeal
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ) :
    rowCofactorImage (r := r) B hB e ≃ₗ[K]
      signedIdealPiece (maximalMinorIdeal B) (e - 2 + ∑ i, standardRowDegrees r c i) where
  toFun f := ⟨f.val, by
    change f.val ∈ gradedMinorIdealPiece B (standardRowDegrees r c) (e - 2)
    rw [← gradedCofactorMap_range_eq_idealPiece B (standardRowDegrees r c) hB]
    exact f.property⟩
  invFun f := ⟨f.val, by
    change f.val ∈ (gradedCofactorMap B (standardRowDegrees r c) hB (e - 2)).range
    rw [gradedCofactorMap_range_eq_idealPiece B (standardRowDegrees r c) hB]
    exact f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The cofactor-piece comparison preserves the polynomial representative. -/
@[simp] theorem rowCofactorImageEquivSignedIdeal_val
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n))
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i)) (e : ℤ)
    (f : rowCofactorImage (r := r) B hB e) :
    (rowCofactorImageEquivSignedIdeal B hB e f).val.val = f.val.val := rfl

/-- Under the genuine cofactor identification, the killed submodule is the
intersection with the quadratic-minor ideal. -/
theorem rowCofactorImageEquivSignedIdeal_map_chopped
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℤ) :
    (choppedSubmodule (K := K) (M := rowCofactorImage (r := r) B hB e)
      (splitCofactorMap B h hB e)).map
        (rowCofactorImageEquivSignedIdeal B hB e).toLinearMap =
      (signedIdealPiece (quadraticMinorIdeal B h)
        (e - 2 + ∑ i, standardRowDegrees r c i)).comap
          (signedIdealPiece (maximalMinorIdeal B)
            (e - 2 + ∑ i, standardRowDegrees r c i)).subtype := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (mem_rowChoppedSubmodule_iff B h hB hdegree e g).mp hg
  · intro hf
    let g := (rowCofactorImageEquivSignedIdeal B hB e).symm f
    refine ⟨g, ?_, (rowCofactorImageEquivSignedIdeal B hB e).apply_symm_apply f⟩
    exact (mem_rowChoppedSubmodule_iff B h hB hdegree e g).mpr hf

/-- The quotient of the actual maximal-minor ideal by its actual quadratic
chop is the cokernel of the actual bottom linear block. -/
def rowIdealResidualEquivLinearCokernel
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℤ) :
    signedIdealResidualPiece (quadraticMinorIdeal B h) (maximalMinorIdeal B)
      (e - 2 + ∑ i, standardRowDegrees r c i) ≃ₗ[K]
      ((Fin a → signedForms K n (e - 1)) ⧸ (rowLinearBlockMap B h hB e).range) :=
  (Submodule.Quotient.equiv
    (choppedSubmodule (K := K) (M := rowCofactorImage (r := r) B hB e) (splitCofactorMap B h hB e))
    _ (rowCofactorImageEquivSignedIdeal B hB e)
    (rowCofactorImageEquivSignedIdeal_map_chopped B h hB hdegree e)).symm.trans
      (rowChopQuotientEquivLinearCokernel B h hB hprimitive e)

/-- The same actual residual identification, now in ordinary degree `d+e`. -/
def rowIdealResidualNatEquivLinearCokernel
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K n)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℕ) :
    idealResidualPiece (quadraticMinorIdeal B h) (maximalMinorIdeal B) (d + e) ≃ₗ[K]
      ((Fin a → signedForms K n ((e : ℤ) - 1)) ⧸
        (rowLinearBlockMap B h hB e).range) := by
  have ht : (e : ℤ) - 2 + (∑ i, standardRowDegrees r c i : ℕ) = ((d + e : ℕ) : ℤ) := by
    rw [hdegree]
    push_cast
    ring
  exact (signedIdealResidualPieceEquivNatOfEq (quadraticMinorIdeal B h)
    (maximalMinorIdeal B) (d + e) ht).symm.trans
      (rowIdealResidualEquivLinearCokernel B h hB hprimitive hdegree e)

/-- Maximal rank of the genuine bottom block computes the genuine residual
ideal dimension in ordinary degree `d+e`. -/
theorem rowIdealResidual_finrank_of_maximalRank
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℕ)
    (hmax : finrank K (rowLinearBlockMap B h hB e).range =
      min (finrank K (Fin c → signedForms K 3 ((e : ℤ) - 2)))
        (finrank K (Fin a → signedForms K 3 ((e : ℤ) - 1)))) :
    (finrank K (idealResidualPiece (quadraticMinorIdeal B h)
      (maximalMinorIdeal B) (d + e)) : ℤ) =
      max ((a : ℤ) * N₂ ((e : ℤ) - 1) - (c : ℤ) * N₂ ((e : ℤ) - 2)) 0 := by
  rw [(rowIdealResidualNatEquivLinearCokernel B h hB hprimitive hdegree e).finrank_eq,
    Submodule.finrank_quotient, hmax]
  have hnat : ∀ n m : ℕ, ((n - min m n : ℕ) : ℤ) = max ((n : ℤ) - m) 0 := by
    intro n m
    have heq : n - min m n = n - m := by omega
    rw [heq]
    have hcast := cast_max_sub 0 n m
    simpa only [max_eq_right (Nat.zero_le (n - m)), Nat.cast_zero, max_comm] using hcast
  rw [hnat]
  have hdim (k : ℕ) (t : ℤ) : (finrank K (Fin k → signedForms K 3 t) : ℤ) = (k : ℤ) * N₂ t := by
    rw [Module.finrank_pi_fintype]
    simp [finrank_signedPlaneForms]
  rw [hdim, hdim]

/-- The Hilbert function of the actual quadratic-row chop equals the Hilbert
function of the actual maximal-minor ideal plus the maximal-rank residual. -/
theorem rowQuadraticChop_hilbertFunction
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℕ)
    (hmax : finrank K (rowLinearBlockMap B h hB e).range =
      min (finrank K (Fin c → signedForms K 3 ((e : ℤ) - 2)))
        (finrank K (Fin a → signedForms K 3 ((e : ℤ) - 1)))) :
    (idealQuotientHilbertFunction (quadraticMinorIdeal B h) (d + e) : ℤ) =
      (idealQuotientHilbertFunction (maximalMinorIdeal B) (d + e) : ℤ) +
      max ((a : ℤ) * N₂ ((e : ℤ) - 1) - (c : ℤ) * N₂ ((e : ℤ) - 2)) 0 := by
  rw [idealQuotientHilbertFunction_eq_add_residual_int _ _
    (quadraticMinorIdeal_le_maximalMinorIdeal B h)]
  rw [rowIdealResidual_finrank_of_maximalRank B h hB hprimitive hdegree e hmax]

/-- The genuine row profile forces precisely the paper's two row counts. -/
theorem standardRowProfile_counts (h : r + a = c + 1)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) :
    (a : ℤ) = aCount d r ∧ (c : ℤ) = cCount d r := by
  have hdeg : 2 * r + a = d + 2 := by
    rw [← sum_standardRowDegrees h]
    exact hdegree
  dsimp [aCount, cCount]
  omega

/-- The maximal-rank actual residual ideal dimension, expressed in the paper's
single residual polynomial. The row profile itself supplies the counts. -/
theorem rowIdealResidual_finrank_eq_residual
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℕ)
    (hmax : finrank K (rowLinearBlockMap B h hB e).range =
      min (finrank K (Fin c → signedForms K 3 ((e : ℤ) - 2)))
        (finrank K (Fin a → signedForms K 3 ((e : ℤ) - 1)))) :
    (finrank K (idealResidualPiece (quadraticMinorIdeal B h)
      (maximalMinorIdeal B) (d + e)) : ℤ) = max (residual d r e) 0 := by
  rw [rowIdealResidual_finrank_of_maximalRank B h hB hprimitive hdegree e hmax]
  obtain ⟨ha, hc⟩ := standardRowProfile_counts h hdegree
  rw [ha, hc, block_dimension_identity]

/-- The actual row chop's Hilbert function, with its correction term in the
paper's residual-polynomial notation. -/
theorem rowQuadraticChop_hilbertFunction_residual
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 3)) (h : r + a = c + 1)
    (hB : ∀ i j, (B i j).IsHomogeneous (standardRowDegrees r c i))
    (hprimitive : PrimitiveMaximalMinors B)
    {d : ℕ} (hdegree : ∑ i, standardRowDegrees r c i = d + 2) (e : ℕ)
    (hmax : finrank K (rowLinearBlockMap B h hB e).range =
      min (finrank K (Fin c → signedForms K 3 ((e : ℤ) - 2)))
        (finrank K (Fin a → signedForms K 3 ((e : ℤ) - 1)))) :
    (idealQuotientHilbertFunction (quadraticMinorIdeal B h) (d + e) : ℤ) =
      (idealQuotientHilbertFunction (maximalMinorIdeal B) (d + e) : ℤ) +
      max (residual d r e) 0 := by
  rw [rowQuadraticChop_hilbertFunction B h hB hprimitive hdegree e hmax]
  obtain ⟨ha, hc⟩ := standardRowProfile_counts h hdegree
  rw [ha, hc, block_dimension_identity]

end ChoppedPlane
