module

public import Mathlib

@[expose] public section

/-!
# Binary Laurent quotients and their graded residue pairing

The two affine-chart subspaces have nonnegative second or first exponent.
Their quotient is represented by the monomials with both exponents negative.
Complementing exponents by `(-1-a,-1-b)` identifies every finite graded free
component with the dual of the corresponding binary polynomial component.
-/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
variable {K : Type*} [Field K]

abbrev BinaryLaurent (K : Type*) [Field K] := AddMonoidAlgebra K (ℤ × ℤ)

def negativeExponents : Set (ℤ × ℤ) := {e | e.1 < 0 ∧ e.2 < 0}

def chartU : Submodule K (BinaryLaurent K) :=
  AddMonoidAlgebra.supported K K {e | 0 ≤ e.2}

def chartV : Submodule K (BinaryLaurent K) :=
  AddMonoidAlgebra.supported K K {e | 0 ≤ e.1}

def negativeSpace : Submodule K (BinaryLaurent K) :=
  AddMonoidAlgebra.supported K K negativeExponents

/-- Project a Laurent polynomial onto its strictly negative monomials. -/
def negativePart : BinaryLaurent K →ₗ[K] BinaryLaurent K := by
  classical
  exact (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    (((Finsupp.supported K K negativeExponents).subtype.comp
      (Finsupp.restrictDom K K negativeExponents)).comp
      (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

@[simp] theorem negativePart_coeff (p : BinaryLaurent K) (e : ℤ × ℤ) :
    (negativePart p).coeff e = if e.1 < 0 ∧ e.2 < 0 then p.coeff e else 0 := by
  classical
  change (p.coeff.filter (· ∈ negativeExponents)) e = _
  by_cases he : e.1 < 0 ∧ e.2 < 0 <;>
    simp [Finsupp.filter, negativeExponents, he]

theorem negativePart_mem (p : BinaryLaurent K) : negativePart p ∈ negativeSpace := by
  apply AddMonoidAlgebra.mem_supported'.mpr
  intro e he
  rw [negativePart_coeff]
  exact ite_eq_right he

theorem negativePart_eq_self {p : BinaryLaurent K} (hp : p ∈ negativeSpace) :
    negativePart p = p := by
  ext e
  by_cases he : e.1 < 0 ∧ e.2 < 0
  · simp [he]
  · have hz := AddMonoidAlgebra.mem_supported'.mp hp e he
    simp [he, hz]

/-- The two chart subspaces cover exactly the monomials surviving neither
strictly negative exponent condition. -/
theorem chart_sup_eq_supported :
    (chartU (K := K)) ⊔ chartV =
      AddMonoidAlgebra.supported K K {e : ℤ × ℤ | 0 ≤ e.2 ∨ 0 ≤ e.1} := by
  simp only [chartU, chartV, AddMonoidAlgebra.supported_eq_map,
    ← Submodule.map_sup, ← Finsupp.supported_union]
  rfl

/-- The kernel of negative projection is the sum of the two actual charts. -/
theorem ker_negativePart : LinearMap.ker (negativePart (K := K)) = chartU ⊔ chartV := by
  rw [chart_sup_eq_supported]
  ext p
  rw [LinearMap.mem_ker, AddMonoidAlgebra.mem_supported']
  constructor
  · intro hp e he
    have he' : e.1 < 0 ∧ e.2 < 0 := by change ¬(0 ≤ e.2 ∨ 0 ≤ e.1) at he; omega
    have hz := congrArg (fun q : BinaryLaurent K => q.coeff e) hp
    simpa [he'] using hz
  · intro hp
    ext e
    by_cases he : e.1 < 0 ∧ e.2 < 0
    · have he' : e ∉ {e : ℤ × ℤ | 0 ≤ e.2 ∨ 0 ≤ e.1} := by simp only [Set.mem_ofPred_eq]; omega
      simp [he, hp e he']
    · simp [he]

/-- Projection with its exact quotient-representative codomain. -/
def negativeProjection : BinaryLaurent K →ₗ[K] negativeSpace (K := K) :=
  (negativePart (K := K)).codRestrict (negativeSpace (K := K)) negativePart_mem

theorem negativeProjection_surjective : Function.Surjective (negativeProjection (K := K)) := by
  intro p
  refine ⟨p.val, Subtype.ext (negativePart_eq_self p.property)⟩

theorem ker_negativeProjection : LinearMap.ker (negativeProjection (K := K)) = chartU ⊔ chartV := by
  rw [← ker_negativePart]
  ext p
  change negativeProjection p = 0 ↔ negativePart p = 0
  exact Subtype.ext_iff

/-- The binary two-chart quotient is exactly its negative Laurent monomials. -/
def negativeQuotientEquiv : (BinaryLaurent K ⧸ (chartU (K := K) ⊔ chartV (K := K))) ≃ₗ[K] negativeSpace (K := K) :=
  (Submodule.quotEquivOfEq _ _ ker_negativeProjection.symm).trans
    ((negativeProjection (K := K)).quotKerEquivOfSurjective negativeProjection_surjective)

@[simp] theorem negativeQuotientEquiv_mk (p : BinaryLaurent K) :
    negativeQuotientEquiv ((chartU ⊔ chartV).mkQ p) = negativeProjection p := by
  simp [negativeQuotientEquiv]

/-- The genuine Laurent coordinate monomials. -/
def U : BinaryLaurent K := AddMonoidAlgebra.single (1, 0) 1
def V : BinaryLaurent K := AddMonoidAlgebra.single (0, 1) 1

variable {ι : Type*}

/-- Coefficient model of a free module of binary Laurent polynomials. -/
abbrev FreeLaurent (K : Type*) [Field K] (ι : Type*) := (ι × (ℤ × ℤ)) →₀ K

/-- The polynomial degree-`r` monomials with generator degrees `g`. -/
def positiveIndices (g : ι → ℤ) (r : ℤ) : Set (ι × (ℤ × ℤ)) :=
  {e | 0 ≤ e.2.1 ∧ 0 ≤ e.2.2 ∧ e.2.1 + e.2.2 + g e.1 = r}

/-- The degree-`-r` top quotient monomials with dual generator degrees `2-g`. -/
def negativeIndices (g : ι → ℤ) (r : ℤ) : Set (ι × (ℤ × ℤ)) :=
  {e | e.2.1 < 0 ∧ e.2.2 < 0 ∧ e.2.1 + e.2.2 + (2 - g e.1) = -r}

abbrev PositiveIndex (g : ι → ℤ) (r : ℤ) := positiveIndices g r
abbrev NegativeIndex (g : ι → ℤ) (r : ℤ) := negativeIndices g r

/-- Complementing Laurent exponents is the exact degree-preserving dual index. -/
def complementIndex (g : ι → ℤ) (r : ℤ) : PositiveIndex g r ≃ NegativeIndex g r where
  toFun e := ⟨(e.val.1, (-1 - e.val.2.1, -1 - e.val.2.2)), by
    obtain ⟨ha, hb, hab⟩ := e.property
    change (-1 - e.val.2.1) < 0 ∧ (-1 - e.val.2.2) < 0 ∧
      (-1 - e.val.2.1) + (-1 - e.val.2.2) + (2 - g e.val.1) = -r
    omega⟩
  invFun e := ⟨(e.val.1, (-1 - e.val.2.1, -1 - e.val.2.2)), by
    obtain ⟨ha, hb, hab⟩ := e.property
    change 0 ≤ (-1 - e.val.2.1) ∧ 0 ≤ (-1 - e.val.2.2) ∧
      (-1 - e.val.2.1) + (-1 - e.val.2.2) + g e.val.1 = r
    omega⟩
  left_inv e := by apply Subtype.ext; simp
  right_inv e := by apply Subtype.ext; simp

instance positiveIndexFinite [Finite ι] (g : ι → ℤ) (r : ℤ) : Finite (PositiveIndex g r) := by
  let f : PositiveIndex g r → Σ i : ι, Fin ((r - g i).toNat + 1) × Fin ((r - g i).toNat + 1) :=
    fun e => ⟨e.val.1, ⟨e.val.2.1.toNat, by
      obtain ⟨ha, hb, hab⟩ := e.property
      have ht : e.val.2.1 ≤ r - g e.val.1 := by omega
      have hn := Int.toNat_le_toNat ht
      omega⟩, ⟨e.val.2.2.toNat, by
      obtain ⟨ha, hb, hab⟩ := e.property
      have ht : e.val.2.2 ≤ r - g e.val.1 := by omega
      have hn := Int.toNat_le_toNat ht
      omega⟩⟩
  apply Finite.of_injective f
  intro a b hab
  apply Subtype.ext
  have hi : a.val.1 = b.val.1 := congrArg Sigma.fst hab
  have ha : a.val.2.1.toNat = b.val.2.1.toNat := by
    simpa using congrArg (fun z => z.snd.1.val) hab
  have hb : a.val.2.2.toNat = b.val.2.2.toNat := by
    simpa using congrArg (fun z => z.snd.2.val) hab
  obtain ⟨haa, hab', haeq⟩ := a.property
  obtain ⟨hba, hbb, hbeq⟩ := b.property
  have ha' : a.val.2.1 = b.val.2.1 := by omega
  have hb' : a.val.2.2 = b.val.2.2 := by omega
  exact Prod.ext hi (Prod.ext ha' hb')

instance negativeIndexFinite [Finite ι] (g : ι → ℤ) (r : ℤ) : Finite (NegativeIndex g r) :=
  Finite.of_equiv (PositiveIndex g r) (complementIndex g r)

/-- Actual supported free polynomial component. -/
def positiveGrade (g : ι → ℤ) (r : ℤ) : Submodule K (FreeLaurent K ι) :=
  Finsupp.supported K K (positiveIndices g r)

/-- Actual supported top Laurent quotient component. -/
def negativeGrade (g : ι → ℤ) (r : ℤ) : Submodule K (FreeLaurent K ι) :=
  Finsupp.supported K K (negativeIndices g r)

/-- Monomial coefficient coordinates on a positive component. -/
def positiveCoordinates (g : ι → ℤ) (r : ℤ) :
    positiveGrade (K := K) g r ≃ₗ[K] PositiveIndex g r →₀ K :=
  Finsupp.supportedEquivFinsupp (positiveIndices g r)

/-- Complementary monomial coefficient coordinates on a negative component. -/
def negativeCoordinates (g : ι → ℤ) (r : ℤ) :
    negativeGrade (K := K) g r ≃ₗ[K] PositiveIndex g r →₀ K := by
  classical
  exact (Finsupp.supportedEquivFinsupp (negativeIndices g r)).trans
    (Finsupp.domLCongr (complementIndex g r).symm)

/-- The positive monomial basis. -/
def positiveBasis (g : ι → ℤ) (r : ℤ) :
    Basis (PositiveIndex g r) K (positiveGrade (K := K) g r) := by
  classical
  exact Basis.ofRepr (positiveCoordinates g r)

/-- The perfect finite-degree residue pairing, including the `2-g` shifts. -/
def residueDualEquiv [Finite ι] (g : ι → ℤ) (r : ℤ) :
    negativeGrade (K := K) g r ≃ₗ[K] Module.Dual K (positiveGrade (K := K) g r) := by
  classical
  exact (negativeCoordinates g r).trans ((positiveCoordinates g r).symm.trans
    (positiveBasis g r).toDualEquiv)

/-- The residue pairing is a concrete bilinear form. -/
def residuePair [Finite ι] (g : ι → ℤ) (r : ℤ) :
    negativeGrade (K := K) g r →ₗ[K] positiveGrade (K := K) g r →ₗ[K] K :=
  (residueDualEquiv g r).toLinearMap


/-- The coefficient model is the genuine free Laurent module. -/
def freeLaurentEquiv [Finite ι] : FreeLaurent K ι ≃ₗ[K] (ι → BinaryLaurent K) := by
  classical
  exact (Finsupp.curryLinearEquiv K).trans
    ((Finsupp.linearEquivFunOnFinite K ((ℤ × ℤ) →₀ K) ι).trans
      (LinearEquiv.piCongrRight fun _ => (AddMonoidAlgebra.coeffLinearEquiv K).symm))

@[simp] theorem freeLaurentEquiv_coeff [Finite ι] (p : FreeLaurent K ι)
    (i : ι) (e : ℤ × ℤ) : (freeLaurentEquiv p i).coeff e = p (i, e) := rfl

@[simp] theorem positiveCoordinates_apply (g : ι → ℤ) (r : ℤ)
    (p : positiveGrade (K := K) g r) (e : PositiveIndex g r) :
    positiveCoordinates g r p e = p.val e.val := rfl

@[simp] theorem negativeCoordinates_apply (g : ι → ℤ) (r : ℤ)
    (p : negativeGrade (K := K) g r) (e : PositiveIndex g r) :
    negativeCoordinates g r p e = p.val (complementIndex g r e).val := rfl

@[simp] theorem positiveBasis_val (g : ι → ℤ) (r : ℤ) (e : PositiveIndex g r) :
    (positiveBasis (K := K) g r e).val = Finsupp.single e.val 1 := by
  classical
  exact Finsupp.supportedEquivFinsupp_symm_single (positiveIndices g r) e 1

/-- Residues on a polynomial monomial are exactly the complementary Laurent coefficient. -/
@[simp] theorem residuePair_basis [Finite ι] (g : ι → ℤ) (r : ℤ)
    (q : negativeGrade (K := K) g r) (e : PositiveIndex g r) :
    residuePair g r q (positiveBasis g r e) = q.val (complementIndex g r e).val := by
  classical
  change (positiveBasis g r).toDualEquiv
    ((positiveCoordinates g r).symm (negativeCoordinates g r q)) (positiveBasis g r e) = _
  rw [Basis.toDualEquiv_apply, Basis.toDual_apply_left]
  change positiveCoordinates g r ((positiveCoordinates g r).symm (negativeCoordinates g r q)) e = _
  rw [LinearEquiv.apply_symm_apply]
  exact negativeCoordinates_apply g r q e

/-- Translation of exponents, the coefficient action of a Laurent monomial. -/
def exponentTranslate (m : ℤ × ℤ) : (ι × (ℤ × ℤ)) ≃ (ι × (ℤ × ℤ)) where
  toFun e := (e.1, (e.2.1 + m.1, e.2.2 + m.2))
  invFun e := (e.1, (e.2.1 - m.1, e.2.2 - m.2))
  left_inv e := by simp
  right_inv e := by simp

def shift (m : ℤ × ℤ) : FreeLaurent K ι →ₗ[K] FreeLaurent K ι := by
  classical
  exact (Finsupp.domLCongr (exponentTranslate m)).toLinearMap

@[simp] theorem shift_apply (m : ℤ × ℤ) (p : FreeLaurent K ι) (i : ι) (e : ℤ × ℤ) :
    shift m p (i,e) = p (i,(e.1-m.1,e.2-m.2)) := rfl

/-- Project free Laurent coefficients to the negative quadrant. -/
def freeNegativePart : FreeLaurent K ι →ₗ[K] FreeLaurent K ι := by
  classical
  exact (Finsupp.supported K K {e : ι × (ℤ × ℤ) | e.2.1 < 0 ∧ e.2.2 < 0}).subtype.comp
    (Finsupp.restrictDom K K {e : ι × (ℤ × ℤ) | e.2.1 < 0 ∧ e.2.2 < 0})

@[simp] theorem freeNegativePart_apply (p : FreeLaurent K ι) (i : ι) (e : ℤ × ℤ) :
    freeNegativePart p (i,e) = if e.1 < 0 ∧ e.2 < 0 then p (i,e) else 0 := by
  classical
  change (p.filter (fun e => e.2.1 < 0 ∧ e.2.2 < 0)) (i,e) = _
  by_cases he : e.1 < 0 ∧ e.2 < 0 <;> simp [Finsupp.filter, he]

/-- Positive monomial translation between the actual polynomial components. -/
def positiveShift (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ) :
    positiveGrade (K := K) g r →ₗ[K] positiveGrade (K := K) g (r + m.1 + m.2) :=
  (shift (K := K) ((m.1 : ℤ), (m.2 : ℤ))).restrict
    (p := positiveGrade g r) (q := positiveGrade g (r + m.1 + m.2)) (by
      intro p hp
      apply (Finsupp.mem_supported' K _).mpr
      intro e he
      rw [shift_apply]
      apply (Finsupp.mem_supported' K p).mp hp
      intro h
      apply he
      obtain ⟨ha,hb,hab⟩ := h
      change 0 ≤ e.2.1 ∧ 0 ≤ e.2.2 ∧ e.2.1 + e.2.2 + g e.1 = r + m.1 + m.2
      change 0 ≤ e.2.1 - (m.1 : ℤ) at ha
      change 0 ≤ e.2.2 - (m.2 : ℤ) at hb
      change (e.2.1 - (m.1 : ℤ)) + (e.2.2 - (m.2 : ℤ)) + g e.1 = r at hab
      omega)

/-- Multiplication followed by the actual negative Laurent projection. -/
def negativeShift (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ) :
    negativeGrade (K := K) g (r + m.1 + m.2) →ₗ[K] negativeGrade (K := K) g r :=
  (freeNegativePart.comp (shift (K := K) ((m.1 : ℤ),(m.2 : ℤ)))).restrict
    (p := negativeGrade g (r + m.1 + m.2)) (q := negativeGrade g r) (by
      intro p hp
      apply (Finsupp.mem_supported' K _).mpr
      intro e he
      rw [LinearMap.comp_apply, freeNegativePart_apply]
      split_ifs with hneg
      · rw [shift_apply]
        apply (Finsupp.mem_supported' K p).mp hp
        intro h
        apply he
        obtain ⟨ha,hb,hab⟩ := h
        change e.2.1 < 0 ∧ e.2.2 < 0 ∧ e.2.1 + e.2.2 + (2-g e.1) = -r
        change (e.2.1 - (m.1 : ℤ)) + (e.2.2 - (m.2 : ℤ)) + (2-g e.1) = -(r + m.1 + m.2) at hab
        exact ⟨hneg.1,hneg.2, by omega⟩
      · rfl)

@[simp] theorem positiveShift_apply (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (p : positiveGrade (K := K) g r) (i : ι) (e : ℤ × ℤ) :
    (positiveShift g r m p).val (i,e) = p.val (i,(e.1-m.1,e.2-m.2)) := rfl

@[simp] theorem negativeShift_apply (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (p : negativeGrade (K := K) g (r+m.1+m.2)) (i : ι) (e : ℤ × ℤ) :
    (negativeShift g r m p).val (i,e) =
      if e.1 < 0 ∧ e.2 < 0 then p.val (i,(e.1-m.1,e.2-m.2)) else 0 := by
  exact freeNegativePart_apply _ i e

def positiveIndexShift (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (e : PositiveIndex g r) : PositiveIndex g (r + m.1 + m.2) :=
  ⟨(e.val.1,(e.val.2.1+m.1,e.val.2.2+m.2)), by
    obtain ⟨ha,hb,hab⟩ := e.property
    change 0 ≤ e.val.2.1 + (m.1 : ℤ) ∧ 0 ≤ e.val.2.2 + (m.2 : ℤ) ∧
      (e.val.2.1 + (m.1 : ℤ)) + (e.val.2.2 + (m.2 : ℤ)) + g e.val.1 = r + m.1 + m.2
    omega⟩

@[simp] theorem positiveShift_basis (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (e : PositiveIndex g r) :
    positiveShift g r m (positiveBasis (K := K) g r e) =
      positiveBasis g (r+m.1+m.2) (positiveIndexShift g r m e) := by
  classical
  apply Subtype.ext
  change shift _ (positiveBasis g r e).val = _
  rw [positiveBasis_val, positiveBasis_val]
  exact Finsupp.domLCongr_single (exponentTranslate _) e.val 1

/-- Polynomial monomial multiplication and projected Laurent multiplication are adjoint. -/
theorem residuePair_shift [Finite ι] (g : ι → ℤ) (r : ℤ) (m : ℕ × ℕ)
    (q : negativeGrade (K := K) g (r+m.1+m.2)) (p : positiveGrade (K := K) g r) :
    residuePair g (r+m.1+m.2) q (positiveShift g r m p) =
      residuePair g r (negativeShift g r m q) p := by
  have h : (residuePair g (r+m.1+m.2) q).comp (positiveShift g r m) =
      residuePair g r (negativeShift g r m q) := by
    apply (positiveBasis g r).ext
    intro e
    rw [LinearMap.comp_apply, positiveShift_basis, residuePair_basis, residuePair_basis,
      negativeShift_apply]
    have hn : -1 - e.val.2.1 < 0 ∧ -1 - e.val.2.2 < 0 := by
      obtain ⟨ha,hb,hab⟩ := e.property
      omega
    change q.val (e.val.1,(-1-(e.val.2.1+m.1),-1-(e.val.2.2+m.2))) =
      if -1-e.val.2.1 < 0 ∧ -1-e.val.2.2 < 0 then
        q.val (e.val.1,((-1-e.val.2.1)-m.1,(-1-e.val.2.2)-m.2)) else 0
    rw [ite_eq_left hn]
    exact congrArg (fun z : ℤ × ℤ => q.val (e.val.1,z))
      (Prod.ext (by omega) (by omega))
  exact LinearMap.congr_fun h p

end ChoppedPlane.LaurentPairing
