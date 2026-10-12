module

public import ChoppedPlane.LaurentWeightedPairing
public import ChoppedPlane.QWeylModule

@[expose] public section

/-!
The finite graded residue pairing is the literal coefficient of `u⁻¹v⁻¹`
in the product of Laurent representatives. Consequently the actual cyclic
cubic action and its literal transpose are adjoint, also when the auxiliary
monomials supply a common factorial weight.
-/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
open scoped Classical
variable {K : Type*} [Field K] {ι : Type*}

/-- Read the literal `u⁻¹v⁻¹` Laurent coefficient. -/
def residueCoefficient : BinaryLaurent K →ₗ[K] K :=
  (Finsupp.lapply (-1,-1)).comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem residueCoefficient_apply (p : BinaryLaurent K) :
    residueCoefficient p = p.coeff (-1,-1) := rfl

/-- The actual weighted Laurent product residue, linear in the positive
representative for each fixed negative representative. -/
def vectorResidueFunctional [Finite ι] (w : ι → K) (q : ι → BinaryLaurent K) :
    (ι → BinaryLaurent K) →ₗ[K] K := by
  classical
  letI := Fintype.ofFinite ι
  exact ∑ i, w i • ((residueCoefficient (K := K)).comp
    ((LinearMap.mulLeft K (q i)).comp (LinearMap.proj i)))

theorem vectorResidueFunctional_apply [Fintype ι] (w : ι → K)
    (q p : ι → BinaryLaurent K) :
    vectorResidueFunctional w q p =
      ∑ i : ι, w i * (q i * p i).coeff (-1,-1) := by
  classical
  unfold vectorResidueFunctional
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearMap.mulLeft_apply, residueCoefficient_apply, smul_eq_mul]
  apply Finset.sum_congr
  · ext i
    simp
  · intro i hi
    rfl

/-- A positive coefficient basis vector is its literal Laurent monomial in
one component of the actual free Laurent module. -/
theorem freeLaurentEquiv_positiveBasis [Finite ι] (g : ι → ℤ) (r : ℤ)
    (e : PositiveIndex g r) (i : ι) :
    freeLaurentEquiv (positiveBasis (K := K) g r e).val i =
      if e.val.1 = i then AddMonoidAlgebra.single e.val.2 1 else 0 := by
  classical
  by_cases hi : e.val.1 = i
  · subst i
    ext z
    simp [positiveBasis_val, Finsupp.single_apply, Prod.ext_iff]
  · ext z
    simp [positiveBasis_val, Finsupp.single_apply, Prod.ext_iff, hi]

/-- The literal product residue agrees with the weighted complementary
coefficient on every actual polynomial basis monomial. -/
theorem vectorResidueFunctional_basis [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (q : negativeGrade (K := K) g r) (e : PositiveIndex g r) :
    vectorResidueFunctional w (freeLaurentEquiv q.val)
      (freeLaurentEquiv (positiveBasis g r e).val) =
      w e.val.1 * q.val (complementIndex g r e).val := by
  classical
  letI := Fintype.ofFinite ι
  rw [vectorResidueFunctional_apply]
  simp only [freeLaurentEquiv_positiveBasis]
  rw [Finset.sum_eq_single e.val.1]
  · simp [AddMonoidAlgebra.coeff_mul_single_apply, complementIndex]
    left
    exact congrArg (fun z : ℤ × ℤ => q.val (e.val.1,z))
      (Prod.ext (by simp [sub_eq_add_neg]) (by simp [sub_eq_add_neg]))
  · intro i hi hne
    simp [Ne.symm hne]
  · simp

/-- The perfect finite pairing is literally residue of the Laurent product. -/
theorem weightedResiduePair_eq_vectorResidue [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (hw : ∀ i, w i ≠ 0)
    (q : negativeGrade (K := K) g r) (p : positiveGrade (K := K) g r) :
    weightedResiduePair g r w hw q p =
      vectorResidueFunctional w (freeLaurentEquiv q.val) (freeLaurentEquiv p.val) := by
  have h : weightedResiduePair g r w hw q =
      (vectorResidueFunctional w (freeLaurentEquiv q.val)).comp
        ((freeLaurentEquiv (K := K)).toLinearMap.comp (positiveGrade g r).subtype) := by
    apply (positiveBasis g r).ext
    intro e
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, weightedResiduePair_basis, vectorResidueFunctional_basis]
  exact LinearMap.congr_fun h p

/-- Actual Laurent cyclic multiplication and its literal transpose have the
same residue, including any common coefficient weight. -/
theorem vectorResidueFunctional_cyclic_transpose (c : K)
    (γ m q : Fin 3 → BinaryLaurent K) :
    vectorResidueFunctional (fun _ : Fin 3 => c) q (QWeyl.cyclicZ γ m) =
      vectorResidueFunctional (fun _ : Fin 3 => c) (QWeyl.cyclicZDual γ q) m := by
  rw [vectorResidueFunctional_apply, vectorResidueFunctional_apply]
  have h := congrArg (fun p : BinaryLaurent K => c * p.coeff (-1,-1))
    (QWeyl.cyclic_pairing_transpose γ m q)
  simpa [AddMonoidAlgebra.coeff_sum, Finset.mul_sum, mul_comm] using h

end ChoppedPlane.LaurentPairing
