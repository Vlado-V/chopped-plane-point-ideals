module

public import ChoppedPlane.LaurentResidueOperators

@[expose] public section

/-! The literal top-Laurent projection is invisible to residue against an
actual positive polynomial grade. Thus the projected dual cyclic action,
rather than an abstract transpose, is the actual adjoint. -/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module
open scoped Classical
variable {K : Type*} [Field K] {ι : Type*}

theorem vectorResidueFunctional_basis_free [Finite ι] (g : ι → ℤ) (r : ℤ)
    (w : ι → K) (q : FreeLaurent K ι) (e : PositiveIndex g r) :
    vectorResidueFunctional w (freeLaurentEquiv q)
      (freeLaurentEquiv (positiveBasis g r e).val) =
      w e.val.1 * q (complementIndex g r e).val := by
  classical
  letI := Fintype.ofFinite ι
  rw [vectorResidueFunctional_apply]
  simp only [freeLaurentEquiv_positiveBasis]
  rw [Finset.sum_eq_single e.val.1]
  · simp [AddMonoidAlgebra.coeff_mul_single_apply, complementIndex]
    left
    exact congrArg (fun z : ℤ × ℤ => q (e.val.1,z))
      (Prod.ext (by simp [sub_eq_add_neg]) (by simp [sub_eq_add_neg]))
  · intro i hi hne
    simp [Ne.symm hne]
  · simp

/-- Projection to the genuine top Laurent representatives changes no
residue against any polynomial representative. -/
theorem vectorResidueFunctional_freeNegativePart [Finite ι]
    (g : ι → ℤ) (r : ℤ) (w : ι → K) (q : FreeLaurent K ι)
    (p : positiveGrade (K := K) g r) :
    vectorResidueFunctional w (freeLaurentEquiv (freeNegativePart q)) (freeLaurentEquiv p.val) =
      vectorResidueFunctional w (freeLaurentEquiv q) (freeLaurentEquiv p.val) := by
  have h : (vectorResidueFunctional w (freeLaurentEquiv (freeNegativePart q))).comp
      ((freeLaurentEquiv (K := K)).toLinearMap.comp (positiveGrade g r).subtype) =
      (vectorResidueFunctional w (freeLaurentEquiv q)).comp
        ((freeLaurentEquiv (K := K)).toLinearMap.comp (positiveGrade g r).subtype) := by
    apply (positiveBasis g r).ext
    intro e
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      vectorResidueFunctional_basis_free]
    have hn : -1-e.val.2.1 < 0 ∧ -1-e.val.2.2 < 0 := by
      obtain ⟨ha,hb,hab⟩ := e.property
      omega
    change w e.val.1 * freeNegativePart q (e.val.1,(-1-e.val.2.1,-1-e.val.2.2)) = _
    rw [freeNegativePart_apply, ite_eq_left hn]
    rfl
  exact LinearMap.congr_fun h p

/-- The same exact projection identity on the actual componentwise Laurent module. -/
theorem vectorResidueFunctional_componentNegativePart [Finite ι]
    (g : ι → ℤ) (r : ℤ) (w : ι → K) (q : ι → BinaryLaurent K)
    (p : positiveGrade (K := K) g r) :
    vectorResidueFunctional w (fun i => negativePart (q i)) (freeLaurentEquiv p.val) =
      vectorResidueFunctional w q (freeLaurentEquiv p.val) := by
  have h := vectorResidueFunctional_freeNegativePart g r w (freeLaurentEquiv.symm q) p
  have he : freeLaurentEquiv (freeNegativePart (freeLaurentEquiv.symm q)) =
      fun i => negativePart (q i) := by
    funext i
    rw [freeLaurentEquiv_negativePart]
    exact congrArg (fun f : ι → BinaryLaurent K => negativePart (f i))
      (freeLaurentEquiv.apply_symm_apply q)
  rw [he, LinearEquiv.apply_symm_apply] at h
  exact h

/-- The actual top-Laurent cyclic transpose is cyclic multiplication followed
by the actual strictly negative exponent projection. -/
theorem vectorResidueFunctional_projected_cyclic_transpose
    (g : Fin 3 → ℤ) (r : ℤ) (c : K) (γ q : Fin 3 → BinaryLaurent K)
    (p : positiveGrade (K := K) g r) :
    vectorResidueFunctional (fun _ : Fin 3 => c) q (QWeyl.cyclicZ γ (freeLaurentEquiv p.val)) =
      vectorResidueFunctional (fun _ : Fin 3 => c)
        (fun i => negativePart (QWeyl.cyclicZDual γ q i)) (freeLaurentEquiv p.val) := by
  rw [vectorResidueFunctional_cyclic_transpose]
  exact (vectorResidueFunctional_componentNegativePart g r (fun _ => c) _ p).symm

end ChoppedPlane.LaurentPairing
