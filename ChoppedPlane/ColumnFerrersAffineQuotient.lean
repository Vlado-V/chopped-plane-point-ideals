module

public import ChoppedPlane.ColumnFerrers

@[expose] public section

/-!
The affine quotient of the column-graded split Ferrers seed is the algebra of functions on
its displayed selected points. The proof restricts the full-grid interpolation
map and uses the actual cofactor separators to identify its kernel.
-/

noncomputable section
namespace ChoppedPlane.ColumnFerrers
open MvPolynomial
variable {K : Type*} [Field K] {m : ℕ}

/-- The inclusion of selected root pairs into the finite full Cartesian grid. -/
def selectedGridIndex (δ : Fin m → ℕ) (s : SelectedIndex δ) :
    Fin (Fintype.card (RootIndex δ)) × Fin (Fintype.card (RootIndex δ)) :=
  (Fintype.equivFin (RootIndex δ) ⟨s.1.val.1, s.2.1⟩,
   Fintype.equivFin (RootIndex δ) ⟨s.1.val.2, s.2.2⟩)

theorem selectedGridIndex_injective (δ : Fin m → ℕ) :
    Function.Injective (selectedGridIndex δ) := by
  intro s t h
  have hx := (Fintype.equivFin (RootIndex δ)).injective (congrArg Prod.fst h)
  have hy := (Fintype.equivFin (RootIndex δ)).injective (congrArg Prod.snd h)
  obtain ⟨⟨⟨i,j⟩, hij⟩, a,b⟩ := s
  obtain ⟨⟨⟨i',j'⟩, hij'⟩, a',b'⟩ := t
  change (⟨i,a⟩ : RootIndex δ) = ⟨i',a'⟩ at hx
  change (⟨j,b⟩ : RootIndex δ) = ⟨j',b'⟩ at hy
  cases hx
  cases hy
  rfl

@[simp] theorem selectedGridIndex_mem (δ : Fin m → ℕ) (s : SelectedIndex δ) :
    selectedGridIndex δ s ∈ selectedGridSet δ := by
  simpa [selectedGridIndex, selectedGridSet] using s.1.property

/-- Evaluation at the displayed selected affine points, as a coefficient-field
algebra map. -/
def selectedAffineEvaluation (δ : Fin m → ℕ) (α β : RootIndex δ → K) :
    Poly K 2 →ₐ[K] (SelectedIndex δ → K) where
  toRingHom := RingHom.pi (fun s => eval ![selectedX δ α s, selectedY δ β s])
  commutes' a := by
    ext s
    change eval ![selectedX δ α s, selectedY δ β s] (C a) = a
    simp

@[simp] theorem selectedAffineEvaluation_apply (δ : Fin m → ℕ)
    (α β : RootIndex δ → K) (f : Poly K 2) (s : SelectedIndex δ) :
    selectedAffineEvaluation δ α β f s = eval ![selectedX δ α s, selectedY δ β s] f := rfl

/-- Selected evaluation is full-grid evaluation followed by restriction. -/
theorem selectedAffineEvaluation_eq_full (δ : Fin m → ℕ) (α β : RootIndex δ → K)
    (f : Poly K 2) (s : SelectedIndex δ) :
    selectedAffineEvaluation δ α β f s =
      Grid.mvAffineGridEvaluation (Ferrers.flatRoots δ α) (Ferrers.flatRoots δ β) f (selectedGridIndex δ s) := by
  simp [Grid.mvAffineGridEvaluation_apply, selectedGridIndex, Ferrers.flatRoots,
    selectedX, selectedY]

/-- Arbitrary values on selected points are realized by actual affine
polynomials. -/
theorem selectedAffineEvaluation_surjective (δ : Fin m → ℕ) (α β : RootIndex δ → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Surjective (selectedAffineEvaluation δ α β) := by
  intro v
  obtain ⟨w, hw⟩ := (selectedGridIndex_injective δ).surjective_comp_right (γ := K) v
  obtain ⟨f, hf⟩ := Grid.mvAffineGridEvaluation_surjective
    (Ferrers.flatRoots δ α) (Ferrers.flatRoots δ β)
    (Ferrers.flatRoots_injective δ α hα) (Ferrers.flatRoots_injective δ β hβ) w
  refine ⟨f, ?_⟩
  ext s
  rw [selectedAffineEvaluation_eq_full, hf]
  exact congrFun hw s

/-- Every affine cofactor vanishes on the selected diagram. -/
theorem affineCofactorIdeal_le_selectedAffineEvaluation_ker 
    (δ : Fin m → ℕ) (α β : RootIndex δ → K) :
    affineCofactorIdeal δ α β ≤ RingHom.ker (selectedAffineEvaluation δ α β).toRingHom := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro f ⟨j,rfl⟩
  change selectedAffineEvaluation δ α β (affineDehom (cofactorProduct δ α β j)) = 0
  ext s
  simpa [selectedAffineEvaluation_apply, Ferrers.eval_affineDehom] using
    cofactorProduct_eval_selected δ α β s j

/-- The actual affine cofactor ideal is exactly the kernel of selected-point
evaluation. -/
theorem selectedAffineEvaluation_ker (δ : Fin m → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    RingHom.ker (selectedAffineEvaluation δ α β).toRingHom = affineCofactorIdeal δ α β := by
  apply le_antisymm
  · intro f hf
    have hker : RingHom.ker
        (Grid.mvAffineGridEvaluation (Ferrers.flatRoots δ α) (Ferrers.flatRoots δ β)) ≤
        affineCofactorIdeal δ α β := by
      rw [Grid.mvAffineGridEvaluation_ker _ _ (Ferrers.flatRoots_injective δ α hα)
        (Ferrers.flatRoots_injective δ β hβ)]
      exact mvAffineGridIdeal_le_affineCofactorIdeal δ α β
    apply mem_ideal_of_vanish_on_selected
      (Grid.mvAffineGridEvaluation (Ferrers.flatRoots δ α) (Ferrers.flatRoots δ β))
      (Grid.mvAffineGridEvaluation_surjective _ _ (Ferrers.flatRoots_injective δ α hα)
        (Ferrers.flatRoots_injective δ β hβ))
      (affineCofactorIdeal δ α β) hker (selectedGridSet δ)
      (affineCofactor_separator δ α β hα hβ)
    intro ij hij
    let u := (Fintype.equivFin (RootIndex δ)).symm ij.1
    let v := (Fintype.equivFin (RootIndex δ)).symm ij.2
    have huv : u.1 ≤ v.1 := hij
    let s : SelectedIndex δ := ⟨⟨(u.1,v.1),huv⟩,(u.2,v.2)⟩
    have hh := congrFun (show selectedAffineEvaluation δ α β f = 0 from hf) s
    simpa [Grid.mvAffineGridEvaluation_apply, Ferrers.flatRoots, selectedAffineEvaluation_apply,
      selectedX,selectedY,s,u,v] using hh
  · exact affineCofactorIdeal_le_selectedAffineEvaluation_ker δ α β

/-- The affine seed quotient is the full algebra of functions on its selected
points, with no extra points or nilpotents. -/
def affineCofactorQuotientAlgEquiv (δ : Fin m → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    (Poly K 2 ⧸ affineCofactorIdeal δ α β) ≃ₐ[K] (SelectedIndex δ → K) :=
  (Ideal.quotientEquivAlgOfEq K (selectedAffineEvaluation_ker δ α β hα hβ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := selectedAffineEvaluation δ α β)
      (selectedAffineEvaluation_surjective δ α β hα hβ))

theorem affineCofactorQuotient_finite (δ : Fin m → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    Module.Finite K (Poly K 2 ⧸ affineCofactorIdeal δ α β) :=
  Module.Finite.of_surjective (affineCofactorQuotientAlgEquiv δ α β hα hβ).symm.toLinearMap
    (affineCofactorQuotientAlgEquiv δ α β hα hβ).symm.surjective

/-- The actual affine quotient length is the exact number of selected cells. -/
theorem affineCofactorQuotient_finrank (δ : Fin m → ℕ)
    (α β : RootIndex δ → K) (hα : Function.Injective α) (hβ : Function.Injective β) :
    Module.finrank K (Poly K 2 ⧸ affineCofactorIdeal δ α β) = Fintype.card (SelectedIndex δ) := by
  rw [(affineCofactorQuotientAlgEquiv δ α β hα hβ).toLinearEquiv.finrank_eq]
  simp

end ChoppedPlane.ColumnFerrers
