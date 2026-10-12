module

public import ChoppedPlane.PolynomialOperatorDuality

@[expose] public section

/-! Actual coefficient differentiation commutes with simultaneous changes
of its source and target coefficient coordinates. -/
noncomputable section
namespace ChoppedPlane
variable {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']

theorem operatorDifferential_equiv_apply
    (E : V ≃ₗ[K] V') (F : W ≃ₗ[K] W')
    (T : Fin 3 → V →ₗ[K] W) (T' : Fin 3 → V' →ₗ[K] W')
    (h : ∀ i v, F (T i v) = T' i (E v)) (t : ℕ)
    (c : Sym (Fin 3) (t+1) → V) :
    (fun s => F (operatorDifferential T t c s)) =
      operatorDifferential T' t (fun s => E (c s)) := by
  funext s
  simp only [operatorDifferential_coeff, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro i hi
  rw [h]

theorem operatorDifferential_surjective_iff_of_equiv
    (E : V ≃ₗ[K] V') (F : W ≃ₗ[K] W')
    (T : Fin 3 → V →ₗ[K] W) (T' : Fin 3 → V' →ₗ[K] W')
    (h : ∀ i v, F (T i v) = T' i (E v)) (t : ℕ) :
    Function.Surjective (operatorDifferential T t) ↔
      Function.Surjective (operatorDifferential T' t) := by
  constructor
  · intro hs y
    obtain ⟨x,hx⟩ := hs (fun s => F.symm (y s))
    refine ⟨fun s => E (x s), ?_⟩
    rw [← operatorDifferential_equiv_apply E F T T' h t x, hx]
    funext s
    exact F.apply_symm_apply _
  · intro hs y
    obtain ⟨x,hx⟩ := hs (fun s => F (y s))
    refine ⟨fun s => E.symm (x s), ?_⟩
    have he := operatorDifferential_equiv_apply E F T T' h t
      (fun s => E.symm (x s))
    have hex : (fun s => E (E.symm (x s))) = x := by
      funext s
      exact E.apply_symm_apply _
    rw [hex, hx] at he
    funext s
    exact F.injective (congrFun he s)

end ChoppedPlane
