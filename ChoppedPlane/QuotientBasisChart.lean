module

public import ChoppedPlane.KernelRankOpen

@[expose] public section

/-! A finite-dimensional quotient has a basis of fixed vectors on a polynomial
chart. The chart is certified by a single determinant of relations and lifts. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module

variable {K ι V α κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype α] [Fintype κ]

/-- Linear combinations of a finite family of vectors. -/
def finiteCombination (v : κ → V) : (κ → K) →ₗ[K] V :=
  ∑ i, (LinearMap.toSpanSingleton K V (v i)).comp (LinearMap.proj i)

omit [FiniteDimensional K V] in
@[simp] theorem finiteCombination_apply (v : κ → V) (c : κ → K) :
    finiteCombination (K := K) v c = ∑ i, c i • v i := by
  simp [finiteCombination]

omit [FiniteDimensional K V] in
/-- On an invertible combined relation-and-lift chart, the lifts span the
quotient. -/
theorem quotient_lifts_surjective (Q : Submodule K V) (r : α → V) (b : κ → V)
    (hr : ∀ i, r i ∈ Q)
    (h : Function.Surjective (finiteCombination (K := K) (Sum.elim r b))) :
    Function.Surjective (Q.mkQ.comp (finiteCombination (K := K) b)) := by
  classical
  intro x
  obtain ⟨v, rfl⟩ := Q.mkQ_surjective x
  obtain ⟨c, hc⟩ := h v
  refine ⟨fun i => c (.inr i), ?_⟩
  have hre : Q.mkQ (∑ i, c (.inl i) • r i) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero Q).mpr
    exact Q.sum_mem fun i _ => Q.smul_mem _ (hr i)
  have hs := congrArg Q.mkQ hc
  rw [finiteCombination_apply, Fintype.sum_sum_type, map_add] at hs
  simp only [Sum.elim_inl, Sum.elim_inr] at hs
  rw [hre, zero_add] at hs
  simpa only [LinearMap.comp_apply, finiteCombination_apply] using hs

/-- If the lifts have the quotient's dimension, spanning makes them a basis. -/
noncomputable def quotientBasisOfCombined (Q : Submodule K V) (r : α → V) (b : κ → V)
    (hr : ∀ i, r i ∈ Q)
    (h : Function.Surjective (finiteCombination (K := K) (Sum.elim r b)))
    (hdim : finrank K (V ⧸ Q) = Fintype.card κ) : Basis κ K (V ⧸ Q) := by
  let F := Q.mkQ.comp (finiteCombination (K := K) b)
  have hs : Function.Surjective F := quotient_lifts_surjective Q r b hr h
  have hi : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by simpa using hdim.symm)).mpr hs
  exact (Pi.basisFun K κ).map (LinearEquiv.ofBijective F ⟨hi, hs⟩)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem quotientBasisOfCombined_apply [DecidableEq κ]
    (Q : Submodule K V) (r : α → V) (b : κ → V) (hr) (h) (hdim) (i : κ) :
    quotientBasisOfCombined Q r b hr h hdim i = Q.mkQ (b i) := by
  unfold quotientBasisOfCombined
  rw [Basis.map_apply, LinearEquiv.ofBijective_apply, Pi.basisFun_apply]
  change Q.mkQ (finiteCombination (K := K) b (Pi.single i 1)) = Q.mkQ (b i)
  simp [finiteCombination_apply, Pi.single_apply]

omit [FiniteDimensional K V] in
/-- Polynomial dependence of a finite linear-combination map. -/
theorem finiteCombination_isPolynomialFamily
    (v : κ → (ι → K) → V) (hv : ∀ i, IsPolynomialFamily (v i)) :
    IsPolynomialFamily (fun a => finiteCombination (K := K) (fun i => v i a)) := by
  apply isPolynomialFamily_linearMap
  intro c
  have hs := IsPolynomialFamily.sum fun i =>
    (isPolynomialFamily_const (c i)).smul (hv i)
  simpa only [finiteCombination_apply] using hs

/-- Fixed quotient lifts form a basis wherever one polynomial determinant is
nonzero. A quotient-dimension hypothesis is needed only on that chart. -/
theorem quotient_basis_principal_open
    (Q : (ι → K) → Submodule K V)
    (r : α → (ι → K) → V) (b : κ → V)
    (hrpoly : ∀ i, IsPolynomialFamily (r i))
    (hrQ : ∀ a i, r i a ∈ Q a)
    (a₀ : ι → K)
    (h₀ : Function.Bijective (finiteCombination (K := K) (Sum.elim (fun i => r i a₀) b))) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 →
      finrank K (V ⧸ Q a) = Fintype.card κ →
      ∃ B : Basis κ K (V ⧸ Q a), ∀ i, B i = (Q a).mkQ (b i) := by
  classical
  let F (a : ι → K) := finiteCombination (K := K) (Sum.elim (fun i => r i a) b)
  have hF : IsPolynomialFamily F := by
    apply finiteCombination_isPolynomialFamily
    intro i
    cases i with
    | inl j => exact hrpoly j
    | inr j => exact isPolynomialFamily_const (b j)
  obtain ⟨D, hD, hprop⟩ := rank_polynomial_principal_open F hF a₀
  refine ⟨D, hD, fun a ha hdim => ?_⟩
  have hs : Function.Surjective (F a) := by
    apply LinearMap.range_eq_top.mp
    apply Submodule.eq_top_of_finrank_eq
    have hn := hprop a ha
    rw [LinearMap.range_eq_top.mpr h₀.2, finrank_top] at hn
    exact le_antisymm (Submodule.finrank_le _) hn
  exact ⟨quotientBasisOfCombined (Q a) (fun i => r i a) b (hrQ a) hs hdim,
    fun i => quotientBasisOfCombined_apply _ _ _ _ _ _ i⟩

end ChoppedPlane
