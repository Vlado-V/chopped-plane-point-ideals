module

public import Mathlib.RingTheory.MvPolynomial.MonomialOrder
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Finite sums with distinct leading monomials

The greatest leading monomial in a nonempty finite family occurs in exactly
one summand. Its coefficient therefore survives in the sum.
-/
noncomputable section
namespace MonomialOrder
open MvPolynomial
open scoped MonomialOrder

variable {σ α R : Type*} [CommSemiring R]

/-- A finite nonempty family of nonzero polynomials with pairwise distinct
leading degrees has a nonzero sum, for any monomial order. -/
theorem sum_ne_zero_of_degree_injOn (m : MonomialOrder σ)
    (s : Finset α) (f : α → MvPolynomial σ R) (hs : s.Nonempty)
    (hnz : ∀ i ∈ s, f i ≠ 0)
    (hinj : Set.InjOn (fun i => m.degree (f i)) (s : Set α)) :
    (∑ i ∈ s, f i) ≠ 0 := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image s
    (fun j => m.toSyn (m.degree (f j))) hs
  have hcoeff : (∑ j ∈ s, f j).coeff (m.degree (f i)) = m.leadingCoeff (f i) := by
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single i]
    · rfl
    · intro j hj hji
      apply m.coeff_eq_zero_of_lt
      apply lt_of_le_of_ne (hmax j hj)
      intro heq
      exact hji (hinj hj hi (m.toSyn.injective heq))
    · exact fun h => False.elim (h hi)
  intro hz
  have hlead := m.leadingCoeff_ne_zero_iff.mpr (hnz i hi)
  apply hlead
  rw [← hcoeff, hz]
  simp

end MonomialOrder
