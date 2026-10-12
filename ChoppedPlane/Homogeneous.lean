module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Homogeneous polynomial spaces

The spaces and maps in this file use actual multivariate polynomials. The
monomial-basis construction and its dimension proof are adapted from
`Quartic.Homogeneous` in the local Fröberg formalization. The homogeneous
evaluation scaling proof is adapted from `OAI.Nagata.W16` in
`OAI.AlgebraicGeometry.PlaneCurves.Forms`. Both are reproduced here with their
proofs, so this module has no dependency on either manuscript's theorem.
-/

noncomputable section

namespace ChoppedPlane

open MvPolynomial Module

variable (K : Type*) [Field K] (n d : ℕ)

abbrev Poly := MvPolynomial (Fin n) K

abbrev Forms := MvPolynomial.homogeneousSubmodule (Fin n) K d

/-- Degree-`d` exponent vectors are multisets of `d` variable indices. -/
def exponentEquiv : Sym (Fin n) d ≃ {e : Fin n →₀ ℕ // e.degree = d} :=
  Sym.equivNatSum (Fin n) d

/-- The monomial basis of the genuine homogeneous polynomial subspace. -/
def formsBasis : Basis (Sym (Fin n) d) K (Forms K n d) := by
  rw [Forms, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  exact (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (exponentEquiv n d).symm

private theorem basis_transport_val {M ι : Type*} [AddCommGroup M] [Module K M]
    {P Q : Submodule K M} (h : P = Q) (b : Basis ι K Q) (i : ι) :
    (Eq.mpr (congrArg (fun W : Submodule K M => Basis ι K W) h) b i).val = (b i).val := by
  subst P
  rfl

/-- The form basis consists of coefficient-one monomials, with exponent index
independent of the coefficient field. -/
theorem formsBasis_val_monomial (i : Sym (Fin n) d) :
    (formsBasis K n d i).val = monomial (exponentEquiv n d i).val 1 := by
  let b := (MvPolynomial.basisRestrictSupport K {e : Fin n →₀ ℕ | e.degree = d}).reindex
    (exponentEquiv n d).symm
  have h : Forms K n d = MvPolynomial.restrictSupport K {e : Fin n →₀ ℕ | e.degree = d} :=
    homogeneousSubmodule_eq_finsupp_supported (Fin n) K d
  have hval : (formsBasis K n d i).val = (b i).val :=
    basis_transport_val K h b i
  rw [hval]
  simp only [b, Basis.reindex_apply, Equiv.symm_symm]
  change ((AddMonoidAlgebra.supportedEquivFinsupp {e : Fin n →₀ ℕ | e.degree = d}).symm
    (Finsupp.single (exponentEquiv n d i) 1)).val = _
  simp [AddMonoidAlgebra.supportedEquivFinsupp]
  rfl

/-- Coefficient maps preserve the chosen homogeneous monomial basis. -/
theorem formsBasis_map {L : Type*} [Field L] (k : K →+* L) (i : Sym (Fin n) d) :
    MvPolynomial.map k (formsBasis K n d i).val = (formsBasis L n d i).val := by
  rw [formsBasis_val_monomial, formsBasis_val_monomial]
  simp

instance formsFinite : Module.Finite K (Forms K n d) :=
  Module.Finite.of_basis (formsBasis K n d)

/-- Stars and bars as a dimension theorem for homogeneous forms. -/
theorem finrank_forms : finrank K (Forms K n d) = (n + d - 1).choose d := by
  rw [Module.finrank_eq_card_basis (formsBasis K n d), Sym.card_sym_eq_choose]
  simp

/-- The dimension of ternary degree-`d` forms. -/
theorem finrank_plane_forms : finrank K (Forms K 3 d) = (d + 2).choose 2 := by
  rw [finrank_forms]
  have h : 3 + d - 1 = d + 2 := by omega
  rw [h, ← Nat.choose_symm (by omega : d ≤ d + 2)]
  simp

variable {K n d} {e : ℕ}

/-- Multiplication by a fixed form, with the correct homogeneous target. -/
def mulForm (f : Forms K n d) : Forms K n e →ₗ[K] Forms K n (d + e) where
  toFun a := ⟨f.val * a.val, f.property.mul a.property⟩
  map_add' a b := Subtype.ext (mul_add f.val a.val b.val)
  map_smul' k a := Subtype.ext (mul_smul_comm k f.val a.val)

@[simp] theorem mulForm_val (f : Forms K n d) (a : Forms K n e) :
    (mulForm f a).val = f.val * a.val := rfl

/-- A nonzero form multiplies injectively in a polynomial ring over a field. -/
theorem mulForm_injective (f : Forms K n d) (hf : f.val ≠ 0) :
    Function.Injective (mulForm (e := e) f) := by
  intro a b hab
  apply Subtype.ext
  exact mul_left_cancel₀ hf (congrArg Subtype.val hab)

/-- All products of degree-`d` and degree-`e` forms span degree `d + e`. -/
theorem forms_mul_forms : Forms K n d * Forms K n e = Forms K n (d + e) := by
  calc
    Forms K n d * Forms K n e = Forms K n 1 ^ d * Forms K n 1 ^ e := by
      simp only [Forms, MvPolynomial.homogeneousSubmodule_one_pow]
    _ = Forms K n 1 ^ (d + e) := (pow_add _ d e).symm
    _ = Forms K n (d + e) := MvPolynomial.homogeneousSubmodule_one_pow K (d + e)

/-- Evaluation on a fixed homogeneous representative is a linear functional. -/
def evaluationLinear (K : Type*) [Field K] (n d : ℕ) (x : Fin n → K) :
    Forms K n d →ₗ[K] K where
  toFun f := MvPolynomial.eval x f.val
  map_add' f g := map_add _ _ _
  map_smul' c f := by simp

@[simp] theorem evaluationLinear_apply (x : Fin n → K) (f : Forms K n d) :
    evaluationLinear K n d x f = MvPolynomial.eval x f.val := rfl

section Scaling

/-- Homogeneous scaling after any coefficient-ring map. -/
theorem homogeneous_eval₂_scale {σ R T : Type*} [CommSemiring R] [CommSemiring T]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (k : R →+* T) (x : σ → T) (a : T) :
    MvPolynomial.eval₂ k (fun i => a * x i) f =
      a ^ d * MvPolynomial.eval₂ k x f := by
  classical
  simp only [MvPolynomial.eval₂_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hf.degree_eq_sum_deg_support hu]
  ac_rfl

/-- Homogeneous evaluation commutes with scalar rescaling. -/
theorem homogeneous_eval_scale {σ R : Type*} [CommSemiring R]
    {f : MvPolynomial σ R} {d : ℕ} (hf : f.IsHomogeneous d)
    (x : σ → R) (a : R) :
    MvPolynomial.eval (fun i => a * x i) f = a ^ d * MvPolynomial.eval x f := by
  classical
  simp only [MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← hf.degree_eq_sum_deg_support hu]
  ac_rfl

/-- Vanishing of a homogeneous form is invariant under nonzero rescaling. -/
theorem homogeneous_eval_scale_eq_zero_iff {σ R : Type*} [CommRing R]
    [IsDomain R] {f : MvPolynomial σ R} {d : ℕ}
    (hf : f.IsHomogeneous d) (x : σ → R) {a : R} (ha : a ≠ 0) :
    MvPolynomial.eval (fun i => a * x i) f = 0 ↔ MvPolynomial.eval x f = 0 := by
  rw [homogeneous_eval_scale hf x a]
  simp only [mul_eq_zero, pow_ne_zero d ha, false_or]

end Scaling

end ChoppedPlane
