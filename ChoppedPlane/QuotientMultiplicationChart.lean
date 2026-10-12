module

public import ChoppedPlane.QuotientBasisChart
public import ChoppedPlane.ReducedOpen

@[expose] public section

/-!
# Denominator-cleared multiplication in a quotient chart

A square family of relations and quotient lifts can be inverted with an
adjugate.  Its determinant is a common denominator for every coordinate of
every product of quotient basis elements.  Product representatives may live
in a larger homogeneous component than the basis representatives; the proof
only uses the common linear map to the quotient algebra.
-/

noncomputable section
namespace ChoppedPlane
open Module MvPolynomial

variable {K ι V α κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Fintype α] [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
/-- The adjugate of a polynomial square combination chart is a polynomial
right inverse multiplied by a determinant.  The determinant is normalized to
one at the witness by using its combined vectors as the reference basis. -/
theorem polynomial_combination_adjugate_chart
    (r : α → (ι → K) → V) (l : κ → (ι → K) → V)
    (hr : ∀ i, IsPolynomialFamily (r i))
    (hl : ∀ i, IsPolynomialFamily (l i))
    (a₀ : ι → K)
    (h₀ : Function.Bijective
      (finiteCombination (K := K) (Sum.elim (fun i => r i a₀) (fun i => l i a₀)))) :
    ∃ (D : MvPolynomial ι K)
      (R : (ι → K) → (V →ₗ[K] (Sum α κ → K))),
      eval a₀ D = 1 ∧ IsPolynomialFamily R ∧
      ∀ a,
        (finiteCombination (K := K) (Sum.elim (fun i => r i a) (fun i => l i a))).comp
          (R a) = (eval a D) • LinearMap.id := by
  classical
  let F (a : ι → K) :=
    finiteCombination (K := K) (Sum.elim (fun i => r i a) (fun i => l i a))
  let bS := Pi.basisFun K (Sum α κ)
  let e : (Sum α κ → K) ≃ₗ[K] V := LinearEquiv.ofBijective (F a₀) h₀
  let bV := bS.map e
  have hF : IsPolynomialFamily F := by
    apply finiteCombination_isPolynomialFamily
    intro i
    cases i with
    | inl j => exact hr j
    | inr j => exact hl j
  obtain ⟨P, hP⟩ := polynomial_matrix_representation bS bV F hF
  let D : MvPolynomial ι K := P.det
  let R (a : ι → K) : V →ₗ[K] (Sum α κ → K) :=
    Matrix.toLin bV bS (P.adjugate.map (eval a))
  have hR : IsPolynomialFamily R := isPolynomialFamily_matrix_toLin bV bS P.adjugate
  have hD (a : ι → K) : eval a D = (LinearMap.toMatrix bS bV (F a)).det := by
    dsimp [D]
    rw [(eval a).map_det]
    change (P.map (eval a)).det = _
    rw [hP]
  have hP₀ : LinearMap.toMatrix bS bV (F a₀) = 1 := by
    ext i j
    rw [LinearMap.toMatrix_apply]
    change bV.repr (bV j) i = _
    simp only [Basis.repr_self_apply, Matrix.one_apply, eq_comm]
  refine ⟨D, R, ?_, hR, ?_⟩
  · rw [hD, hP₀, Matrix.det_one]
  · intro a
    have hs := congrArg (Matrix.toLin bV bV)
      (Matrix.mul_adjugate (LinearMap.toMatrix bS bV (F a)))
    have hadj : P.adjugate.map (eval a) = (P.map (eval a)).adjugate :=
      (eval a).map_adjugate P
    dsimp [R]
    rw [hadj, hP]
    rw [Matrix.toLin_mul bV bS bV, Matrix.toLin_toMatrix, map_smul,
      Matrix.toLin_one, ← hD] at hs
    exact hs

omit [FiniteDimensional K V] [DecidableEq κ] in
/-- Quotient coordinates discard the relation coordinates of a combined
relation-and-lift expression. -/
theorem combined_quotient_coordinates
    {A : Type*} [AddCommGroup A] [Module K A]
    (q : V →ₗ[K] A) (r : α → V) (l : κ → V) (b : Basis κ K A)
    (hr : ∀ i, q (r i) = 0) (hl : ∀ i, q (l i) = b i)
    (c : Sum α κ → K) (k : κ) :
    b.repr (q (finiteCombination (K := K) (Sum.elim r l) c)) k = c (.inr k) := by
  classical
  rw [finiteCombination_apply, map_sum, Fintype.sum_sum_type]
  simp only [map_smul, Sum.elim_inl, Sum.elim_inr, hr, hl, smul_zero,
    Finset.sum_const_zero, zero_add]
  exact congrFun (b.repr_sum_self (fun i => c (.inr i))) k

omit [DecidableEq κ] in
/-- A polynomial relation map supplies a polynomial relation basis adapted to
any fixed lifts of a witness quotient basis.  Only source preimages at the
witness are chosen; the same preimages are used for every specialization. -/
theorem polynomial_relations_for_quotient_basis
    {U W : Type*} [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : (ι → K) → (U →ₗ[K] V)) (hE : IsPolynomialFamily E)
    (a₀ : ι → K) (q : V →ₗ[K] W)
    (hker : LinearMap.range (E a₀) = LinearMap.ker q)
    (b : Basis κ K W) (l : κ → V) (hl : ∀ i, q (l i) = b i) :
    ∃ r : Fin (finrank K (LinearMap.range (E a₀))) → (ι → K) → V,
      (∀ i, IsPolynomialFamily (r i)) ∧
      (∀ a i, r i a ∈ LinearMap.range (E a)) ∧
      Function.Bijective
        (finiteCombination (K := K) (Sum.elim (fun i => r i a₀) l)) := by
  classical
  let bR := Module.finBasis K (LinearMap.range (E a₀))
  choose u hu using fun i => (bR i).property
  let r (i : Fin (finrank K (LinearMap.range (E a₀)))) (a : ι → K) := E a (u i)
  have hr (i) : r i a₀ = (bR i).val := hu i
  let F := finiteCombination (K := K) (Sum.elim (fun i => r i a₀) l)
  have hs : Function.Surjective F := by
    intro v
    let c : κ → K := fun i => b.repr (q v) i
    let w := v - ∑ i, c i • l i
    have hw : w ∈ LinearMap.range (E a₀) := by
      rw [hker]
      change q w = 0
      simp only [w, map_sub, map_sum, map_smul, hl, c, b.sum_repr, sub_self]
    let wR : LinearMap.range (E a₀) := ⟨w, hw⟩
    refine ⟨Sum.elim (fun i => bR.repr wR i) c, ?_⟩
    change finiteCombination (K := K) (Sum.elim (fun i => r i a₀) l) _ = v
    rw [finiteCombination_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, hr]
    have hsum : ∑ i, bR.repr wR i • (bR i).val = w := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        congrArg Subtype.val (bR.sum_repr wR)
    rw [hsum]
    exact sub_add_cancel v _
  have hsq : Function.Surjective q := by
    intro w
    refine ⟨∑ i, b.repr w i • l i, ?_⟩
    simp only [map_sum, map_smul, hl, b.sum_repr]
  have hdim := LinearMap.finrank_range_add_finrank_ker q
  rw [LinearMap.range_eq_top.mpr hsq, finrank_top, ← hker,
    Module.finrank_eq_card_basis b] at hdim
  have heqdim : finrank K
      (Sum (Fin (finrank K (LinearMap.range (E a₀)))) κ → K) = finrank K V := by
    simp only [Module.finrank_pi, Fintype.card_sum, Fintype.card_fin]
    omega
  have hi : Function.Injective F :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heqdim).mpr hs
  exact ⟨r, fun i => hE.linear_comp (LinearMap.applyₗ (R := K) (u i)),
    fun a i => ⟨u i, rfl⟩, hi, hs⟩

variable (A : (ι → K) → Type*)
  [∀ a, CommRing (A a)] [∀ a, Algebra K (A a)]

/-- Actual polynomial relations, lifts and products determine polynomial
multiplication matrices with one common determinant denominator.  The bases
can be provided only on a pre-existing principal open. -/
theorem polynomial_quotient_multiplication_chart
    (H₀ : MvPolynomial ι K)
    (b : ∀ a, eval a H₀ ≠ 0 → Basis κ K (A a))
    (q : ∀ a, V →ₗ[K] A a)
    (r : α → (ι → K) → V) (l : κ → (ι → K) → V)
    (p : κ → κ → (ι → K) → V)
    (hrpoly : ∀ i, IsPolynomialFamily (r i))
    (hlpoly : ∀ i, IsPolynomialFamily (l i))
    (hppoly : ∀ i j, IsPolynomialFamily (p i j))
    (hr : ∀ a, eval a H₀ ≠ 0 → ∀ i, q a (r i a) = 0)
    (hl : ∀ a (ha : eval a H₀ ≠ 0) i, q a (l i a) = b a ha i)
    (hp : ∀ a (ha : eval a H₀ ≠ 0) i j,
      q a (p i j a) = b a ha i * b a ha j)
    (a₀ : ι → K) (hH₀ : eval a₀ H₀ ≠ 0)
    (h₀ : Function.Bijective
      (finiteCombination (K := K) (Sum.elim (fun i => r i a₀) (fun i => l i a₀)))) :
    ∃ (H : MvPolynomial ι K)
      (M : κ → Matrix κ κ (MvPolynomial ι K)),
      eval a₀ H ≠ 0 ∧
      (∀ a, eval a H ≠ 0 → eval a H₀ ≠ 0) ∧
      ∀ a (ha : eval a H₀ ≠ 0),
        ∀ i, (M i).map (eval a) = (eval a H) •
          Algebra.leftMulMatrix (b a ha) (b a ha i) := by
  classical
  obtain ⟨D, R, hD₀, hR, hFR⟩ :=
    polynomial_combination_adjugate_chart r l hrpoly hlpoly a₀ h₀
  have hmPoly (i j k : κ) :
      IsPolynomialFamily (fun a => R a (p i j a) (.inr k)) := by
    have h := hR.bilinear (hppoly i j) (LinearMap.id :
      (V →ₗ[K] (Sum α κ → K)) →ₗ[K] V →ₗ[K] (Sum α κ → K))
    exact h.linear_comp (LinearMap.proj (.inr k))
  choose m hm using fun i j k => hmPoly i j k LinearMap.id
  let N : κ → Matrix κ κ (MvPolynomial ι K) := fun i k j => m i j k
  have hN (a : ι → K) (ha : eval a H₀ ≠ 0) (i : κ) :
      (N i).map (eval a) = (eval a D) •
        Algebra.leftMulMatrix (b a ha) (b a ha i) := by
    ext k j
    rw [Matrix.map_apply, Matrix.smul_apply, Algebra.leftMulMatrix_eq_repr_mul]
    have hc := combined_quotient_coordinates (q a) (fun i => r i a)
      (fun i => l i a) (b a ha) (hr a ha) (hl a ha) (R a (p i j a)) k
    have hf := LinearMap.congr_fun (hFR a) (p i j a)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hf
    rw [hf, map_smul, hp a ha i j, map_smul] at hc
    simpa only [N, LinearMap.id_apply, Finsupp.smul_apply, smul_eq_mul] using
      (hm i j k a).trans hc.symm
  refine ⟨H₀ * D, fun i => H₀ • N i, ?_, ?_, ?_⟩
  · rw [map_mul, hD₀, mul_one]
    exact hH₀
  · intro a ha
    exact (mul_ne_zero_iff.mp (by simpa only [map_mul] using ha)).1
  · intro a ha i
    rw [Matrix.map_smul' (eval a) H₀ (N i) (eval a).map_mul,
      hN a ha i, smul_smul, ← map_mul]

/-- A split witness and a polynomial relation-and-product chart give a
principal open of reduced quotient algebras.  No multiplication matrices are
assumed: the preceding adjugate construction supplies them. -/
theorem reduced_principal_open_of_polynomial_quotient_chart
    (H₀ : MvPolynomial ι K)
    (b : ∀ a, eval a H₀ ≠ 0 → Basis κ K (A a))
    (q : ∀ a, V →ₗ[K] A a)
    (r : α → (ι → K) → V) (l : κ → (ι → K) → V)
    (p : κ → κ → (ι → K) → V)
    (hrpoly : ∀ i, IsPolynomialFamily (r i))
    (hlpoly : ∀ i, IsPolynomialFamily (l i))
    (hppoly : ∀ i j, IsPolynomialFamily (p i j))
    (hr : ∀ a, eval a H₀ ≠ 0 → ∀ i, q a (r i a) = 0)
    (hl : ∀ a (ha : eval a H₀ ≠ 0) i, q a (l i a) = b a ha i)
    (hp : ∀ a (ha : eval a H₀ ≠ 0) i j,
      q a (p i j a) = b a ha i * b a ha j)
    (a₀ : ι → K) (hH₀ : eval a₀ H₀ ≠ 0)
    (h₀ : Function.Bijective
      (finiteCombination (K := K) (Sum.elim (fun i => r i a₀) (fun i => l i a₀))))
    (e : A a₀ ≃ₐ[K] (κ → K)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → IsReduced (A a) := by
  classical
  obtain ⟨H, M, hH, hH₀chart, hM⟩ :=
    polynomial_quotient_multiplication_chart A H₀ b q r l p
      hrpoly hlpoly hppoly hr hl hp a₀ hH₀ h₀
  let bH (a : ι → K) (ha : eval a H ≠ 0) : Basis κ K (A a) :=
    b a (hH₀chart a ha)
  exact reduced_principal_open_of_split_chart A M H bH
    (fun a ha i => hM a (hH₀chart a ha) i) a₀ hH e

end ChoppedPlane
