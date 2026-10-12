module

public import ChoppedPlane.KernelProductRank

@[expose] public section

/-!
# Polynomial charts for kernels of surjective maps

A fixed right inverse at the witness supplies a square polynomial matrix.
Its adjugate clears denominators and gives a polynomial endomorphism whose
image is the varying kernel wherever that determinant is nonzero.
-/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial
variable {K ι V U W T : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W] [AddCommGroup T] [Module K T]

/-- Subtraction preserves polynomial dependence. -/
theorem IsPolynomialFamily.sub {f g : (ι → K) → V}
    (hf : IsPolynomialFamily f) (hg : IsPolynomialFamily g) :
    IsPolynomialFamily (fun a => f a - g a) := by
  simpa only [LinearMap.neg_apply, LinearMap.id_apply, sub_eq_add_neg] using
    hf.add (hg.linear_comp (-LinearMap.id))

/-- A matrix of parameter polynomials specializes to a polynomial map family. -/
theorem isPolynomialFamily_matrix_toLin
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [FiniteDimensional K V]
    (bV : Basis n K V) (bU : Basis m K U)
    (P : Matrix m n (MvPolynomial ι K)) :
    IsPolynomialFamily (fun a => Matrix.toLin bV bU (P.map (eval a))) := by
  apply isPolynomialFamily_linearMap
  intro x
  have hterm (i : m) (j : n) :
      IsPolynomialFamily (fun a => (eval a (P i j) * bV.repr x j) • bU i) := by
    have h := (isPolynomialFamily_eval (P i j * C (bV.repr x j))).smul
      (isPolynomialFamily_const (bU i))
    have heq : (fun a : ι → K => eval a (P i j * C (bV.repr x j)) • bU i) =
        (fun a => (eval a (P i j) * bV.repr x j) • bU i) := by
      funext a
      rw [eval_mul, eval_C]
    rw [heq] at h
    exact h
  have h := IsPolynomialFamily.sum (fun i => IsPolynomialFamily.sum (hterm i))
  simpa only [Matrix.toLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
    Finset.sum_smul] using h

/-- Polynomial matrices represent polynomial families of finite-dimensional maps. -/
theorem polynomial_matrix_representation [FiniteDimensional K V]
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (bV : Basis n K V) (bU : Basis m K U)
    (E : (ι → K) → (V →ₗ[K] U)) (hE : IsPolynomialFamily E) :
    ∃ P : Matrix m n (MvPolynomial ι K),
      ∀ a, P.map (eval a) = LinearMap.toMatrix bV bU (E a) := by
  have hpoly (i : m) (j : n) :=
    (hE.linear_comp (LinearMap.applyₗ (R := K) (M₂ := U) (bV j))).linear_comp (bU.coord i)
  choose p hp using fun i j => hpoly i j LinearMap.id
  let P : Matrix m n (MvPolynomial ι K) := p
  refine ⟨P, fun a => ?_⟩
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply]
  simpa only [P, LinearMap.id_apply, LinearMap.applyₗ_apply_apply, Basis.coord_apply] using hp i j a

/-- A polynomial endomorphism with image equal to the kernel on a nonempty
principal open containing any surjective witness. It restricts to the identity
on the witness kernel. -/
theorem polynomial_kernel_chart [FiniteDimensional K V] [FiniteDimensional K U]
    (E : (ι → K) → (V →ₗ[K] U)) (hE : IsPolynomialFamily E)
    (a₀ : ι → K) (hsurj : Function.Surjective (E a₀)) :
    ∃ (D : MvPolynomial ι K) (C : (ι → K) → (V →ₗ[K] V)),
      IsPolynomialFamily C ∧ eval a₀ D = 1 ∧
      (∀ a, LinearMap.range (C a) ≤ LinearMap.ker (E a)) ∧
      (∀ a, eval a D ≠ 0 → LinearMap.range (C a) = LinearMap.ker (E a) ∧
        Function.Surjective (E a)) ∧
      (∀ v, v ∈ LinearMap.ker (E a₀) → C a₀ v = v) := by
  classical
  obtain ⟨L, hL⟩ := (E a₀).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let b := Module.finBasis K U
  have hEL : IsPolynomialFamily (fun a => (E a).comp L) := by
    apply isPolynomialFamily_linearMap
    intro x
    exact hE.linear_comp (LinearMap.applyₗ (R := K) (M₂ := U) (L x))
  obtain ⟨P, hP⟩ := polynomial_matrix_representation b b
    (fun a => (E a).comp L) hEL
  let D : MvPolynomial ι K := P.det
  let R (a : ι → K) : U →ₗ[K] U := Matrix.toLin b b (P.adjugate.map (eval a))
  let C (a : ι → K) : V →ₗ[K] V :=
    (eval a D) • LinearMap.id - L.comp ((R a).comp (E a))
  have hR : IsPolynomialFamily R := isPolynomialFamily_matrix_toLin b b P.adjugate
  have hRE : IsPolynomialFamily (fun a => (R a).comp (E a)) :=
    hR.bilinear hE (LinearMap.llcomp K V U U)
  have hC : IsPolynomialFamily C := by
    apply (isPolynomialFamily_eval D).smul (isPolynomialFamily_const LinearMap.id) |>.sub
    exact hRE.linear_comp ((LinearMap.llcomp K V U V) L)
  have hD (a : ι → K) : eval a D = (LinearMap.toMatrix b b ((E a).comp L)).det := by
    dsimp [D]
    rw [(eval a).map_det]
    change (P.map (eval a)).det = _
    rw [hP]
  have hD₀ : eval a₀ D = 1 := by
    rw [hD, hL]
    simp
  have hcomp (a : ι → K) : ((E a).comp L).comp (R a) =
      (eval a D) • LinearMap.id := by
    change ((E a).comp L).comp (Matrix.toLin b b (P.adjugate.map (eval a))) = _
    have hadj : P.adjugate.map (eval a) = (P.map (eval a)).adjugate :=
      (eval a).map_adjugate P
    rw [hadj, hP]
    have hs := congrArg (Matrix.toLin b b)
      (Matrix.mul_adjugate (LinearMap.toMatrix b b ((E a).comp L)))
    rw [Matrix.toLin_mul b b b, Matrix.toLin_toMatrix, map_smul, Matrix.toLin_one,
      ← hD] at hs
    exact hs
  have hker (a : ι → K) : LinearMap.range (C a) ≤ LinearMap.ker (E a) := by
    rintro _ ⟨v, rfl⟩
    change E a (C a v) = 0
    have hc := LinearMap.congr_fun (hcomp a) (E a v)
    simpa only [C, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.comp_apply, map_sub, map_smul, sub_eq_zero] using hc.symm
  have hfix (a : ι → K) (v : V) (hv : v ∈ LinearMap.ker (E a)) :
      C a v = (eval a D) • v := by
    have hz : E a v = 0 := hv
    simp [C, hz]
  refine ⟨D, C, hC, hD₀, hker, ?_, ?_⟩
  · intro a ha
    constructor
    · apply le_antisymm (hker a)
      intro v hv
      refine ⟨(eval a D)⁻¹ • v, ?_⟩
      rw [map_smul, hfix a v hv, smul_smul, inv_mul_cancel₀ ha, one_smul]
    · intro u
      refine ⟨(eval a D)⁻¹ • L (R a u), ?_⟩
      have hc := LinearMap.congr_fun (hcomp a) u
      simpa only [map_smul, LinearMap.comp_apply, LinearMap.smul_apply,
        LinearMap.id_apply, smul_smul, inv_mul_cancel₀ ha, one_smul] using
        congrArg ((eval a D)⁻¹ • ·) hc
  · intro v hv
    rw [hfix a₀ v hv, hD₀, one_smul]

/-- The actual kernel product space has at least its witness dimension on a
principal open around a surjective witness. The kernel dimension itself is
constant there. -/
theorem kernelProduct_surjective_principal_open
    [FiniteDimensional K V] [FiniteDimensional K U]
    [FiniteDimensional K W] [FiniteDimensional K T]
    (B : V →ₗ[K] W →ₗ[K] T)
    (E : (ι → K) → (V →ₗ[K] U)) (hE : IsPolynomialFamily E)
    (a₀ : ι → K) (hsurj : Function.Surjective (E a₀)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → Function.Surjective (E a) ∧
        finrank K (LinearMap.ker (E a)) = finrank K (LinearMap.ker (E a₀)) ∧
        finrank K (kernelProductSpace B (LinearMap.ker (E a₀))) ≤
          finrank K (kernelProductSpace B (LinearMap.ker (E a))) := by
  obtain ⟨D₀, C, hC, hD₀, hker, hchart, hfix⟩ := polynomial_kernel_chart E hE a₀ hsurj
  have hD₀ne : eval a₀ D₀ ≠ 0 := by rw [hD₀]; exact one_ne_zero
  obtain ⟨D₁, hD₁, hprod⟩ := kernelProduct_range_polynomial_principal_open
    B E C hC hker a₀ (hchart a₀ hD₀ne).1
  refine ⟨D₀ * D₁, ?_, ?_⟩
  · simpa only [map_mul] using mul_ne_zero hD₀ne hD₁
  · intro a ha
    have hparts : eval a D₀ ≠ 0 ∧ eval a D₁ ≠ 0 := by
      simpa only [map_mul, mul_ne_zero_iff] using ha
    have hs := (hchart a hparts.1).2
    refine ⟨hs, ?_, hprod a hparts.2⟩
    have h₀ := LinearMap.finrank_range_add_finrank_ker (E a₀)
    have h₁ := LinearMap.finrank_range_add_finrank_ker (E a)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h₀
    rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h₁
    omega

end ChoppedPlane
