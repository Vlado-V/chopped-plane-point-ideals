module

public import Mathlib

@[expose] public section

/-!
# Polynomial parameter families and nonempty rank opens

Polynomial families of linear maps have locally persistent rank, and their
maximum rank is attained on a nonempty principal open. Finitely many nonempty
principal opens over an infinite field have a simultaneous point.

Adapted from the local project's `Quartic/PolynomialRankOpen.lean` and the
coordinate-functional helpers in `Quartic/Koszul.lean` and `GenericMatrix.lean`.
-/
noncomputable section
namespace ChoppedPlane
open Module MvPolynomial
variable {K ι V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup U] [Module K U]

/-- Independent vectors admit simultaneous coordinate functionals. -/
theorem exists_coordinate_functionals {r : ℕ} (q : Fin r → V)
    (hq : LinearIndependent K q) :
    ∃ dual : Fin r → V →ₗ[K] K, ∀ i j, dual i (q j) = if i = j then 1 else 0 := by
  classical
  obtain ⟨g, hg⟩ := (Finsupp.linearCombination K q).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hq)
  refine ⟨fun i => (Finsupp.lapply i).comp g, ?_⟩
  intro i j
  have h := LinearMap.congr_fun hg (Finsupp.single j 1)
  have hj : g (q j) = Finsupp.single j 1 := by simpa using h
  simp [hj, Finsupp.single_apply, eq_comm]

/-- A scalar linear function encoded as a polynomial in the parameters. -/
def polynomialOfLinear [Fintype ι] [DecidableEq ι]
    (L : (ι → K) →ₗ[K] K) : MvPolynomial ι K :=
  ∑ i, C (L (Pi.single i 1)) * X i

theorem eval_polynomialOfLinear [Fintype ι] [DecidableEq ι]
    (L : (ι → K) →ₗ[K] K) (a : ι → K) :
    eval a (polynomialOfLinear L) = L a := by
  have h := congrArg L ((Pi.basisFun K ι).sum_equivFun a)
  simpa [polynomialOfLinear, map_sum, Pi.basisFun_apply, Pi.basisFun_equivFun,
    smul_eq_mul, mul_comm] using h

/-- Every linear coordinate of the family is a polynomial in its parameters. -/
def IsPolynomialFamily (f : (ι → K) → V) : Prop :=
  ∀ ell : V →ₗ[K] K, ∃ p : MvPolynomial ι K, ∀ a, eval a p = ell (f a)

theorem isPolynomialFamily_const (v : V) : IsPolynomialFamily (fun _ : ι → K => v) := by
  intro ell
  exact ⟨C (ell v), by simp⟩

/-- Evaluating a fixed parameter polynomial gives a scalar polynomial family. -/
theorem isPolynomialFamily_eval (p : MvPolynomial ι K) :
    IsPolynomialFamily (fun a : ι → K => eval a p) := by
  intro ell
  refine ⟨C (ell 1) * p, fun a => ?_⟩
  simp [mul_comm]

/-- A single parameter coordinate is a polynomial family. -/
theorem isPolynomialFamily_coordinate (i : ι) :
    IsPolynomialFamily (fun a : ι → K => a i) := by
  simpa using isPolynomialFamily_eval (X i : MvPolynomial ι K)

theorem isPolynomialFamily_linear [Fintype ι] [DecidableEq ι] (f : (ι → K) →ₗ[K] V) : IsPolynomialFamily f := by
  intro ell
  exact ⟨polynomialOfLinear (ell.comp f), fun a => eval_polynomialOfLinear _ a⟩

theorem IsPolynomialFamily.linear_comp {f : (ι → K) → V}
    (hf : IsPolynomialFamily f) (L : V →ₗ[K] W) : IsPolynomialFamily (fun a => L (f a)) := by
  intro ell
  exact hf (ell.comp L)

theorem IsPolynomialFamily.add {f g : (ι → K) → V}
    (hf : IsPolynomialFamily f) (hg : IsPolynomialFamily g) :
    IsPolynomialFamily (fun a => f a + g a) := by
  intro ell
  obtain ⟨p, hp⟩ := hf ell
  obtain ⟨q, hq⟩ := hg ell
  exact ⟨p + q, fun a => by rw [map_add, hp, hq, map_add]⟩

theorem IsPolynomialFamily.smul {f : (ι → K) → K} {g : (ι → K) → V}
    (hf : IsPolynomialFamily f) (hg : IsPolynomialFamily g) :
    IsPolynomialFamily (fun a => f a • g a) := by
  intro ell
  obtain ⟨p, hp⟩ := hf LinearMap.id
  obtain ⟨q, hq⟩ := hg ell
  refine ⟨p * q, fun a => ?_⟩
  simp only [map_mul, hp, hq, LinearMap.id_apply, map_smul, smul_eq_mul]

theorem IsPolynomialFamily.sum {J : Type*} [Fintype J]
    {f : J → (ι → K) → V} (hf : ∀ j, IsPolynomialFamily (f j)) :
    IsPolynomialFamily (fun a => ∑ j, f j a) := by
  intro ell
  choose p hp using fun j => hf j ell
  refine ⟨∑ j, p j, fun a => ?_⟩
  simp only [map_sum, hp]

/-- Polynomial families are closed under any bilinear map between finite-dimensional spaces. -/
theorem IsPolynomialFamily.bilinear [FiniteDimensional K V]
    {f : (ι → K) → V} {g : (ι → K) → W}
    (hf : IsPolynomialFamily f) (hg : IsPolynomialFamily g) (B : V →ₗ[K] W →ₗ[K] U) :
    IsPolynomialFamily (fun a => B (f a) (g a)) := by
  let b := Module.finBasis K V
  have hterm (j : Fin (Module.finrank K V)) :
      IsPolynomialFamily (fun a => (b.repr (f a) j) • B (b j) (g a)) :=
    (hf.linear_comp (b.coord j)).smul (hg.linear_comp (B (b j)))
  have hsum := IsPolynomialFamily.sum hterm
  have heq : (fun a => ∑ j, b.repr (f a) j • B (b j) (g a)) =
      (fun a => B (f a) (g a)) := by
    funext a
    conv_rhs => rw [← b.sum_repr (f a)]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [heq] at hsum
  exact hsum

/-- Pairing polynomial families preserves polynomial dependence. -/
theorem IsPolynomialFamily.prod_mk {f : (ι → K) → V} {g : (ι → K) → W}
    (hf : IsPolynomialFamily f) (hg : IsPolynomialFamily g) :
    IsPolynomialFamily (fun a => (f a, g a)) := by
  have h := (hf.linear_comp (LinearMap.inl K V W)).add
    (hg.linear_comp (LinearMap.inr K V W))
  simpa only [LinearMap.inl_apply, LinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add] using h

/-- To prove polynomial dependence of a family of linear maps, it suffices
to check its application to each fixed input. -/
theorem isPolynomialFamily_linearMap [FiniteDimensional K V]
    (A : (ι → K) → (V →ₗ[K] W))
    (hA : ∀ x : V, IsPolynomialFamily (fun a => A a x)) : IsPolynomialFamily A := by
  let b := Module.finBasis K V
  let T (j : Fin (Module.finrank K V)) : W →ₗ[K] (V →ₗ[K] W) :=
    { toFun := LinearMap.smulRight (b.coord j)
      map_add' := by intro x y; ext v; simp [LinearMap.smulRight_apply, smul_add]
      map_smul' := by
        intro r x
        ext v
        change b.repr v j • (r • x) = r • (b.repr v j • x)
        exact smul_comm _ _ _ }
  have h := IsPolynomialFamily.sum (fun j => (hA (b j)).linear_comp (T j))
  have heq : (fun a => ∑ j, T j (A a (b j))) = A := by
    funext a
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply]
    change (∑ j, b.repr v j • A a (b j)) = A a v
    conv_rhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [heq] at h
  exact h

/-- A finite independent polynomial family stays independent on a determinant open. -/
theorem independent_polynomial_principal_open {r : ℕ}
    (q : Fin r → (ι → K) → V) (hqpoly : ∀ i, IsPolynomialFamily (q i))
    (a₀ : ι → K) (hq : LinearIndependent K (fun i => q i a₀)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → LinearIndependent K (fun i => q i a) := by
  classical
  obtain ⟨dual, hdual⟩ := exists_coordinate_functionals (fun i => q i a₀) hq
  choose p hp using fun i j => hqpoly j (dual i)
  let M : Matrix (Fin r) (Fin r) (MvPolynomial ι K) := p
  have heval (a : ι → K) : eval a M.det = (Matrix.of fun i j => dual i (q j a)).det := by
    rw [(eval a).map_det]
    congr 1
    ext i j
    exact hp i j a
  refine ⟨M.det, ?_, ?_⟩
  · rw [heval]
    have hM : (Matrix.of fun i j => dual i (q j a₀)) = (1 : Matrix (Fin r) (Fin r) K) := by
      ext i j
      simp [hdual, Matrix.one_apply]
    rw [hM, Matrix.det_one]
    exact one_ne_zero
  · intro a ha
    rw [heval] at ha
    let L : V →ₗ[K] (Fin r → K) := LinearMap.pi dual
    exact LinearIndependent.of_comp L (Matrix.linearIndependent_cols_of_det_ne_zero ha)

/-- A polynomial family of linear maps has at least its witness rank on a principal open. -/
theorem rank_polynomial_principal_open [FiniteDimensional K V] [FiniteDimensional K W]
    (A : (ι → K) → (V →ₗ[K] W)) (hA : IsPolynomialFamily A) (a₀ : ι → K) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      finrank K (LinearMap.range (A a₀)) ≤ finrank K (LinearMap.range (A a)) := by
  classical
  let R := LinearMap.range (A a₀)
  let b := Module.finBasis K R
  have hb : LinearIndependent K (fun i => (b i).val) :=
    b.linearIndependent.map' R.subtype (LinearMap.ker_eq_bot.mpr (Submodule.injective_subtype _))
  have hpre : ∀ i, ∃ x, A a₀ x = (b i).val := fun i => (b i).property
  choose x hx using hpre
  let q : Fin (finrank K R) → (ι → K) → W := fun i a => A a (x i)
  have hqpoly (i) : IsPolynomialFamily (q i) :=
    hA.linear_comp (LinearMap.applyₗ (R := K) (M₂ := W) (x i))
  have hq : LinearIndependent K (fun i => q i a₀) := by simpa only [q, hx] using hb
  obtain ⟨D, hD, hfamily⟩ := independent_polynomial_principal_open q hqpoly a₀ hq
  refine ⟨D, hD, ?_⟩
  intro a ha
  have hle : Submodule.span K (Set.range (fun i => q i a)) ≤ LinearMap.range (A a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨x i, rfl⟩
  have h := Submodule.finrank_mono hle
  rwa [finrank_span_eq_card (hfamily a ha), Fintype.card_fin] at h

/-- Injectivity at one parameter gives a nonempty determinant open of injective maps. -/
theorem injective_polynomial_principal_open [FiniteDimensional K V] [FiniteDimensional K W]
    (A : (ι → K) → (V →ₗ[K] W)) (hA : IsPolynomialFamily A) (a₀ : ι → K)
    (ha₀ : Function.Injective (A a₀)) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      Function.Injective (A a) := by
  obtain ⟨D, hD, h⟩ := rank_polynomial_principal_open A hA a₀
  refine ⟨D, hD, fun a ha => ?_⟩
  have hr := h a ha
  rw [LinearMap.finrank_range_of_inj ha₀] at hr
  have hk := LinearMap.finrank_range_add_finrank_ker (A a)
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- Every finite-dimensional family has a parameter attaining its largest rank. -/
theorem exists_maximum_rank [FiniteDimensional K W]
    (A : (ι → K) → (V →ₗ[K] W)) :
    ∃ a₀ : ι → K, ∀ a, finrank K (LinearMap.range (A a)) ≤
      finrank K (LinearMap.range (A a₀)) := by
  let ranks : Set ℕ := Set.range (fun a => finrank K (LinearMap.range (A a)))
  have hb : BddAbove ranks := by
    refine ⟨finrank K W, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact Submodule.finrank_le _
  have hn : ranks.Nonempty := ⟨_, ⟨fun _ => 0, rfl⟩⟩
  obtain ⟨r, hr, hmax⟩ := hb.exists_isGreatest_of_nonempty hn
  obtain ⟨a₀, rfl⟩ := hr
  exact ⟨a₀, fun a => hmax ⟨a, rfl⟩⟩

/-- A polynomial family has constant maximum rank on a nonempty principal open. -/
theorem maximum_rank_polynomial_principal_open [FiniteDimensional K V]
    [FiniteDimensional K W]
    (A : (ι → K) → (V →ₗ[K] W)) (hA : IsPolynomialFamily A) :
    ∃ (a₀ : ι → K) (D : MvPolynomial ι K),
      eval a₀ D ≠ 0 ∧
      (∀ a, finrank K (LinearMap.range (A a)) ≤
        finrank K (LinearMap.range (A a₀))) ∧
      (∀ a, eval a D ≠ 0 → finrank K (LinearMap.range (A a)) =
        finrank K (LinearMap.range (A a₀))) := by
  obtain ⟨a₀, hmax⟩ := exists_maximum_rank A
  obtain ⟨D, hD, hlow⟩ := rank_polynomial_principal_open A hA a₀
  exact ⟨a₀, D, hD, hmax, fun a ha => le_antisymm (hmax a) (hlow a ha)⟩

/-- Nonzero determinant polynomials have a simultaneous nonvanishing parameter. -/
theorem nonempty_principal_intersection [Infinite K] {J : Type*} [Fintype J]
    (D : J → MvPolynomial ι K) (hD : ∀ j, D j ≠ 0) :
    ∃ a : ι → K, ∀ j, eval a (D j) ≠ 0 := by
  classical
  have hp : (∏ j, D j) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hD j)
  by_contra h
  push Not at h
  apply hp
  apply MvPolynomial.funext
  intro a
  obtain ⟨j, hj⟩ := h a
  simp only [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ j) hj

/-- Finitely many principal-open conditions, possibly witnessed at different
points, can be imposed simultaneously over an infinite field. -/
theorem simultaneous_principal_properties [Infinite K] {J : Type*} [Fintype J]
    (P : J → (ι → K) → Prop)
    (hP : ∀ j, ∃ D : MvPolynomial ι K, (∃ a, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → P j a) :
    ∃ a : ι → K, ∀ j, P j a := by
  choose D hD hprop using hP
  have hne (j) : D j ≠ 0 := by
    obtain ⟨a, ha⟩ := hD j
    intro h
    simp [h] at ha
  obtain ⟨a, ha⟩ := nonempty_principal_intersection D hne
  exact ⟨a, fun j => hprop j a (ha j)⟩

/-- Finitely many polynomial map families achieve their maximum ranks on one
nonempty principal open over an infinite field. -/
theorem simultaneous_maximum_rank_principal_open [Infinite K]
    [FiniteDimensional K V] [FiniteDimensional K W]
    {J : Type*} [Fintype J]
    (A : J → (ι → K) → (V →ₗ[K] W)) (hA : ∀ j, IsPolynomialFamily (A j)) :
    ∃ D : MvPolynomial ι K, (∃ a, eval a D ≠ 0) ∧
      ∀ a, eval a D ≠ 0 → ∀ j b,
        finrank K (LinearMap.range (A j b)) ≤ finrank K (LinearMap.range (A j a)) := by
  classical
  choose a₀ D hD hmax heq using
    fun j => maximum_rank_polynomial_principal_open (A j) (hA j)
  have hne (j) : D j ≠ 0 := by
    intro hz
    simpa [hz] using hD j
  obtain ⟨a, ha⟩ := nonempty_principal_intersection D hne
  refine ⟨∏ j, D j, ⟨a, ?_⟩, ?_⟩
  · simpa only [map_prod] using
      Finset.prod_ne_zero_iff.mpr (fun j _ => ha j)
  · intro b hb j c
    have hj : eval b (D j) ≠ 0 := by
      rw [map_prod] at hb
      exact (Finset.prod_ne_zero_iff.mp hb) j (Finset.mem_univ j)
    rw [heq j b hj]
    exact hmax j c

end ChoppedPlane
