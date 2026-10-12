module

public import ChoppedPlane.QWeylModule

@[expose] public section

/-! Explicit semilinear quartic pullback of the cyclic cubic modules. -/

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial

variable {A A' : Type*} [CommRing A] [CommRing A']

/-- Componentwise extension followed by fixed component multipliers. -/
def weightedVectorBaseChange (φ : A →+* A') (ρ : Fin 3 → A') :
    (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A') where
  toFun m i := φ (m i) * ρ i
  map_add' m n := by funext i; simp [add_mul]
  map_smul' a m := by funext i; simp [mul_assoc]

@[simp] theorem weightedVectorBaseChange_apply (φ : A →+* A')
    (ρ : Fin 3 → A') (m : Fin 3 → A) (i : Fin 3) :
    weightedVectorBaseChange φ ρ m i = φ (m i) * ρ i := rfl

theorem weightedVectorBaseChange_injective [IsDomain A']
    (φ : A →+* A') (hφ : Function.Injective φ) (ρ : Fin 3 → A')
    (hρ : ∀ i, ρ i ≠ 0) : Function.Injective (weightedVectorBaseChange φ ρ) := by
  intro m n h
  funext i
  apply hφ
  exact mul_right_cancel₀ (hρ i) (congrFun h i)

/-- Next component in the cyclic order. -/
def cyclicNext : Fin 3 → Fin 3 := ![1, 2, 0]

theorem weightedVectorBaseChange_cyclicZ
    (φ : A →+* A') (γ : Fin 3 → A) (γ' ρ : Fin 3 → A') (H : A')
    (h : ∀ i, φ (γ i) * ρ (cyclicNext i) = H * γ' i * ρ i)
    (m : Fin 3 → A) :
    weightedVectorBaseChange φ ρ (cyclicZ γ m) =
      H • cyclicZ γ' (weightedVectorBaseChange φ ρ m) := by
  funext i
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change φ (γ 0) * ρ 1 = H * γ' 0 * ρ 0 at h0
  change φ (γ 1) * ρ 2 = H * γ' 1 * ρ 1 at h1
  change φ (γ 2) * ρ 0 = H * γ' 2 * ρ 2 at h2
  fin_cases i
  · change φ (γ 2 * m 2) * ρ 0 = H * (γ' 2 * (φ (m 2) * ρ 2))
    rw [map_mul]
    calc
      _ = (φ (γ 2) * ρ 0) * φ (m 2) := by ring
      _ = _ := by rw [h2]; ring
  · change φ (γ 0 * m 0) * ρ 1 = H * (γ' 0 * (φ (m 0) * ρ 0))
    rw [map_mul]
    calc
      _ = (φ (γ 0) * ρ 1) * φ (m 0) := by ring
      _ = _ := by rw [h0]; ring
  · change φ (γ 1 * m 1) * ρ 2 = H * (γ' 1 * (φ (m 1) * ρ 1))
    rw [map_mul]
    calc
      _ = (φ (γ 1) * ρ 2) * φ (m 1) := by ring
      _ = _ := by rw [h1]; ring

theorem weightedVectorBaseChange_cyclicZDual
    (φ : A →+* A') (γ : Fin 3 → A) (γ' ρ : Fin 3 → A') (H : A')
    (h : ∀ i, φ (γ i) * ρ i = H * γ' i * ρ (cyclicNext i))
    (m : Fin 3 → A) :
    weightedVectorBaseChange φ ρ (cyclicZDual γ m) =
      H • cyclicZDual γ' (weightedVectorBaseChange φ ρ m) := by
  funext i
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  change φ (γ 0) * ρ 0 = H * γ' 0 * ρ 1 at h0
  change φ (γ 1) * ρ 1 = H * γ' 1 * ρ 2 at h1
  change φ (γ 2) * ρ 2 = H * γ' 2 * ρ 0 at h2
  fin_cases i
  · change φ (γ 0 * m 1) * ρ 0 = H * (γ' 0 * (φ (m 1) * ρ 1))
    rw [map_mul]
    calc
      _ = (φ (γ 0) * ρ 0) * φ (m 1) := by ring
      _ = _ := by rw [h0]; ring
  · change φ (γ 1 * m 2) * ρ 1 = H * (γ' 1 * (φ (m 2) * ρ 2))
    rw [map_mul]
    calc
      _ = (φ (γ 1) * ρ 1) * φ (m 2) := by ring
      _ = _ := by rw [h1]; ring
  · change φ (γ 2 * m 0) * ρ 2 = H * (γ' 2 * (φ (m 0) * ρ 0))
    rw [map_mul]
    calc
      _ = (φ (γ 2) * ρ 2) * φ (m 0) := by ring
      _ = _ := by rw [h2]; ring

/-- Coefficient extension which multiplies the cubic root by `H`. -/
def cyclicScaledBaseChangeHom (φ : A →+* A') (F : A) (F' H : A')
    (hF : φ F = F' * H ^ 3) :
    CyclicCubicRing A F →+* CyclicCubicRing A' F' :=
  Ideal.Quotient.lift _
    (Polynomial.eval₂RingHom ((cyclicCoefficientHom F').comp φ)
      (cyclicCoefficientHom F' H * cyclicRoot F')) (by
      change Ideal.span {cyclicCubicEquation F} ≤ RingHom.ker _
      apply Ideal.span_le.mpr
      intro p hp
      have hp' : p = cyclicCubicEquation F := Set.mem_singleton_iff.mp hp
      subst p
      change Polynomial.eval₂ ((cyclicCoefficientHom F').comp φ)
        (cyclicCoefficientHom F' H * cyclicRoot F') (cyclicCubicEquation F) = 0
      simp only [cyclicCubicEquation, Polynomial.eval₂_sub,
        Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        RingHom.comp_apply]
      rw [mul_pow, cyclicRoot_cube, hF, map_mul, map_pow]
      ring)

@[simp] theorem cyclicScaledBaseChangeHom_root (φ : A →+* A') (F : A) (F' H : A')
    (hF : φ F = F' * H ^ 3) :
    cyclicScaledBaseChangeHom φ F F' H hF (cyclicRoot F) =
      cyclicCoefficientHom F' H * cyclicRoot F' := by
  simp [cyclicScaledBaseChangeHom, cyclicRoot]

@[simp] theorem cyclicScaledBaseChangeHom_coefficient
    (φ : A →+* A') (F : A) (F' H : A') (hF : φ F = F' * H ^ 3) (a : A) :
    cyclicScaledBaseChangeHom φ F F' H hF (cyclicCoefficientHom F a) =
      cyclicCoefficientHom F' (φ a) := by
  simp [cyclicScaledBaseChangeHom, cyclicCoefficientHom]

/-- Polynomial evaluation after the scaled extension is evaluation at the
scaled endomorphism. -/
theorem cyclicActionHom_scaledBaseChange_polynomial
    (φ : A →+* A') (F : A) (F' H : A') (hF : φ F = F' * H ^ 3)
    (Z' : Module.End A' (Fin 3 → A')) (hZ' : Z' ^ 3 = F' • 1)
    (p : Polynomial A) :
    cyclicActionHom F' Z' hZ'
      (cyclicScaledBaseChangeHom φ F F' H hF
        (Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation F}) p)) =
      Polynomial.aeval (H • Z') (p.map φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.map_add, hp, hq]
  | monomial n a =>
    simp [cyclicScaledBaseChangeHom, Polynomial.aeval_monomial,
      cyclicActionHom_coefficient, cyclicActionHom_root,
      Algebra.algebraMap_eq_smul_one]

/-- The weighted coefficient map intertwines the genuine cubic actions. -/
theorem cyclicActionHom_scaledBaseChange
    (φ : A →+* A') (F : A) (F' H : A') (hF : φ F = F' * H ^ 3)
    (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hZ : Z ^ 3 = F • 1) (hZ' : Z' ^ 3 = F' • 1)
    (hT : ∀ m, T (Z m) = H • Z' (T m))
    (r : CyclicCubicRing A F) (m : Fin 3 → A) :
    T (cyclicActionHom F Z hZ r m) =
      cyclicActionHom F' Z' hZ' (cyclicScaledBaseChangeHom φ F F' H hF r) (T m) := by
  refine Quotient.inductionOn' r ?_
  intro p
  change T (cyclicActionHom F Z hZ
    (Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation F}) p) m) =
    cyclicActionHom F' Z' hZ' (cyclicScaledBaseChangeHom φ F F' H hF
      (Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation F}) p)) (T m)
  rw [cyclicActionHom_scaledBaseChange_polynomial]
  change T (Polynomial.aeval Z p m) = Polynomial.aeval (H • Z') (p.map φ) (T m)
  exact semilinear_polynomial_aeval φ T Z (H • Z') hT p m

/-- Bundled semilinear pullback for the actual cubic-module structures. -/
def cyclicModuleScaledBaseChange
    (φ : A →+* A') (F : A) (F' H : A') (hF : φ F = F' * H ^ 3)
    (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hZ : Z ^ 3 = F • 1) (hZ' : Z' ^ 3 = F' • 1)
    (hT : ∀ m, T (Z m) = H • Z' (T m)) :
    letI := cyclicModuleStructure F Z hZ
    letI := cyclicModuleStructure F' Z' hZ'
    (Fin 3 → A) →ₛₗ[cyclicScaledBaseChangeHom φ F F' H hF] (Fin 3 → A') := by
  letI := cyclicModuleStructure F Z hZ
  letI := cyclicModuleStructure F' Z' hZ'
  exact
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun r m =>
        cyclicActionHom_scaledBaseChange φ F F' H hF T Z Z' hZ hZ' hT r m }

@[simp] theorem cyclicModuleScaledBaseChange_apply
    (φ : A →+* A') (F : A) (F' H : A') (hF : φ F = F' * H ^ 3)
    (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hZ : Z ^ 3 = F • 1) (hZ' : Z' ^ 3 = F' • 1)
    (hT : ∀ m, T (Z m) = H • Z' (T m)) (m : Fin 3 → A) :
    cyclicModuleScaledBaseChange φ F F' H hF T Z Z' hZ hZ' hT m = T m := rfl

/-- Cyclic factors over any commutative coefficient ring. -/
def cyclicProfileCoefficients (u v q : A) : CubicProfile → Fin 3 → A
  | .degreeThree => ![u + v, u + q * v, u + q ^ 2 * v]
  | .degreeTwo => ![u + v, 1, (u + q * v) * (u + q ^ 2 * v)]
  | .degreeOne => ![1, u + q * v, (u + v) * (u + q ^ 2 * v)]

/-- Multipliers for the three possible shifted modules. -/
def profilePullbackWeights (u v q : A) : CubicProfile → Fin 3 → A
  | .degreeThree => ![weightZero u v q, weightOne u v q, weightTwo u v q]
  | .degreeTwo => ![(u-v)^2, (u-q*v)*(u-q^2*v),
      (u-q^2*v)^2*(u-v)*(u-q*v)^2]
  | .degreeOne => ![u-q*v, (u-v)*(u-q*v)^2*(u-q^2*v),
      (u-v)^2*(u-q^2*v)^2]

/-- Multipliers for the literal transpose modules. -/
def profileDualPullbackWeights (u v q : A) : CubicProfile → Fin 3 → A
  | .degreeThree => ![(u-q*v)*(u-q^2*v)^2, (u-q^2*v)*(u-v)^2,
      (u-v)*(u-q*v)^2]
  | .degreeTwo => ![(u-q*v)^2*(u-q^2*v)^2,
      (u-q*v)*(u-q^2*v)*(u-v)^2, u-v]
  | .degreeOne => ![(u-v)^2*(u-q*v)*(u-q^2*v)^2,
      (u-v)*(u-q^2*v), (u-q*v)^2]

theorem profilePullbackWeights_intertwine (u v q : A) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (i : Fin 3) :
    cyclicProfileCoefficients (quarticU u v) (quarticV u v) q s i *
      profilePullbackWeights u v q s (cyclicNext i) =
    (u ^ 3 - v ^ 3) * cyclicProfileCoefficients u v q s i *
      profilePullbackWeights u v q s i := by
  cases s with
  | degreeThree =>
    fin_cases i
    · change (quarticU u v + quarticV u v) * weightOne u v q =
        (u ^ 3 - v ^ 3) * (u+v) * weightZero u v q
      convert (intertwiner_zero u v q hq).symm using 1 <;> ring
    · change (quarticU u v + q * quarticV u v) * weightTwo u v q =
        (u ^ 3 - v ^ 3) * (u+q*v) * weightOne u v q
      convert (intertwiner_one u v q hq).symm using 1 <;> ring
    · change (quarticU u v + q^2 * quarticV u v) * weightZero u v q =
        (u ^ 3 - v ^ 3) * (u+q^2*v) * weightTwo u v q
      convert (intertwiner_two u v q hq).symm using 1 <;> ring
  | degreeTwo =>
    have h := shifted_two_intertwiners u v q hq
    dsimp at h
    fin_cases i
    · convert h.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profilePullbackWeights, cyclicNext] <;> ring
    · convert h.2.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profilePullbackWeights, cyclicNext] <;> ring
    · convert h.2.2.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profilePullbackWeights, cyclicNext] <;> ring
  | degreeOne =>
    have h := shifted_one_intertwiners u v q hq
    dsimp at h
    fin_cases i
    · convert h.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profilePullbackWeights, cyclicNext] <;> ring
    · convert h.2.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profilePullbackWeights, cyclicNext] <;> ring
    · convert h.2.2.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profilePullbackWeights, cyclicNext] <;> ring

theorem profileDualPullbackWeights_intertwine (u v q : A) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (i : Fin 3) :
    cyclicProfileCoefficients (quarticU u v) (quarticV u v) q s i *
      profileDualPullbackWeights u v q s i =
    (u ^ 3 - v ^ 3) * cyclicProfileCoefficients u v q s i *
      profileDualPullbackWeights u v q s (cyclicNext i) := by
  cases s with
  | degreeThree =>
    have h := dual_intertwiners u v q hq
    dsimp at h
    fin_cases i
    · convert h.2.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
    · convert h.2.2.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
    · convert h.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
  | degreeTwo =>
    have h := shifted_two_dual_intertwiners u v q hq
    dsimp at h
    fin_cases i
    · convert h.2.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
    · convert h.2.2.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
    · convert h.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
  | degreeOne =>
    have h := shifted_one_dual_intertwiners u v q hq
    dsimp at h
    fin_cases i
    · convert h.2.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
    · convert h.2.2.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring
    · convert h.1.symm using 1 <;>
        dsimp [cyclicProfileCoefficients, profileDualPullbackWeights, cyclicNext] <;> ring

end ChoppedPlane.QWeyl
