module

public import ChoppedPlane.GradedPresentation
public import ChoppedPlane.QWeylPullback
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

/-!
# Binary free modules for the cubic witness

The coefficient ring is the actual quotient
`K[u,v][z] / (z^3 - u^3 - v^3)`. Its action is constructed by evaluating
`z` at a cyclic endomorphism of the free binary-polynomial module. The dual
endomorphism is its literal transpose for the coefficientwise pairing.
Integer-graded pieces are genuine spaces of homogeneous binary polynomials.
-/

noncomputable section

namespace ChoppedPlane.QWeyl

open Module MvPolynomial

variable (K : Type*) [Field K]

abbrev BinaryRing := Poly K 2
abbrev BinaryVector := Fin 3 → BinaryRing K

def binaryU : BinaryRing K := X 0
def binaryV : BinaryRing K := X 1
def binaryCubic : BinaryRing K := binaryU K ^ 3 + binaryV K ^ 3

def cubicEquation : Polynomial (BinaryRing K) :=
  Polynomial.X ^ 3 - Polynomial.C (binaryCubic K)

abbrev CubicRing := Polynomial (BinaryRing K) ⧸ Ideal.span {cubicEquation K}

def cubicRoot : CubicRing K := Ideal.Quotient.mk _ Polynomial.X

def cubicCoefficient (b : BinaryRing K) : CubicRing K :=
  Ideal.Quotient.mk _ (Polynomial.C b)

variable {K}

variable {A : Type*} [CommRing A]

/-- Forward cyclic action: `z e_i = γ_i e_(i+1)`. -/
def cyclicZ (γ : Fin 3 → A) : (Fin 3 → A) →ₗ[A] (Fin 3 → A) where
  toFun m := ![γ 2 * m 2, γ 0 * m 0, γ 1 * m 1]
  map_add' m n := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' b m := by
    funext i
    fin_cases i <;> simp [mul_left_comm]

/-- Transpose cyclic action on the binary dual. -/
def cyclicZDual (γ : Fin 3 → A) : (Fin 3 → A) →ₗ[A] (Fin 3 → A) where
  toFun m := ![γ 0 * m 1, γ 1 * m 2, γ 2 * m 0]
  map_add' m n := by
    funext i
    fin_cases i <;> simp [mul_add]
  map_smul' b m := by
    funext i
    fin_cases i <;> simp [mul_left_comm]

theorem cyclicZ_cube (γ : Fin 3 → A) :
    cyclicZ γ ^ 3 = (γ 0 * γ 1 * γ 2) • (1 : Module.End A (Fin 3 → A)) := by
  ext m i
  fin_cases i <;> simp [cyclicZ, pow_succ, Module.End.mul_apply] <;> ring

theorem cyclicZDual_cube (γ : Fin 3 → A) :
    cyclicZDual γ ^ 3 = (γ 0 * γ 1 * γ 2) • (1 : Module.End A (Fin 3 → A)) := by
  ext m i
  fin_cases i <;> simp [cyclicZDual, pow_succ, Module.End.mul_apply] <;> ring

/-- The coefficientwise pairing identifies the second operator as the transpose. -/
theorem cyclic_pairing_transpose (γ : Fin 3 → A) (m d : Fin 3 → A) :
    (∑ i, cyclicZ γ m i * d i) = ∑ i, m i * cyclicZDual γ d i := by
  simp [Fin.sum_univ_succ, cyclicZ, cyclicZDual]
  ring

/-- The same construction over any commutative coefficient ring, including
the two binary localization charts. -/
def cyclicCubicEquation (F : A) : Polynomial A :=
  Polynomial.X ^ 3 - Polynomial.C F

abbrev CyclicCubicRing (A : Type*) [CommRing A] (F : A) :=
  Polynomial A ⧸ Ideal.span {cyclicCubicEquation F}

def cyclicRoot (F : A) : CyclicCubicRing A F := Ideal.Quotient.mk _ Polynomial.X

def cyclicCoefficientHom (F : A) : A →+* CyclicCubicRing A F :=
  (Ideal.Quotient.mk _).comp Polynomial.C

theorem cyclicRoot_cube (F : A) :
    cyclicRoot F ^ 3 = cyclicCoefficientHom F F := by
  have hmem : cyclicCubicEquation F ∈ Ideal.span {cyclicCubicEquation F} :=
    Ideal.subset_span (Set.mem_singleton _)
  have hz : Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation F})
      (cyclicCubicEquation F) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  apply sub_eq_zero.mp
  change (Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation F}) Polynomial.X) ^ 3 -
    Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation F}) (Polynomial.C F) = 0
  rw [← map_pow, ← map_sub]
  exact hz

def cyclicActionHom (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) : CyclicCubicRing A F →+* Module.End A (Fin 3 → A) :=
  Ideal.Quotient.lift _ (Polynomial.aeval Z).toRingHom (by
    change Ideal.span {cyclicCubicEquation F} ≤ RingHom.ker (Polynomial.aeval Z).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = cyclicCubicEquation F := Set.mem_singleton_iff.mp hp
    subst p
    change Polynomial.aeval Z (cyclicCubicEquation F) = 0
    simp [cyclicCubicEquation, hZ, Algebra.algebraMap_eq_smul_one])

@[simp] theorem cyclicActionHom_root (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) : cyclicActionHom F Z hZ (cyclicRoot F) = Z := by
  simp [cyclicActionHom, cyclicRoot]

@[simp] theorem cyclicActionHom_coefficient (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) (b : A) :
    cyclicActionHom F Z hZ (cyclicCoefficientHom F b) = b • 1 := by
  simp [cyclicActionHom, cyclicCoefficientHom, Algebra.algebraMap_eq_smul_one]

abbrev cyclicModuleStructure (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) : Module (CyclicCubicRing A F) (Fin 3 → A) :=
  Module.compHom _ (cyclicActionHom F Z hZ)

theorem cyclicModule_root_smul (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) :
    letI := cyclicModuleStructure F Z hZ
    ∀ m : Fin 3 → A, cyclicRoot F • m = Z m := by
  intro m
  change cyclicActionHom F Z hZ (cyclicRoot F) m = Z m
  rw [cyclicActionHom_root]

theorem cyclicModule_coefficient_smul (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) :
    letI := cyclicModuleStructure F Z hZ
    ∀ (b : A) (m : Fin 3 → A), cyclicCoefficientHom F b • m = b • m := by
  intro b m
  change cyclicActionHom F Z hZ (cyclicCoefficientHom F b) m = b • m
  rw [cyclicActionHom_coefficient]
  rfl

variable {A' : Type*} [CommRing A']

/-- Extension of coefficients on the actual cubic quotient rings. -/
def cyclicBaseChangeHom (φ : A →+* A') (F : A) :
    CyclicCubicRing A F →+* CyclicCubicRing A' (φ F) :=
  Ideal.Quotient.lift _
    ((Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation (φ F)})).comp
      (Polynomial.mapRingHom φ)) (by
    change Ideal.span {cyclicCubicEquation F} ≤ RingHom.ker _
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = cyclicCubicEquation F := Set.mem_singleton_iff.mp hp
    subst p
    have hmap : (Polynomial.mapRingHom φ) (cyclicCubicEquation F) =
        cyclicCubicEquation (φ F) := by simp [cyclicCubicEquation]
    change ((Ideal.Quotient.mk (Ideal.span {cyclicCubicEquation (φ F)})).comp
      (Polynomial.mapRingHom φ)) (cyclicCubicEquation F) = 0
    rw [RingHom.comp_apply, hmap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))

@[simp] theorem cyclicBaseChangeHom_root (φ : A →+* A') (F : A) :
    cyclicBaseChangeHom φ F (cyclicRoot F) = cyclicRoot (φ F) := by
  simp [cyclicBaseChangeHom, cyclicRoot]

@[simp] theorem cyclicBaseChangeHom_coefficient (φ : A →+* A') (F a : A) :
    cyclicBaseChangeHom φ F (cyclicCoefficientHom F a) =
      cyclicCoefficientHom (φ F) (φ a) := by
  simp [cyclicBaseChangeHom, cyclicCoefficientHom]

/-- Extension of coefficients in the free three-component module. -/
def cyclicVectorBaseChange (φ : A →+* A') : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A') where
  toFun m i := φ (m i)
  map_add' m n := by funext i; exact φ.map_add _ _
  map_smul' a m := by funext i; exact φ.map_mul _ _

@[simp] theorem cyclicVectorBaseChange_apply (φ : A →+* A') (m : Fin 3 → A)
    (i : Fin 3) : cyclicVectorBaseChange φ m i = φ (m i) := rfl

theorem cyclicZ_baseChange (φ : A →+* A') (γ : Fin 3 → A) (m : Fin 3 → A) :
    cyclicVectorBaseChange φ (cyclicZ γ m) =
      cyclicZ (fun i => φ (γ i)) (cyclicVectorBaseChange φ m) := by
  funext i
  fin_cases i <;> simp [cyclicZ, cyclicVectorBaseChange]

theorem cyclicZDual_baseChange (φ : A →+* A') (γ : Fin 3 → A) (m : Fin 3 → A) :
    cyclicVectorBaseChange φ (cyclicZDual γ m) =
      cyclicZDual (fun i => φ (γ i)) (cyclicVectorBaseChange φ m) := by
  funext i
  fin_cases i <;> simp [cyclicZDual, cyclicVectorBaseChange]

/-- Semilinear coefficient extension commutes with evaluation at compatible
endomorphisms, including every polynomial in the cubic root. -/
theorem semilinear_polynomial_aeval
    (φ : A →+* A') (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hT : ∀ m, T (Z m) = Z' (T m)) (p : Polynomial A) (m : Fin 3 → A) :
    T (Polynomial.aeval Z p m) = Polynomial.aeval Z' (p.map φ) (T m) := by
  have hpow (n : ℕ) (v : Fin 3 → A) : T ((Z ^ n) v) = (Z' ^ n) (T v) := by
    induction n generalizing v with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih, hT,
        ← Module.End.mul_apply, ← pow_succ]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Polynomial.map_add, LinearMap.add_apply, hp, hq]
  | monomial n a =>
    simp [Polynomial.aeval_monomial,
      Algebra.algebraMap_eq_smul_one, hpow]

/-- The genuine quotient-ring actions commute with coefficient extension. -/
theorem cyclicActionHom_baseChange
    (φ : A →+* A') (F : A)
    (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hZ : Z ^ 3 = F • 1) (hZ' : Z' ^ 3 = φ F • 1)
    (hT : ∀ m, T (Z m) = Z' (T m))
    (r : CyclicCubicRing A F) (m : Fin 3 → A) :
    T (cyclicActionHom F Z hZ r m) =
      cyclicActionHom (φ F) Z' hZ' (cyclicBaseChangeHom φ F r) (T m) := by
  refine Quotient.inductionOn' r ?_
  intro p
  change T (Polynomial.aeval Z p m) =
    Polynomial.aeval Z' (p.map φ) (T m)
  exact semilinear_polynomial_aeval φ T Z Z' hT p m

/-- A compatible semilinear coefficient map is semilinear for the actual
cubic quotient-ring actions. -/
def cyclicModuleBaseChange
    (φ : A →+* A') (F : A)
    (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hZ : Z ^ 3 = F • 1) (hZ' : Z' ^ 3 = φ F • 1)
    (hT : ∀ m, T (Z m) = Z' (T m)) :
    letI := cyclicModuleStructure F Z hZ
    letI := cyclicModuleStructure (φ F) Z' hZ'
    (Fin 3 → A) →ₛₗ[cyclicBaseChangeHom φ F] (Fin 3 → A') := by
  letI := cyclicModuleStructure F Z hZ
  letI := cyclicModuleStructure (φ F) Z' hZ'
  exact
    { toFun := T
      map_add' := T.map_add
      map_smul' := fun r m => cyclicActionHom_baseChange φ F T Z Z' hZ hZ' hT r m }

@[simp] theorem cyclicModuleBaseChange_apply
    (φ : A →+* A') (F : A)
    (T : (Fin 3 → A) →ₛₗ[φ] (Fin 3 → A'))
    (Z : Module.End A (Fin 3 → A)) (Z' : Module.End A' (Fin 3 → A'))
    (hZ : Z ^ 3 = F • 1) (hZ' : Z' ^ 3 = φ F • 1)
    (hT : ∀ m, T (Z m) = Z' (T m)) (m : Fin 3 → A) :
    cyclicModuleBaseChange φ F T Z Z' hZ hZ' hT m = T m := rfl

/-- A cubic endomorphism defines an action of the commutative quotient ring. -/
def cubicActionHom (Z : Module.End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = binaryCubic K • 1) :
    CubicRing K →+* Module.End (BinaryRing K) (BinaryVector K) :=
  Ideal.Quotient.lift _ (Polynomial.aeval Z).toRingHom (by
    change Ideal.span {cubicEquation K} ≤ RingHom.ker (Polynomial.aeval Z).toRingHom
    apply Ideal.span_le.mpr
    intro p hp
    have hp' : p = cubicEquation K := Set.mem_singleton_iff.mp hp
    subst p
    change Polynomial.aeval Z (cubicEquation K) = 0
    simp [cubicEquation, hZ, Algebra.algebraMap_eq_smul_one])

@[simp] theorem cubicActionHom_root
    (Z : Module.End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = binaryCubic K • 1) :
    cubicActionHom Z hZ (cubicRoot K) = Z := by
  simp [cubicActionHom, cubicRoot]

@[simp] theorem cubicActionHom_coefficient
    (Z : Module.End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = binaryCubic K • 1) (b : BinaryRing K) :
    cubicActionHom Z hZ (cubicCoefficient K b) = b • 1 := by
  simp [cubicActionHom, cubicCoefficient, Algebra.algebraMap_eq_smul_one]

/-- This is an actual module structure; callers install it locally for the
chosen cyclic factors, so distinct profiles do not create conflicting instances. -/
abbrev cubicModuleStructure (Z : Module.End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = binaryCubic K • 1) : Module (CubicRing K) (BinaryVector K) :=
  Module.compHom _ (cubicActionHom Z hZ)

theorem cubicModule_root_smul
    (Z : Module.End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = binaryCubic K • 1) :
    letI := cubicModuleStructure Z hZ
    ∀ m : BinaryVector K, cubicRoot K • m = Z m := by
  intro m
  change cubicActionHom Z hZ (cubicRoot K) m = Z m
  rw [cubicActionHom_root]

theorem cubicModule_coefficient_smul
    (Z : Module.End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = binaryCubic K • 1) :
    letI := cubicModuleStructure Z hZ
    ∀ (b : BinaryRing K) (m : BinaryVector K), cubicCoefficient K b • m = b • m := by
  intro b m
  change cubicActionHom Z hZ (cubicCoefficient K b) m = b • m
  rw [cubicActionHom_coefficient]
  rfl

/-- The three initial dimensions: three, two, or one. -/
inductive CubicProfile where
  | degreeThree
  | degreeTwo
  | degreeOne
  deriving DecidableEq

def generatorWeights : CubicProfile → Fin 3 → ℕ
  | .degreeThree => ![0, 0, 0]
  | .degreeTwo => ![0, 0, 1]
  | .degreeOne => ![0, 1, 1]

def dualGeneratorWeights (s : CubicProfile) : Fin 3 → ℕ :=
  fun i => 2 - generatorWeights s i

def cubicLinearFactors (q : K) : Fin 3 → BinaryRing K :=
  ![binaryU K + binaryV K,
    binaryU K + C q * binaryV K,
    binaryU K + C (q ^ 2) * binaryV K]

def profileFactors (q : K) : CubicProfile → Fin 3 → BinaryRing K
  | .degreeThree => cubicLinearFactors q
  | .degreeTwo => ![cubicLinearFactors q 0, 1,
      cubicLinearFactors q 1 * cubicLinearFactors q 2]
  | .degreeOne => ![1, cubicLinearFactors q 1,
      cubicLinearFactors q 0 * cubicLinearFactors q 2]

theorem cubicLinearFactors_product (q : K) (hq : q ^ 2 + q + 1 = 0) :
    cubicLinearFactors q 0 * cubicLinearFactors q 1 * cubicLinearFactors q 2 =
      binaryCubic K := by
  have hq' : (C q : BinaryRing K) ^ 2 + C q + 1 = 0 := by
    simpa using congrArg (C : K →+* BinaryRing K) hq
  have h := binary_cubic_factor (binaryU K) (-binaryV K) (C q) hq'
  change (binaryU K + binaryV K) * (binaryU K + C q * binaryV K) *
    (binaryU K + C (q ^ 2) * binaryV K) = binaryU K ^ 3 + binaryV K ^ 3
  rw [map_pow]
  convert h using 1 <;> ring

theorem profileFactors_product (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    profileFactors q s 0 * profileFactors q s 1 * profileFactors q s 2 =
      binaryCubic K := by
  have h := cubicLinearFactors_product q hq
  cases s with
  | degreeThree => exact h
  | degreeTwo =>
    change cubicLinearFactors q 0 * 1 *
      (cubicLinearFactors q 1 * cubicLinearFactors q 2) = _
    simpa only [mul_one, mul_assoc] using h
  | degreeOne =>
    change 1 * cubicLinearFactors q 1 *
      (cubicLinearFactors q 0 * cubicLinearFactors q 2) = _
    calc
      _ = cubicLinearFactors q 0 * cubicLinearFactors q 1 * cubicLinearFactors q 2 := by ring
      _ = _ := h

theorem profileZ_cube (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    cyclicZ (profileFactors q s) ^ 3 = binaryCubic K • 1 := by
  rw [cyclicZ_cube, profileFactors_product q hq]

theorem profileZDual_cube (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    cyclicZDual (profileFactors q s) ^ 3 = binaryCubic K • 1 := by
  rw [cyclicZDual_cube, profileFactors_product q hq]

/-- Genuine homogeneous components of the binary free module with shifts. -/
abbrev GradedBinaryVector (w : Fin 3 → ℕ) (t : ℤ) :=
  ∀ i : Fin 3, signedForms K 2 (t - w i)

def gradedBinaryVectorVal (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t →ₗ[K] BinaryVector K where
  toFun m i := (m i).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem gradedBinaryVectorVal_injective (w : Fin 3 → ℕ) (t : ℤ) :
    Function.Injective (gradedBinaryVectorVal (K := K) w t) := by
  intro m n h
  funext i
  apply Subtype.ext
  exact congrFun h i

end ChoppedPlane.QWeyl
