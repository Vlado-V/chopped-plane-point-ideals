module

public import ChoppedPlane.QWeylGrading
public import ChoppedPlane.QuarticKernelCoordinates

@[expose] public section

/-! The actual symmetric quadratic kernel vectors have weighted binary
degree twice their auxiliary degree, in each of the six cyclic modules. -/

set_option maxHeartbeats 600000

noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
open scoped TensorProduct

variable {K : Type*} [Field K]

/-- Membership in the genuine shifted binary component. -/
def WeightedVector (w : Fin 3 → ℕ) (t : ℤ) (m : BinaryVector K) : Prop :=
  ∀ i, m i ∈ signedForms K 2 (t - w i)

theorem weightedVector_zero (w : Fin 3 → ℕ) (t : ℤ) :
    WeightedVector (K := K) w t 0 := by
  intro i
  exact (signedForms K 2 _).zero_mem

theorem weightedVector_add {w : Fin 3 → ℕ} {t : ℤ} {m n : BinaryVector K}
    (hm : WeightedVector w t m) (hn : WeightedVector w t n) :
    WeightedVector w t (m + n) := by
  intro i
  exact (signedForms K 2 _).add_mem (hm i) (hn i)

theorem weightedVector_neg {w : Fin 3 → ℕ} {t : ℤ} {m : BinaryVector K}
    (hm : WeightedVector w t m) : WeightedVector w t (-m) := by
  intro i
  exact (signedForms K 2 _).neg_mem (hm i)

theorem weightedVector_sum {ι : Type*} (s : Finset ι) {w : Fin 3 → ℕ} {t : ℤ}
    {m : ι → BinaryVector K} (hm : ∀ i ∈ s, WeightedVector w t (m i)) :
    WeightedVector w t (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weightedVector_zero w t
  | @insert i s hi hs =>
    rw [Finset.sum_insert hi]
    exact weightedVector_add (hm i (Finset.mem_insert_self i s))
      (hs (fun j hj => hm j (Finset.mem_insert_of_mem hj)))

theorem weightedVector_binary_smul {w : Fin 3 → ℕ} {t : ℤ} {d : ℕ}
    {b : BinaryRing K} {m : BinaryVector K}
    (hb : b.IsHomogeneous d) (hm : WeightedVector w t m) :
    WeightedVector w (t + d) (b • m) := by
  intro i
  change b * m i ∈ signedForms K 2 (t + d - w i)
  have h := homogeneous_mul_mem_signedForms hb (hm i)
  convert h using 1
  congr 1
  omega

theorem weightedVector_profileZ (q : K) (s : CubicProfile) {t : ℤ}
    {m : BinaryVector K} (hm : WeightedVector (generatorWeights s) t m) :
    WeightedVector (generatorWeights s) (t + 1) (cyclicZ (profileFactors q s) m) := by
  let m' : GradedBinaryVector (K := K) (generatorWeights s) t := fun i => ⟨m i, hm i⟩
  intro i
  exact (gradedProfileZ q s t m' i).property

theorem weightedVector_profileZDual (q : K) (s : CubicProfile) {t : ℤ}
    {m : BinaryVector K} (hm : WeightedVector (dualGeneratorWeights s) t m) :
    WeightedVector (dualGeneratorWeights s) (t + 1)
      (cyclicZDual (profileFactors q s) m) := by
  let m' : GradedBinaryVector (K := K) (dualGeneratorWeights s) t := fun i => ⟨m i, hm i⟩
  intro i
  exact (gradedProfileZDual q s t m' i).property

section CubicAction
variable (F : BinaryRing K) (Z : End (BinaryRing K) (BinaryVector K))
  (hZ : Z ^ 3 = F • 1)
variable [Module (CyclicCubicRing (BinaryRing K) F) (BinaryVector K)]
  (hcoeff : ∀ (b : BinaryRing K) (m : BinaryVector K), cyclicCoefficientHom F b • m = b • m)
  (hroot : ∀ (m : BinaryVector K), cyclicRoot F • m = Z m)

/-- A scalar has degree `d` when it raises every shifted binary component by `d`. -/
def WeightedScalar (w : Fin 3 → ℕ) (d : ℤ) (r : CyclicCubicRing (BinaryRing K) F) : Prop :=
  ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m → WeightedVector w (t + d) (r • m)

theorem weightedScalar_zero (w : Fin 3 → ℕ) (d : ℤ) :
    WeightedScalar F w d 0 := by
  intro t m hm
  rw [Module.zero_smul (R := CyclicCubicRing (BinaryRing K) F) m]
  exact weightedVector_zero w (t + d)

theorem weightedScalar_add {w : Fin 3 → ℕ} {d : ℤ} {r s : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) (hs : WeightedScalar F w d s) :
    WeightedScalar F w d (r + s) := by
  intro t m hm
  rw [add_smul]
  exact weightedVector_add (hr t m hm) (hs t m hm)

theorem weightedScalar_neg {w : Fin 3 → ℕ} {d : ℤ} {r : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) : WeightedScalar F w d (-r) := by
  intro t m hm
  rw [neg_smul]
  exact weightedVector_neg (hr t m hm)

theorem weightedScalar_one (w : Fin 3 → ℕ) : WeightedScalar F w 0 1 := by
  intro t m hm
  simpa using hm

theorem weightedScalar_mul {w : Fin 3 → ℕ} {d e : ℤ} {r s : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) (hs : WeightedScalar F w e s) :
    WeightedScalar F w (d + e) (r * s) := by
  intro t m hm
  rw [mul_smul]
  have h := hr (t + e) (s • m) (hs t m hm)
  simpa only [add_assoc, add_comm, add_left_comm] using h

theorem weightedScalar_sum {ι : Type*} (s : Finset ι) {w : Fin 3 → ℕ} {d : ℤ}
    {r : ι → CyclicCubicRing (BinaryRing K) F} (hr : ∀ i ∈ s, WeightedScalar F w d (r i)) :
    WeightedScalar F w d (∑ i ∈ s, r i) := by
  intro t m hm
  rw [Finset.sum_smul]
  exact weightedVector_sum s (fun i hi => hr i hi t m hm)

theorem weightedScalar_pow {w : Fin 3 → ℕ} {d : ℤ} {r : CyclicCubicRing (BinaryRing K) F}
    (hr : WeightedScalar F w d r) (n : ℕ) :
    WeightedScalar F w (n * d) (r ^ n) := by
  induction n with
  | zero => simpa using weightedScalar_one F w
  | succ n ih =>
    rw [pow_succ]
    convert weightedScalar_mul F ih hr using 1
    push_cast
    ring

include hcoeff in
theorem weightedScalar_coefficient {w : Fin 3 → ℕ} {d : ℕ} {b : BinaryRing K}
    (hb : b.IsHomogeneous d) :
    WeightedScalar F w d (cyclicCoefficientHom F b) := by
  intro t m hm
  rw [hcoeff]
  exact weightedVector_binary_smul hb hm

include hroot in
theorem weightedScalar_root (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) :
    WeightedScalar F w 1 (cyclicRoot F) := by
  intro t m hm
  rw [hroot]
  exact hgraded t m hm

/-- Every coefficient of an auxiliary polynomial has the given binary action degree. -/
def WeightedPolynomial (w : Fin 3 → ℕ) (d : ℤ) (p : Aux (CyclicCubicRing (BinaryRing K) F)) : Prop :=
  ∀ α, WeightedScalar F w d (p.coeff α)

theorem weightedPolynomial_mul {w : Fin 3 → ℕ} {d e : ℤ} {p q : Aux (CyclicCubicRing (BinaryRing K) F)}
    (hp : WeightedPolynomial F w d p) (hq : WeightedPolynomial F w e q) :
    WeightedPolynomial F w (d + e) (p * q) := by
  intro α
  classical
  rw [coeff_mul]
  exact weightedScalar_sum F _
    (fun x _ => weightedScalar_mul F (hp x.1) (hq x.2))

theorem weightedPolynomial_one (w : Fin 3 → ℕ) :
    WeightedPolynomial F w 0 1 := by
  intro α
  classical
  by_cases h : α = 0
  · subst α
    simpa using weightedScalar_one F w
  · simpa [coeff_one, h, Ne.symm h] using weightedScalar_zero F w 0

theorem weightedPolynomial_pow {w : Fin 3 → ℕ} {d : ℤ} {p : Aux (CyclicCubicRing (BinaryRing K) F)}
    (hp : WeightedPolynomial F w d p) (n : ℕ) :
    WeightedPolynomial F w (n * d) (p ^ n) := by
  induction n with
  | zero => simpa using weightedPolynomial_one F w
  | succ n ih =>
    rw [pow_succ]
    convert weightedPolynomial_mul F ih hp using 1
    push_cast
    ring

theorem weightedPolynomial_linearForm {w : Fin 3 → ℕ} {d : ℤ} {a : Fin 3 → CyclicCubicRing (BinaryRing K) F}
    (ha : ∀ i, WeightedScalar F w d (a i)) :
    WeightedPolynomial F w d (linearForm a) := by
  intro α
  classical
  simp only [linearForm, coeff_sum]
  apply weightedScalar_sum F
  intro i _
  rw [C_mul_X_eq_monomial, coeff_monomial]
  split_ifs
  · exact ha i
  · exact weightedScalar_zero F w d

include hcoeff hroot in
theorem weightedPolynomial_quadraticOne (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) :
    WeightedPolynomial F w 2
      (linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
        (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F))) := by
  apply weightedPolynomial_linearForm F (w := w) (d := 2)
  have hu : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryU K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 0)
  have hv : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryV K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 1)
  have hz := weightedScalar_root F Z hroot w hgraded
  intro i
  fin_cases i
  · exact weightedScalar_mul F hv hz
  · exact weightedScalar_mul F hz hu
  · exact weightedScalar_mul F hu hv

include hcoeff hroot in
theorem weightedPolynomial_quadraticTwo (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) :
    WeightedPolynomial F w 2
      (linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
        (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F))) := by
  apply weightedPolynomial_linearForm F (w := w) (d := 2)
  have hu : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryU K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 0)
  have hv : WeightedScalar F w 1 (cyclicCoefficientHom F (binaryV K)) :=
    weightedScalar_coefficient F hcoeff (isHomogeneous_X K 1)
  have hz := weightedScalar_root F Z hroot w hgraded
  intro i
  fin_cases i
  · exact weightedScalar_pow F hu 2
  · exact weightedScalar_pow F hv 2
  · exact weightedScalar_neg F (weightedScalar_pow F hz 2)

include hcoeff hroot in
theorem weightedPolynomial_quadraticSymmetric (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) (n : ℕ) (j : Fin (n + 1)) :
    WeightedPolynomial F w (2 * n)
      (linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (j : ℕ) *
        linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (n - j)) := by
  have h := weightedPolynomial_mul F
    (weightedPolynomial_pow F (weightedPolynomial_quadraticOne F Z hcoeff hroot w hgraded) j)
    (weightedPolynomial_pow F (weightedPolynomial_quadraticTwo F Z hcoeff hroot w hgraded) (n - j))
  convert h using 1
  have hj : (j : ℕ) ≤ n := by omega
  omega

/-- The literal source basis vector lies in the component of its generator shift. -/
theorem weightedVector_basis (w : Fin 3 → ℕ) (k : Fin 3) :
    WeightedVector (K := K) w (w k) (Pi.single k 1) := by
  intro i
  by_cases h : k = i
  · subst i
    simp only [Pi.single_eq_same, sub_self]
    change (1 : BinaryRing K) ∈ Forms K 2 0
    exact isHomogeneous_one (Fin 2) K
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    exact (signedForms K 2 _).zero_mem

include hcoeff hroot in
/-- Every entry of the actual symmetric kernel column has its required shifted degree. -/
theorem quadraticSymmetric_coefficient_degree (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) (n : ℕ) (j : Fin (n + 1))
    (α : Fin 3 →₀ ℕ) (i k : Fin 3) :
    tensorCoefficients
      ((linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (j : ℕ) *
        linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
          (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (n - j)) ⊗ₜ[CyclicCubicRing (BinaryRing K) F]
          (Pi.single k (1 : BinaryRing K) : BinaryVector K)) α i ∈
      signedForms K 2 (2 * n + w k - w i) := by
  rw [tensorCoefficients_tmul]
  have h := weightedPolynomial_quadraticSymmetric F Z hcoeff hroot w hgraded n j α
      (w k) (Pi.single k 1) (weightedVector_basis w k) i
  convert h using 1
  congr 1
  omega

end CubicAction

/-- The literal degree-`n` symmetric column of the two quadratic syzygies. -/
def quadraticSymmetricPolynomial (F : BinaryRing K) (n : ℕ) (j : Fin (n + 1)) :
    Aux (CyclicCubicRing (BinaryRing K) F) :=
  linearForm (quadraticOne (cyclicCoefficientHom F (binaryU K))
      (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (j : ℕ) *
    linearForm (quadraticTwo (cyclicCoefficientHom F (binaryU K))
      (cyclicCoefficientHom F (binaryV K)) (cyclicRoot F)) ^ (n - j)

/-- The coefficient certificate in the actual cyclic cubic module, including
its explicit scalar action. -/
theorem cyclic_quadraticSymmetric_coefficient_degree
    (F : BinaryRing K) (Z : End (BinaryRing K) (BinaryVector K))
    (hZ : Z ^ 3 = F • 1) (w : Fin 3 → ℕ)
    (hgraded : ∀ (t : ℤ) (m : BinaryVector K), WeightedVector w t m →
      WeightedVector w (t + 1) (Z m)) (n : ℕ) (j : Fin (n + 1))
    (α : Fin 3 →₀ ℕ) (i k : Fin 3) :
    letI := cyclicModuleStructure F Z hZ
    (((quadraticSymmetricPolynomial F n j).coeff α •
        (Pi.single k (1 : BinaryRing K) : BinaryVector K)) : BinaryVector K) i ∈
      signedForms K 2 (2 * n + w k - w i) := by
  let _ := cyclicModuleStructure F Z hZ
  simpa only [quadraticSymmetricPolynomial, tensorCoefficients_tmul] using
    quadraticSymmetric_coefficient_degree F Z
      (cyclicModule_coefficient_smul F Z hZ) (cyclicModule_root_smul F Z hZ)
      w hgraded n j α i k

/-- All three primal cyclic profiles satisfy the degree certificate. -/
theorem profile_quadraticSymmetric_coefficient_degree (q : K)
    (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (j : Fin (n + 1)) (α : Fin 3 →₀ ℕ) (i k : Fin 3) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s)
    (((quadraticSymmetricPolynomial (binaryCubic K) n j).coeff α •
        (Pi.single k (1 : BinaryRing K) : BinaryVector K)) : BinaryVector K) i ∈
      signedForms K 2 (2 * n + generatorWeights s k - generatorWeights s i) := by
  apply cyclic_quadraticSymmetric_coefficient_degree
  intro t m hm
  exact weightedVector_profileZ q s hm

/-- All three transposed cyclic profiles satisfy the dual shifted certificate. -/
theorem profileDual_quadraticSymmetric_coefficient_degree (q : K)
    (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile)
    (n : ℕ) (j : Fin (n + 1)) (α : Fin 3 →₀ ℕ) (i k : Fin 3) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s)
    (((quadraticSymmetricPolynomial (binaryCubic K) n j).coeff α •
        (Pi.single k (1 : BinaryRing K) : BinaryVector K)) : BinaryVector K) i ∈
      signedForms K 2 (2 * n + dualGeneratorWeights s k - dualGeneratorWeights s i) := by
  apply cyclic_quadraticSymmetric_coefficient_degree
  intro t m hm
  exact weightedVector_profileZDual q s hm

end ChoppedPlane.QWeyl
