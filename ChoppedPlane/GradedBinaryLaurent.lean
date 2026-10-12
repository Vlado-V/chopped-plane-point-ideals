module

public import ChoppedPlane.ProfileOperators
public import ChoppedPlane.LaurentPairing
public import ChoppedPlane.SymmetricCoordinates
public import Mathlib.LinearAlgebra.Finsupp.Pi

@[expose] public section

/-! Actual homogeneous binary polynomial vectors are exactly the nonnegative
Laurent coefficient vectors of the same weighted degree. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial Module LaurentPairing
variable {K : Type*} [Field K]

/-- Signed homogeneous membership is the literal support-degree condition. -/
theorem mem_signedBinaryForms_iff_coeff (t : ℤ) (f : BinaryRing K) :
    f ∈ signedForms K 2 t ↔ ∀ s : Fin 2 →₀ ℕ,
      f.coeff s ≠ 0 → (s.degree : ℤ) = t := by
  by_cases ht : 0 ≤ t
  · simp only [signedForms, ite_eq_left ht]
    constructor
    · intro hf s hs
      have h := hf hs
      have hnat : s.degree = t.toNat := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using h
      omega
    · intro h
      change f.IsHomogeneous t.toNat
      intro s hs
      have hnat : s.degree = t.toNat := by have h' := h s hs; omega
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hnat
  · simp only [signedForms, ite_eq_right ht, Submodule.mem_bot]
    constructor
    · intro hf s hs
      simp [hf] at hs
    · intro h
      apply MvPolynomial.ext
      intro s
      by_contra hs
      have h' := h s (by simpa using hs)
      omega

/-- Flatten the actual coefficient vectors, retaining the component index. -/
def binaryVectorCoefficients : BinaryVector K ≃ₗ[K]
    (Fin 3 × (Fin 2 →₀ ℕ)) →₀ K :=
  (LinearEquiv.piCongrRight fun _ => (AddMonoidAlgebra.coeffLinearEquiv K)).trans
    ((Finsupp.linearEquivFunOnFinite K ((Fin 2 →₀ ℕ) →₀ K) (Fin 3)).symm.trans
      (Finsupp.curryLinearEquiv K).symm)

@[simp] theorem binaryVectorCoefficients_apply (m : BinaryVector K)
    (i : Fin 3) (s : Fin 2 →₀ ℕ) :
    binaryVectorCoefficients m (i,s) = (m i).coeff s := by
  rfl

/-- The two binary exponents become the two nonnegative Laurent exponents. -/
def binaryVectorExponent (a : Fin 3 × (Fin 2 →₀ ℕ)) : Fin 3 × (ℤ × ℤ) :=
  (a.1, ((a.2 0 : ℤ), (a.2 1 : ℤ)))

theorem binaryVectorExponent_injective : Function.Injective binaryVectorExponent := by
  intro a b h
  have hi : a.1 = b.1 := by
    simpa only [binaryVectorExponent] using congrArg Prod.fst h
  have h0 : a.2 0 = b.2 0 := by
    have h' := congrArg (fun e : Fin 3 × (ℤ × ℤ) => e.2.1) h
    simpa only [binaryVectorExponent, Int.natCast_inj] using h'
  have h1 : a.2 1 = b.2 1 := by
    have h' := congrArg (fun e : Fin 3 × (ℤ × ℤ) => e.2.2) h
    simpa only [binaryVectorExponent, Int.natCast_inj] using h'
  apply Prod.ext hi
  ext i
  fin_cases i
  · exact h0
  · exact h1

theorem mem_range_binaryVectorExponent (e : Fin 3 × (ℤ × ℤ)) :
    e ∈ Set.range binaryVectorExponent ↔ 0 ≤ e.2.1 ∧ 0 ≤ e.2.2 := by
  constructor
  · rintro ⟨⟨i,s⟩,rfl⟩
    exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _⟩
  · rintro ⟨ha,hb⟩
    refine ⟨(e.1,Finsupp.single 0 e.2.1.toNat+Finsupp.single 1 e.2.2.toNat),?_⟩
    ext <;> simp [binaryVectorExponent, Int.toNat_of_nonneg ha, Int.toNat_of_nonneg hb]

/-- The actual binary polynomial embedding into the free Laurent coefficient module. -/
def binaryVectorLaurent : BinaryVector K →ₗ[K] FreeLaurent K (Fin 3) :=
  (Finsupp.lmapDomain K K binaryVectorExponent).comp binaryVectorCoefficients.toLinearMap

@[simp] theorem binaryVectorLaurent_coeff (m : BinaryVector K)
    (i : Fin 3) (s : Fin 2 →₀ ℕ) :
    binaryVectorLaurent m (binaryVectorExponent (i,s)) = (m i).coeff s := by
  change (Finsupp.mapDomain binaryVectorExponent (binaryVectorCoefficients m))
    (binaryVectorExponent (i,s)) = _
  rw [Finsupp.mapDomain_apply_of_injective binaryVectorExponent_injective]
  exact binaryVectorCoefficients_apply m i s

theorem binaryVectorLaurent_injective : Function.Injective (binaryVectorLaurent (K := K)) :=
  (Finsupp.mapDomain_injective binaryVectorExponent_injective).comp
    binaryVectorCoefficients.injective

/-- The weighted actual homogeneous component maps into its literal Laurent grade. -/
theorem binaryVectorLaurent_mem_positiveGrade (w : Fin 3 → ℕ) (t : ℤ)
    (m : GradedBinaryVector (K := K) w t) :
    binaryVectorLaurent (gradedBinaryVectorVal w t m) ∈
      positiveGrade (fun i => (w i : ℤ)) t := by
  apply (Finsupp.mem_supported K _).mpr
  intro e he
  have hn : binaryVectorLaurent (gradedBinaryVectorVal w t m) e ≠ 0 :=
    Finsupp.mem_support_iff.mp he
  obtain ⟨⟨i,s⟩,rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hn
  have hs : (m i).val.coeff s ≠ 0 := by
    change (binaryVectorLaurent (gradedBinaryVectorVal w t m))
      (binaryVectorExponent (i,s)) ≠ 0 at hn
    rw [binaryVectorLaurent_coeff] at hn
    exact hn
  have hdeg := (mem_signedBinaryForms_iff_coeff (t-(w i : ℤ)) (m i).val).mp
    (m i).property s hs
  have hb := ChoppedPlane.SymmetricDerivative.binary_degree s
  change 0 ≤ (s 0 : ℤ) ∧ 0 ≤ (s 1 : ℤ) ∧
    (s 0 : ℤ)+(s 1 : ℤ)+(w i : ℤ) = t
  exact ⟨Int.natCast_nonneg _,Int.natCast_nonneg _,by omega⟩

/-- The actual graded polynomial-to-Laurent map. -/
def gradedBinaryLaurentMap (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t →ₗ[K]
      positiveGrade (K := K) (fun i => (w i : ℤ)) t :=
  ((binaryVectorLaurent (K := K)).comp (gradedBinaryVectorVal w t)).codRestrict _
    (binaryVectorLaurent_mem_positiveGrade w t)

@[simp] theorem gradedBinaryLaurentMap_val (w : Fin 3 → ℕ) (t : ℤ)
    (m : GradedBinaryVector (K := K) w t) :
    (gradedBinaryLaurentMap w t m).val = binaryVectorLaurent (gradedBinaryVectorVal w t m) := rfl

theorem gradedBinaryLaurentMap_injective (w : Fin 3 → ℕ) (t : ℤ) :
    Function.Injective (gradedBinaryLaurentMap (K := K) w t) := by
  intro m n h
  apply gradedBinaryVectorVal_injective w t
  apply binaryVectorLaurent_injective
  exact congrArg Subtype.val h

theorem gradedBinaryLaurentMap_surjective (w : Fin 3 → ℕ) (t : ℤ) :
    Function.Surjective (gradedBinaryLaurentMap (K := K) w t) := by
  intro p
  have hrange : p.val ∈ Set.range (Finsupp.mapDomain binaryVectorExponent) := by
    apply (Finsupp.mem_range_mapDomain_iff binaryVectorExponent
      binaryVectorExponent_injective p.val).mpr
    intro e he
    by_contra hn
    have hp := (Finsupp.mem_supported K p.val).mp p.property
      (Finsupp.mem_support_iff.mpr hn)
    exact he ((mem_range_binaryVectorExponent e).mpr ⟨hp.1,hp.2.1⟩)
  obtain ⟨c,hc⟩ := hrange
  let v := binaryVectorCoefficients.symm c
  have hv : binaryVectorLaurent v = p.val := by
    change Finsupp.mapDomain binaryVectorExponent
      (binaryVectorCoefficients (binaryVectorCoefficients.symm c)) = p.val
    rw [LinearEquiv.apply_symm_apply]
    exact hc
  have hgrade (i : Fin 3) : v i ∈ signedForms K 2 (t-(w i : ℤ)) := by
    apply (mem_signedBinaryForms_iff_coeff _ _).mpr
    intro s hs
    have hpne : p.val (binaryVectorExponent (i,s)) ≠ 0 := by
      rw [← hv, binaryVectorLaurent_coeff]
      exact hs
    have hp := (Finsupp.mem_supported K p.val).mp p.property
      (Finsupp.mem_support_iff.mpr hpne)
    have hb := ChoppedPlane.SymmetricDerivative.binary_degree s
    change 0 ≤ (s 0 : ℤ) ∧ 0 ≤ (s 1 : ℤ) ∧
      (s 0 : ℤ)+(s 1 : ℤ)+(w i : ℤ)=t at hp
    omega
  refine ⟨fun i => ⟨v i,hgrade i⟩,?_⟩
  apply Subtype.ext
  exact hv

/-- This is an actual equivalence, with no dimension or rank premise. -/
def gradedBinaryLaurentEquiv (w : Fin 3 → ℕ) (t : ℤ) :
    GradedBinaryVector (K := K) w t ≃ₗ[K]
      positiveGrade (K := K) (fun i => (w i : ℤ)) t :=
  LinearEquiv.ofBijective (gradedBinaryLaurentMap w t)
    ⟨gradedBinaryLaurentMap_injective w t,gradedBinaryLaurentMap_surjective w t⟩

@[simp] theorem gradedBinaryLaurentEquiv_apply (w : Fin 3 → ℕ) (t : ℤ)
    (m : GradedBinaryVector (K := K) w t) :
    (gradedBinaryLaurentEquiv w t m).val = binaryVectorLaurent (gradedBinaryVectorVal w t m) := rfl

end ChoppedPlane.QWeyl
