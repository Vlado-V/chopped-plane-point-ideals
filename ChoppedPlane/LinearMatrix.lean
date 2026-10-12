module

public import ChoppedPlane.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Multiplication by a matrix of linear forms

The source and target are actual homogeneous polynomial spaces. This module
proves the elementary rank and degree-propagation facts; it makes no assertion
that a general matrix has maximal rank.
-/

noncomputable section

namespace ChoppedPlane

open MvPolynomial Module

variable (K : Type*) [Field K]

/-- A genuine `a × c` matrix of ternary linear forms. -/
abbrev LinearMatrix (a c : ℕ) := Matrix (Fin a) (Fin c) (Forms K 3 1)

/-- The source of the induced map in twist `t`. -/
abbrev MatrixSource (c t : ℕ) := Fin c → Forms K 3 t

/-- The target of the induced map in twist `t`. -/
abbrev MatrixTarget (a t : ℕ) := Fin a → Forms K 3 (t + 1)

variable {K} {a c t : ℕ}

/-- Multiplication by one linear form, with degrees written in successor form. -/
def multiplyLinear (q : Forms K 3 1) (f : Forms K 3 t) : Forms K 3 (t + 1) :=
  ⟨q.val * f.val, by
    change (q.val * f.val).IsHomogeneous (t + 1)
    simpa only [Nat.add_comm] using q.property.mul f.property⟩

@[simp] theorem multiplyLinear_val (q : Forms K 3 1) (f : Forms K 3 t) :
    (multiplyLinear q f).val = q.val * f.val := rfl

/-- Entrywise multiplication of a homogeneous vector by one linear form. -/
def multiplyVector {b : ℕ} (q : Forms K 3 1) (v : Fin b → Forms K 3 t) :
    Fin b → Forms K 3 (t + 1) := fun i => multiplyLinear q (v i)

/-- The degree-`t` polynomial multiplication map defined by the matrix. -/
def linearMatrixMap (L : LinearMatrix K a c) (t : ℕ) :
    MatrixSource K c t →ₗ[K] MatrixTarget K a t where
  toFun v i := ⟨∑ j, (L i j).val * (v j).val, by
    apply IsHomogeneous.sum
    intro j _
    simpa only [Nat.add_comm] using (L i j).property.mul (v j).property⟩
  map_add' v w := by
    funext i
    apply Subtype.ext
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' k v := by
    funext i
    apply Subtype.ext
    simp [Finset.smul_sum]

@[simp] theorem linearMatrixMap_val (L : LinearMatrix K a c) (t : ℕ)
    (v : MatrixSource K c t) (i : Fin a) :
    (linearMatrixMap L t v i).val = ∑ j, (L i j).val * (v j).val := rfl

/-- Source dimension of the degree-`t` matrix map. -/
theorem finrank_matrixSource (K : Type*) [Field K] (c t : ℕ) :
    finrank K (MatrixSource K c t) = c * (t + 2).choose 2 := by
  simp [MatrixSource, Module.finrank_pi_fintype, finrank_plane_forms]

/-- Target dimension of the degree-`t` matrix map. -/
theorem finrank_matrixTarget (K : Type*) [Field K] (a t : ℕ) :
    finrank K (MatrixTarget K a t) = a * (t + 3).choose 2 := by
  simp [MatrixTarget, Module.finrank_pi_fintype, finrank_plane_forms, Nat.add_assoc]

/-- Maximal rank has its literal finite-dimensional meaning. -/
def LinearMatrixMaximalRank (L : LinearMatrix K a c) (t : ℕ) : Prop :=
  finrank K (linearMatrixMap L t).range =
    min (finrank K (MatrixSource K c t)) (finrank K (MatrixTarget K a t))

/-- The cokernel is the actual quotient by the image. -/
abbrev LinearMatrixCokernel (L : LinearMatrix K a c) (t : ℕ) :=
  MatrixTarget K a t ⧸ (linearMatrixMap L t).range

/-- Polynomial multiplication commutes with the matrix map. -/
theorem linearMatrixMap_multiplyVector (L : LinearMatrix K a c)
    (q : Forms K 3 1) (v : MatrixSource K c t) :
    linearMatrixMap L (t + 1) (multiplyVector q v) =
      multiplyVector q (linearMatrixMap L t v) := by
  funext i
  apply Subtype.ext
  simp [linearMatrixMap, multiplyVector, multiplyLinear, Finset.mul_sum,
    mul_left_comm]

/-- A nonzero linear form multiplies homogeneous vectors injectively. -/
theorem multiplyVector_injective {b : ℕ} (q : Forms K 3 1) (hq : q.val ≠ 0) :
    Function.Injective (multiplyVector (b := b) (t := t) q) := by
  intro v w h
  funext i
  apply Subtype.ext
  exact mul_left_cancel₀ hq (congrArg Subtype.val (congrFun h i))

/-- Injectivity in one twist implies injectivity in the preceding twist. -/
theorem linearMatrixMap_injective_of_succ (L : LinearMatrix K a c)
    (h : Function.Injective (linearMatrixMap L (t + 1))) :
    Function.Injective (linearMatrixMap L t) := by
  let q : Forms K 3 1 := ⟨X 0, isHomogeneous_X K 0⟩
  have hq : q.val ≠ 0 := X_ne_zero 0
  intro v w hvw
  apply multiplyVector_injective q hq
  apply h
  rw [linearMatrixMap_multiplyVector, linearMatrixMap_multiplyVector, hvw]

/-- Injectivity propagates to all lower twists. -/
theorem linearMatrixMap_injective_downward (L : LinearMatrix K a c)
    {s t : ℕ} (hst : s ≤ t) (h : Function.Injective (linearMatrixMap L t)) :
    Function.Injective (linearMatrixMap L s) := by
  induction t generalizing s with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact h
  | succ t ih =>
    by_cases hs : s = t + 1
    · subst s
      exact h
    · apply ih (by omega : s ≤ t)
      exact linearMatrixMap_injective_of_succ L h

/-- Surjectivity in one twist implies surjectivity in the next twist. -/
theorem linearMatrixMap_surjective_succ (L : LinearMatrix K a c)
    (h : Function.Surjective (linearMatrixMap L t)) :
    Function.Surjective (linearMatrixMap L (t + 1)) := by
  classical
  have hsingle (i : Fin a) (p : Poly K 3) (hp : p ∈ Forms K 3 (t + 1 + 1)) :
      Pi.single i (⟨p, hp⟩ : Forms K 3 (t + 1 + 1)) ∈
        (linearMatrixMap L (t + 1)).range := by
    have heq : Forms K 3 1 * Forms K 3 (t + 1) = Forms K 3 (t + 1 + 1) := by
      simpa only [Nat.add_comm] using
        (forms_mul_forms (K := K) (n := 3) (d := 1) (e := t + 1))
    have hprod : p ∈ Forms K 3 1 * Forms K 3 (t + 1) := by rw [heq]; exact hp
    have hresult : ∀ q : Poly K 3, q ∈ Forms K 3 1 * Forms K 3 (t + 1) →
        ∀ hq : q ∈ Forms K 3 (t + 1 + 1),
          Pi.single i (⟨q, hq⟩ : Forms K 3 (t + 1 + 1)) ∈
            (linearMatrixMap L (t + 1)).range := by
      intro q hq
      refine Submodule.mul_induction_on'
        (M := Forms K 3 1) (N := Forms K 3 (t + 1))
        (C := fun q _ => ∀ hq : q ∈ Forms K 3 (t + 1 + 1),
          Pi.single i (⟨q, hq⟩ : Forms K 3 (t + 1 + 1)) ∈
            (linearMatrixMap L (t + 1)).range) ?_ ?_ hq
      · intro f hf g hg hfg
        obtain ⟨v, hv⟩ := h (Pi.single i (⟨g, hg⟩ : Forms K 3 (t + 1)))
        refine ⟨multiplyVector (⟨f, hf⟩ : Forms K 3 1) v, ?_⟩
        rw [linearMatrixMap_multiplyVector, hv]
        funext j
        apply Subtype.ext
        by_cases hji : j = i
        · subst j
          simp [multiplyVector, multiplyLinear]
        · simp [multiplyVector, multiplyLinear, hji]
      · intro q hq r hr hq_ih hr_ih hqr
        have hq' : q ∈ Forms K 3 (t + 1 + 1) := by rw [← heq]; exact hq
        have hr' : r ∈ Forms K 3 (t + 1 + 1) := by rw [← heq]; exact hr
        obtain ⟨v, hv⟩ := hq_ih hq'
        obtain ⟨w, hw⟩ := hr_ih hr'
        refine ⟨v + w, ?_⟩
        rw [map_add, hv, hw]
        funext j
        apply Subtype.ext
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
    exact hresult p hprod hp
  intro y
  have hy : y ∈ (linearMatrixMap L (t + 1)).range := by
    have hsum := (linearMatrixMap L (t + 1)).range.sum_mem
      (t := Finset.univ) (f := fun i => Pi.single i (y i))
      (fun i _ => hsingle i (y i).val (y i).property)
    have heq : (∑ i : Fin a, Pi.single i (y i)) = y := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rwa [heq] at hsum
  exact hy

/-- Surjectivity propagates to all higher twists. -/
theorem linearMatrixMap_surjective_upward (L : LinearMatrix K a c)
    {s t : ℕ} (hst : s ≤ t) (h : Function.Surjective (linearMatrixMap L s)) :
    Function.Surjective (linearMatrixMap L t) := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t hst ih => exact linearMatrixMap_surjective_succ L ih

/-- An injective matrix map has maximal rank. -/
theorem linearMatrixMaximalRank_of_injective (L : LinearMatrix K a c) (t : ℕ)
    (h : Function.Injective (linearMatrixMap L t)) : LinearMatrixMaximalRank L t := by
  have hr := LinearMap.finrank_range_of_inj h
  have hle := Submodule.finrank_le (linearMatrixMap L t).range
  rw [hr] at hle
  exact hr.trans (min_eq_left hle).symm

/-- A surjective matrix map has maximal rank. -/
theorem linearMatrixMaximalRank_of_surjective (L : LinearMatrix K a c) (t : ℕ)
    (h : Function.Surjective (linearMatrixMap L t)) : LinearMatrixMaximalRank L t := by
  have hr : (linearMatrixMap L t).range = ⊤ := LinearMap.range_eq_top.mpr h
  have hdim := LinearMap.finrank_range_le (linearMatrixMap L t)
  rw [hr, finrank_top] at hdim
  dsimp [LinearMatrixMaximalRank]
  rw [hr, finrank_top, min_eq_right hdim]

/-- When the source is smaller, maximal rank is equivalent to injectivity. -/
theorem linearMatrixMaximalRank_iff_injective (L : LinearMatrix K a c) (t : ℕ)
    (hsize : finrank K (MatrixSource K c t) ≤ finrank K (MatrixTarget K a t)) :
    LinearMatrixMaximalRank L t ↔ Function.Injective (linearMatrixMap L t) := by
  constructor
  · intro h
    dsimp [LinearMatrixMaximalRank] at h
    rw [min_eq_left hsize] at h
    have hk := LinearMap.finrank_range_add_finrank_ker (linearMatrixMap L t)
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    omega
  · exact linearMatrixMaximalRank_of_injective L t

/-- When the target is smaller, maximal rank is equivalent to surjectivity. -/
theorem linearMatrixMaximalRank_iff_surjective (L : LinearMatrix K a c) (t : ℕ)
    (hsize : finrank K (MatrixTarget K a t) ≤ finrank K (MatrixSource K c t)) :
    LinearMatrixMaximalRank L t ↔ Function.Surjective (linearMatrixMap L t) := by
  constructor
  · intro h
    dsimp [LinearMatrixMaximalRank] at h
    rw [min_eq_right hsize] at h
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq h
  · exact linearMatrixMaximalRank_of_surjective L t

/-- Maximal rank means injectivity or surjectivity. -/
theorem linearMatrixMaximalRank_iff (L : LinearMatrix K a c) (t : ℕ) :
    LinearMatrixMaximalRank L t ↔
      Function.Injective (linearMatrixMap L t) ∨
        Function.Surjective (linearMatrixMap L t) := by
  constructor
  · intro h
    by_cases hs : finrank K (MatrixSource K c t) ≤ finrank K (MatrixTarget K a t)
    · exact Or.inl ((linearMatrixMaximalRank_iff_injective L t hs).mp h)
    · exact Or.inr ((linearMatrixMaximalRank_iff_surjective L t (by omega)).mp h)
  · rintro (h | h)
    · exact linearMatrixMaximalRank_of_injective L t h
    · exact linearMatrixMaximalRank_of_surjective L t h

/-- Maximal rank gives the expected nonnegative cokernel dimension. -/
theorem finrank_linearMatrixCokernel (L : LinearMatrix K a c) (t : ℕ)
    (h : LinearMatrixMaximalRank L t) :
    finrank K (LinearMatrixCokernel L t) =
      a * (t + 3).choose 2 - c * (t + 2).choose 2 := by
  have hquot := (linearMatrixMap L t).range.finrank_quotient_add_finrank
  dsimp [LinearMatrixMaximalRank] at h
  rw [h, finrank_matrixSource, finrank_matrixTarget] at hquot
  dsimp [LinearMatrixCokernel]
  omega

/-- Two consecutive injectivity and surjectivity checks cover every twist. -/
theorem linearMatrixMaximalRank_all_of_two_checks (L : LinearMatrix K a c)
    (t₀ : ℕ) (hinj : Function.Injective (linearMatrixMap L t₀))
    (hsurj : Function.Surjective (linearMatrixMap L (t₀ + 1))) :
    ∀ t, LinearMatrixMaximalRank L t := by
  intro t
  by_cases ht : t ≤ t₀
  · exact linearMatrixMaximalRank_of_injective L t
      (linearMatrixMap_injective_downward L ht hinj)
  · exact linearMatrixMaximalRank_of_surjective L t
      (linearMatrixMap_surjective_upward L (by omega) hsurj)

/-- The two-check statement expressed using maximal ranks at the crossing. -/
theorem linearMatrixMaximalRank_all_of_critical_checks (L : LinearMatrix K a c)
    (t₀ : ℕ)
    (hsmall : finrank K (MatrixSource K c t₀) ≤ finrank K (MatrixTarget K a t₀))
    (hlarge : finrank K (MatrixTarget K a (t₀ + 1)) ≤
      finrank K (MatrixSource K c (t₀ + 1)))
    (hleft : LinearMatrixMaximalRank L t₀)
    (hright : LinearMatrixMaximalRank L (t₀ + 1)) :
    ∀ t, LinearMatrixMaximalRank L t :=
  linearMatrixMaximalRank_all_of_two_checks L t₀
    ((linearMatrixMaximalRank_iff_injective L t₀ hsmall).mp hleft)
    ((linearMatrixMaximalRank_iff_surjective L (t₀ + 1) hlarge).mp hright)

/-- A single bijective twist suffices for maximal rank in every twist. -/
theorem linearMatrixMaximalRank_all_of_bijective (L : LinearMatrix K a c)
    (t₀ : ℕ) (h : Function.Bijective (linearMatrixMap L t₀)) :
    ∀ t, LinearMatrixMaximalRank L t := by
  intro t
  by_cases ht : t ≤ t₀
  · exact linearMatrixMaximalRank_of_injective L t
      (linearMatrixMap_injective_downward L ht h.1)
  · exact linearMatrixMaximalRank_of_surjective L t
      (linearMatrixMap_surjective_upward L (by omega) h.2)

/-- For `a + 2` columns the source and target agree at twist `a - 1`. -/
theorem two_extra_columns_crossing (K : Type*) [Field K] {a : ℕ} (ha : 0 < a) :
    finrank K (MatrixSource K (a + 2) (a - 1)) =
      finrank K (MatrixTarget K a (a - 1)) := by
  rw [finrank_matrixSource, finrank_matrixTarget]
  have h₁ : a - 1 + 2 = a + 1 := by omega
  have h₂ : a - 1 + 3 = a + 2 := by omega
  rw [h₁, h₂]
  have h := Nat.choose_mul_succ_eq (a + 1) 2
  have hsub : a + 1 + 1 - 2 = a := by omega
  simpa only [Nat.add_assoc, Nat.one_add, hsub, Nat.mul_comm] using h

/-- Injectivity at the equal-dimensional twist gives all ranks for `a + 2` columns. -/
theorem linearMatrixMaximalRank_all_of_two_extra_columns
    (L : LinearMatrix K a (a + 2)) (ha : 0 < a)
    (h : Function.Injective (linearMatrixMap L (a - 1))) :
    ∀ t, LinearMatrixMaximalRank L t := by
  have hdim := two_extra_columns_crossing K ha
  have hmax := linearMatrixMaximalRank_of_injective L (a - 1) h
  have hsurj := (linearMatrixMaximalRank_iff_surjective L (a - 1) hdim.ge).mp hmax
  exact linearMatrixMaximalRank_all_of_bijective L (a - 1) ⟨h, hsurj⟩

/-- The dimension comparison reduces to a linear inequality in the twist. -/
theorem matrixSource_le_target_iff (K : Type*) [Field K] (a c t : ℕ) :
    finrank K (MatrixSource K c t) ≤ finrank K (MatrixTarget K a t) ↔
      c * (t + 1) ≤ a * (t + 3) := by
  rw [finrank_matrixSource, finrank_matrixTarget]
  have hpos : 0 < (t + 2).choose 2 := Nat.choose_pos (by omega)
  have hchoose : (t + 3).choose 2 * (t + 1) = (t + 2).choose 2 * (t + 3) := by
    have h := Nat.choose_mul_succ_eq (t + 2) 2
    have hsub : t + 2 + 1 - 2 = t + 1 := by omega
    simpa only [Nat.add_assoc, hsub] using h.symm
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_right (t + 1) h
    have h' : c * (t + 1) * (t + 2).choose 2 ≤
        a * (t + 3) * (t + 2).choose 2 := by
      calc
        c * (t + 1) * (t + 2).choose 2 = c * (t + 2).choose 2 * (t + 1) := by ring
        _ ≤ a * (t + 3).choose 2 * (t + 1) := hmul
        _ = a * ((t + 3).choose 2 * (t + 1)) := by ring
        _ = a * ((t + 2).choose 2 * (t + 3)) := by rw [hchoose]
        _ = a * (t + 3) * (t + 2).choose 2 := by ring
    exact Nat.le_of_mul_le_mul_right h' hpos
  · intro h
    have hmul := Nat.mul_le_mul_right ((t + 2).choose 2) h
    have h' : c * (t + 2).choose 2 * (t + 1) ≤
        a * (t + 3).choose 2 * (t + 1) := by
      calc
        c * (t + 2).choose 2 * (t + 1) = c * (t + 1) * (t + 2).choose 2 := by ring
        _ ≤ a * (t + 3) * (t + 2).choose 2 := hmul
        _ = a * ((t + 2).choose 2 * (t + 3)) := by ring
        _ = a * ((t + 3).choose 2 * (t + 1)) := by rw [hchoose]
        _ = a * (t + 3).choose 2 * (t + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h' (by omega)

/-- The reverse dimension comparison has the same linear description. -/
theorem matrixTarget_le_source_iff (K : Type*) [Field K] (a c t : ℕ) :
    finrank K (MatrixTarget K a t) ≤ finrank K (MatrixSource K c t) ↔
      a * (t + 3) ≤ c * (t + 1) := by
  rw [finrank_matrixSource K c t, finrank_matrixTarget K a t]
  have hpos : 0 < (t + 2).choose 2 := Nat.choose_pos (by omega)
  have hchoose : (t + 3).choose 2 * (t + 1) = (t + 2).choose 2 * (t + 3) := by
    have h := Nat.choose_mul_succ_eq (t + 2) 2
    have hsub : t + 2 + 1 - 2 = t + 1 := by omega
    simpa only [Nat.add_assoc, hsub] using h.symm
  constructor
  · intro h
    have hmul := Nat.mul_le_mul_right (t + 1) h
    have h' : a * (t + 3) * (t + 2).choose 2 ≤
        c * (t + 1) * (t + 2).choose 2 := by
      calc
        a * (t + 3) * (t + 2).choose 2 = a * ((t + 2).choose 2 * (t + 3)) := by ring
        _ = a * ((t + 3).choose 2 * (t + 1)) := by rw [hchoose]
        _ = a * (t + 3).choose 2 * (t + 1) := by ring
        _ ≤ c * (t + 2).choose 2 * (t + 1) := hmul
        _ = c * (t + 1) * (t + 2).choose 2 := by ring
    exact Nat.le_of_mul_le_mul_right h' hpos
  · intro h
    have hmul := Nat.mul_le_mul_right ((t + 2).choose 2) h
    have h' : a * (t + 3).choose 2 * (t + 1) ≤
        c * (t + 2).choose 2 * (t + 1) := by
      calc
        a * (t + 3).choose 2 * (t + 1) = a * ((t + 3).choose 2 * (t + 1)) := by ring
        _ = a * ((t + 2).choose 2 * (t + 3)) := by rw [hchoose]
        _ = a * (t + 3) * (t + 2).choose 2 := by ring
        _ ≤ c * (t + 1) * (t + 2).choose 2 := hmul
        _ = c * (t + 2).choose 2 * (t + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h' (by omega)

/-- The first twist strictly past the source/target dimension crossing. -/
def linearMatrixCriticalTwist (a c : ℕ) : ℕ := (2 * a) / (c - a)

/-- The source is at least as large as the target at the critical twist. -/
theorem criticalTwist_target_le_source (K : Type*) [Field K] {a c : ℕ} (hac : a < c) :
    finrank K (MatrixTarget K a (linearMatrixCriticalTwist a c)) ≤
      finrank K (MatrixSource K c (linearMatrixCriticalTwist a c)) := by
  rw [matrixTarget_le_source_iff]
  have hpos : 0 < c - a := by omega
  have hbound := Nat.lt_mul_div_succ (2 * a) hpos
  have hc : c = a + (c - a) := by omega
  dsimp [linearMatrixCriticalTwist]
  nlinarith

/-- Just before a positive critical twist, the source is the smaller space. -/
theorem before_criticalTwist_source_le_target (K : Type*) [Field K] {a c : ℕ}
    (hac : a < c) (hpos : 0 < linearMatrixCriticalTwist a c) :
    finrank K (MatrixSource K c (linearMatrixCriticalTwist a c - 1)) ≤
      finrank K (MatrixTarget K a (linearMatrixCriticalTwist a c - 1)) := by
  rw [matrixSource_le_target_iff]
  have hbound := Nat.div_mul_le_self (2 * a) (c - a)
  have hc : c = a + (c - a) := by omega
  have hsub : linearMatrixCriticalTwist a c - 1 + 1 = linearMatrixCriticalTwist a c := by omega
  rw [hsub]
  have hsub' : linearMatrixCriticalTwist a c - 1 + 3 = linearMatrixCriticalTwist a c + 2 := by omega
  rw [hsub']
  dsimp [linearMatrixCriticalTwist] at *
  nlinarith

/-- All ranks follow from the two numerical critical-twist tests.
When the critical twist is zero, the right-hand test alone suffices. -/
theorem linearMatrixMaximalRank_all_of_numeric_critical_checks
    (L : LinearMatrix K a c) (hac : a < c)
    (hleft : 0 < linearMatrixCriticalTwist a c →
      LinearMatrixMaximalRank L (linearMatrixCriticalTwist a c - 1))
    (hright : LinearMatrixMaximalRank L (linearMatrixCriticalTwist a c)) :
    ∀ t, LinearMatrixMaximalRank L t := by
  by_cases hq : 0 < linearMatrixCriticalTwist a c
  · have hlarge := criticalTwist_target_le_source K hac
    have hsmall := before_criticalTwist_source_le_target K hac hq
    have hsucc : linearMatrixCriticalTwist a c - 1 + 1 = linearMatrixCriticalTwist a c := by omega
    apply linearMatrixMaximalRank_all_of_critical_checks L
      (linearMatrixCriticalTwist a c - 1) hsmall
    · rwa [hsucc]
    · exact hleft hq
    · rwa [hsucc]
  · have hzero : linearMatrixCriticalTwist a c = 0 := by omega
    have hlarge := criticalTwist_target_le_source K hac
    have hsurj := (linearMatrixMaximalRank_iff_surjective L
      (linearMatrixCriticalTwist a c) hlarge).mp hright
    rw [hzero] at hsurj
    intro t
    exact linearMatrixMaximalRank_of_surjective L t
      (linearMatrixMap_surjective_upward L (Nat.zero_le t) hsurj)

end ChoppedPlane
