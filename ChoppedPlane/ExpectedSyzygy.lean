module

public import ChoppedPlane.MainAssembly
public import ChoppedPlane.EmptyConfiguration

@[expose] public section

/-!
# Corollary 5.1: the Expected Syzygy Conjecture in the plane

The actual alternating Koszul coefficient is retained until its first value
at or below the point count in a *positive* excess degree. If no such degree
exists, the untruncated series is retained in every degree. This encodes
Conjecture 1 of Gesmundo–Kayser–Telen directly, including its infinite-cutoff
convention, rather than redefining the expectation as the main theorem's
piecewise formula.
-/
noncomputable section
namespace ChoppedPlane

/-- The coefficient of `(1-z^d)^r/(1-z)^3`, with signed-degree convention. -/
def koszulCoefficient (d r t : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (r + 1),
    (-1 : ℤ)^k * (r.choose k : ℤ) * N₂ ((t : ℤ) - (k : ℤ) * d)

/-- A positive excess degree at which the full Koszul coefficient has already
reached or fallen below the point count. -/
def koszulPrefixHit (d p e : ℕ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ q ≤ e ∧ koszulCoefficient d (N d - p) (d + q) ≤ p

/-- The literal positive-prefix truncation prescribed by the Expected Syzygy
Conjecture. Its cutoff can be infinite. -/
def expectedSyzygyCoefficient (d p t : ℕ) : ℤ :=
  by
    classical
    exact if t < d then N t
      else if koszulPrefixHit d p (t - d) then p
      else koszulCoefficient d (N d - p) t

/-- The least degree whose ternary-form dimension reaches the point count. -/
def expectedSyzygyDegree (p : ℕ) : ℕ :=
  Nat.find (show ∃ d, p ≤ N d from ⟨p,
    Nat.le_trans (Nat.le_succ p)
      (Eq.mpr
        (congrArg (fun n : ℕ => p + 1 ≤ n)
          ((Nat.choose_succ_succ (p + 1) 1).trans
            (congrArg (fun n => n + (p + 1).choose 2) (Nat.choose_one_right (p + 1)))))
        (Nat.le_add_right (p + 1) ((p + 1).choose 2)))⟩)

/-- The conjecture's convention for the chopping degree. -/
def IsExpectedSyzygyDegree (d p : ℕ) : Prop :=
  p ≤ N d ∧ ∀ t, t < d → N t < p

lemma N_monotone : Monotone N := by
  intro a b hab
  exact Nat.choose_mono 2 (by omega : a + 2 ≤ b + 2)

lemma N_strictMono : StrictMono N := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [N_succ]
  omega

lemma expectedSyzygyDegree_spec (p : ℕ) :
    IsExpectedSyzygyDegree (expectedSyzygyDegree p) p := by
  constructor
  · unfold expectedSyzygyDegree
    exact Nat.find_spec (p := fun d => p ≤ N d) _
  · intro t ht
    unfold expectedSyzygyDegree at ht
    exact Nat.lt_of_not_ge (Nat.find_min (p := fun d => p ≤ N d) _ ht)

lemma isExpectedSyzygyDegree_lower {d p : ℕ} (h : IsExpectedSyzygyDegree d p)
    (hd : 1 ≤ d) : N (d - 1) < p := h.2 _ (by omega)

lemma koszulCoefficient_zero (d t : ℕ) : koszulCoefficient d 0 t = N t := by
  simp [koszulCoefficient]

lemma koszulCoefficient_small (d r t : ℕ) (hr : r ≤ 2) :
    koszulCoefficient d r t = completeIntersectionCoefficient d r t := by
  interval_cases r <;>
    norm_num [koszulCoefficient, completeIntersectionCoefficient,
      Finset.sum_range_succ] <;> ring

lemma koszulCoefficient_before_second {d r t : ℕ} (hr : 1 ≤ r) (ht : t < 2 * d) :
    koszulCoefficient d r t = N t - (r : ℤ) * N₂ ((t : ℤ) - d) := by
  let F : ℕ → ℤ := fun k =>
    (-1 : ℤ)^k * (r.choose k : ℤ) * N₂ ((t : ℤ) - (k : ℤ) * d)
  have hsum : (∑ k ∈ Finset.range 2, F k) = ∑ k ∈ Finset.range (r + 1), F k := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (show 2 ≤ r + 1 by omega))
    intro k hk hknot
    have hk2 : 2 ≤ k := by simp only [Finset.mem_range] at hknot; omega
    have hkd : 2 * d ≤ k * d := Nat.mul_le_mul_right d hk2
    have hnegative : (t : ℤ) - (k : ℤ) * d < 0 := by
      have hcast : (t : ℤ) < (k : ℤ) * d := by exact_mod_cast (by omega : t < k * d)
      omega
    simp [F, N₂_neg hnegative]
  change (∑ k ∈ Finset.range (r + 1), F k) = _
  rw [← hsum]
  simp [F, Finset.sum_range_succ, sub_eq_add_neg]

lemma koszulCoefficient_at_excess_before_second {d r e : ℕ}
    (hr : 1 ≤ r) (he : e < d) :
    koszulCoefficient d r (d + e) = (N d : ℤ) - r + residual d r e := by
  rw [koszulCoefficient_before_second hr (by omega)]
  simp only [Nat.cast_add, add_sub_cancel_left, N₂_nat]
  dsimp [residual]
  ring

lemma koszulCoefficient_below_degree {d r t : ℕ} (ht : t < d) :
    koszulCoefficient d r t = N t := by
  let F : ℕ → ℤ := fun k =>
    (-1 : ℤ)^k * (r.choose k : ℤ) * N₂ ((t : ℤ) - (k : ℤ) * d)
  have hsum : (∑ k ∈ Finset.range 1, F k) = ∑ k ∈ Finset.range (r + 1), F k := by
    apply Finset.sum_subset (Finset.range_subset_range.mpr (show 1 ≤ r + 1 by omega))
    intro k hk hknot
    have hk1 : 1 ≤ k := by simp only [Finset.mem_range] at hknot; omega
    have hkd : d ≤ k * d := by simpa using Nat.mul_le_mul_right d hk1
    have hnegative : (t : ℤ) - (k : ℤ) * d < 0 := by
      have hcast : (t : ℤ) < (k : ℤ) * d := by exact_mod_cast (by omega : t < k * d)
      omega
    simp [F, N₂_neg hnegative]
  change (∑ k ∈ Finset.range (r + 1), F k) = _
  rw [← hsum]
  simp [F]

lemma koszulPrefixHit_iff_cutoff_le {d p : ℕ}
    (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : 3 ≤ N d - p) (e : ℕ) :
    koszulPrefixHit d p e ↔ cutoff d (N d - p) ≤ e := by
  let r := N d - p
  have hr' : 3 ≤ r := hr
  have hrd := (generator_count_bounds (by omega) hlo hhi).2
  have hcut : cutoff d r < d := cutoff_lt_degree hd hr' hrd
  have hcast : (N d : ℤ) - r = (p : ℤ) := by
    dsimp [r]
    rw [Nat.cast_sub hhi.le]
    ring
  constructor
  · rintro ⟨q, hq, hqe, hhit⟩
    by_cases hqd : q < d
    · rw [koszulCoefficient_at_excess_before_second (by omega : 1 ≤ r) hqd,
        hcast] at hhit
      exact ((residual_nonpos_iff_cutoff_le hr' hq).mp (by omega)).trans hqe
    · change cutoff d r ≤ e
      omega
  · intro he
    refine ⟨cutoff d r, cutoff_pos d r, he, ?_⟩
    rw [koszulCoefficient_at_excess_before_second (by omega : 1 ≤ r) hcut, hcast]
    have := residual_nonpos_at_cutoff (d := d) hr'
    omega

/-- One equation has a strictly increasing quotient coefficient in positive
excess degree, so its positive cutoff is infinite. -/
lemma completeIntersectionCoefficient_one_excess (d e : ℕ) :
    completeIntersectionCoefficient d 1 (d + e) = (N d : ℤ) - 1 + (d : ℤ) * e := by
  have h := twice_residual d 1 e
  simp only [Nat.cast_one] at h
  have hc : completeIntersectionCoefficient d 1 (d + e) =
      (N d : ℤ) - 1 + residual d 1 e := by
    simp only [completeIntersectionCoefficient, Nat.cast_add, add_sub_cancel_left,
      N₂_nat]
    norm_num
    rw [show (d : ℤ) + e = ((d + e : ℕ) : ℤ) by push_cast; rfl, N₂_nat]
    dsimp [residual]
    ring
  rw [hc]
  nlinarith

/-- Past the second Koszul shift the two-equation coefficient is `d²`. -/
lemma completeIntersectionCoefficient_two_late {d e : ℕ} (he : d ≤ e) :
    completeIntersectionCoefficient d 2 (d + e) = (d : ℤ)^2 := by
  have hshift : ((d + e : ℕ) : ℤ) - 2 * d = ((e - d : ℕ) : ℤ) := by
    rw [Nat.cast_sub he]
    push_cast
    ring
  have h0 := twice_N (d + e)
  have h1 := twice_N e
  have h2 := twice_N (e - d)
  rw [Nat.cast_sub he] at h2
  push_cast at h0
  simp only [completeIntersectionCoefficient]
  rw [hshift, show ((d + e : ℕ) : ℤ) - d = (e : ℤ) by push_cast; ring,
    N₂_nat, N₂_nat, N₂_nat]
  norm_num
  nlinarith

/-- In the minimal-degree range two equations never give a coefficient below
the point count. A positive equality can occur only for two quadrics. -/
lemma completeIntersectionCoefficient_two_ge_point {d p e : ℕ}
    (hd : 2 ≤ d) (hcount : p = N d - 2) :
    (p : ℤ) ≤ completeIntersectionCoefficient d 2 (d + e) := by
  have hn : 2 ≤ N d := by have := N_ge_degree_add_one d; omega
  have hp : (p : ℤ) = (N d : ℤ) - 2 := by
    rw [hcount, Nat.cast_sub hn]
    norm_num
  by_cases he : e < d
  · rw [← koszulCoefficient_small d 2 (d + e) (by decide),
      koszulCoefficient_at_excess_before_second (by decide) he]
    norm_num only [Nat.cast_ofNat]
    rw [← hp]
    have h := twice_residual d 2 e
    norm_num only [Nat.cast_ofNat, mul_one, sub_self, sub_zero] at h
    have hdZ : 2 ≤ (d : ℤ) := by exact_mod_cast hd
    have heZ : (e : ℤ) ≤ (d : ℤ) - 1 := by omega
    have hfactor : 0 ≤ 2 * (d : ℤ) - 3 - e := by omega
    have hproduct := mul_nonneg (show 0 ≤ (e : ℤ) by omega) hfactor
    nlinarith
  · rw [completeIntersectionCoefficient_two_late (by omega)]
    have h := twice_N d
    have hdZ : 2 ≤ (d : ℤ) := by exact_mod_cast hd
    rw [hp]
    nlinarith

lemma completeIntersectionCoefficient_two_hit_degree {d p q : ℕ}
    (hd : 2 ≤ d) (hcount : p = N d - 2) (hq : 1 ≤ q)
    (hhit : completeIntersectionCoefficient d 2 (d + q) ≤ p) : d = 2 := by
  have hn : 2 ≤ N d := by have := N_ge_degree_add_one d; omega
  have hp : (p : ℤ) = (N d : ℤ) - 2 := by
    rw [hcount, Nat.cast_sub hn]
    norm_num
  by_cases hqd : q < d
  · rw [← koszulCoefficient_small d 2 (d + q) (by decide),
      koszulCoefficient_at_excess_before_second (by decide) hqd] at hhit
    norm_num only [Nat.cast_ofNat] at hhit
    rw [← hp] at hhit
    have h := twice_residual d 2 q
    norm_num only [Nat.cast_ofNat, mul_one, sub_self, sub_zero] at h
    have hqZ : 0 < (q : ℤ) := by omega
    have hf : 2 * (d : ℤ) - 3 - q ≤ 0 := by
      apply nonpos_of_mul_nonpos_right _ hqZ
      nlinarith
    omega
  · rw [completeIntersectionCoefficient_two_late (by omega), hp] at hhit
    have h := twice_N d
    have hdZ : 2 ≤ (d : ℤ) := by exact_mod_cast hd
    have hle : d ≤ 2 := by nlinarith
    omega

lemma completeIntersectionCoefficient_two_quadrics {e : ℕ} (he : 1 ≤ e) :
    completeIntersectionCoefficient 2 2 (2 + e) = 4 := by
  by_cases he2 : 2 ≤ e
  · rw [completeIntersectionCoefficient_two_late he2]
    norm_num
  · have : e = 1 := by omega
    subst e
    norm_num [completeIntersectionCoefficient, N₂, N]
    decide

lemma koszulPrefixHit_none_of_full_count {d p : ℕ} (hcount : p = N d) (e : ℕ) :
    ¬ koszulPrefixHit d p e := by
  rintro ⟨q, hq, _, hhit⟩
  rw [hcount, Nat.sub_self, koszulCoefficient_zero] at hhit
  have hlt : N d < N (d + q) := N_strictMono (by omega)
  exact (by exact_mod_cast hlt : (N d : ℤ) < N (d + q)).not_ge hhit

lemma koszulPrefixHit_none_of_one_generator {d p : ℕ}
    (hd : 1 ≤ d) (hr : N d - p = 1) (e : ℕ) :
    ¬ koszulPrefixHit d p e := by
  rintro ⟨q, hq, _, hhit⟩
  rw [hr, koszulCoefficient_small d 1 (d + q) (by decide),
    completeIntersectionCoefficient_one_excess] at hhit
  have hp : (N d : ℤ) - 1 = (p : ℤ) := by omega
  rw [hp] at hhit
  have hprod : 0 < (d : ℤ) * q := mul_pos (by omega) (by omega)
  omega

lemma koszulCoefficient_small_ge_point {d p : ℕ}
    (hd : 1 ≤ d) (hlo : N (d - 1) < p) (hupper : p ≤ N d)
    (hr : N d - p ≤ 2) (e : ℕ) :
    (p : ℤ) ≤ koszulCoefficient d (N d - p) (d + e) := by
  by_cases hr0 : N d - p = 0
  · rw [hr0, koszulCoefficient_zero]
    exact_mod_cast hupper.trans (N_monotone (by omega : d ≤ d + e))
  by_cases hr1 : N d - p = 1
  · rw [hr1, koszulCoefficient_small d 1 (d + e) (by decide),
      completeIntersectionCoefficient_one_excess]
    have hp : (N d : ℤ) - 1 = (p : ℤ) := by omega
    have : 0 ≤ (d : ℤ) * e := mul_nonneg (by omega) (by omega)
    omega
  · have hr2 : N d - p = 2 := by omega
    have hhi : p < N d := by omega
    have hbound := (generator_count_bounds hd hlo hhi).2
    have hd2 : 2 ≤ d := by omega
    rw [hr2, koszulCoefficient_small d 2 (d + e) (by decide)]
    exact completeIntersectionCoefficient_two_ge_point hd2 (by omega)

lemma koszulCoefficient_eq_point_of_small_hit {d p e : ℕ}
    (hd : 1 ≤ d) (hlo : N (d - 1) < p) (hupper : p ≤ N d)
    (hr : N d - p ≤ 2) (hhit : koszulPrefixHit d p e) :
    koszulCoefficient d (N d - p) (d + e) = p := by
  by_cases hr0 : N d - p = 0
  · exact False.elim (koszulPrefixHit_none_of_full_count (by omega) e hhit)
  by_cases hr1 : N d - p = 1
  · exact False.elim (koszulPrefixHit_none_of_one_generator hd hr1 e hhit)
  have hr2 : N d - p = 2 := by omega
  have hhi : p < N d := by omega
  have hbound := (generator_count_bounds hd hlo hhi).2
  have hd2 : 2 ≤ d := by omega
  rcases hhit with ⟨q, hq, hqe, hhit⟩
  rw [hr2, koszulCoefficient_small d 2 (d + q) (by decide)] at hhit
  have hdEq := completeIntersectionCoefficient_two_hit_degree hd2 (by omega) hq hhit
  subst d
  have hp : p = 4 := by norm_num [N, Nat.choose] at hr2; omega
  rw [hr2, koszulCoefficient_small 2 2 (2 + e) (by decide),
    completeIntersectionCoefficient_two_quadrics (by omega), hp]
  rfl

lemma expectedSyzygyCoefficient_small_excess {d p : ℕ}
    (hd : 1 ≤ d) (hlo : N (d - 1) < p) (hupper : p ≤ N d)
    (hr : N d - p ≤ 2) (e : ℕ) :
    expectedSyzygyCoefficient d p (d + e) =
      completeIntersectionCoefficient d (N d - p) (d + e) := by
  classical
  simp only [expectedSyzygyCoefficient, show ¬d + e < d by omega, ite_false,
    Nat.add_sub_cancel_left]
  by_cases hhit : koszulPrefixHit d p e
  · rw [ite_eq_left hhit, ← koszulCoefficient_small d (N d - p) (d + e) hr,
      koszulCoefficient_eq_point_of_small_hit hd hlo hupper hr hhit]
  · rw [ite_eq_right hhit, koszulCoefficient_small d (N d - p) (d + e) hr]

/-- In the genuine many-generator range the full Koszul truncation agrees
with the residual maximum, because its first hit occurs before degree `2d`. -/
lemma expectedSyzygyCoefficient_many_excess {d p : ℕ}
    (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : 3 ≤ N d - p) (e : ℕ) :
    expectedSyzygyCoefficient d p (d + e) =
      ((max p (N (d + e) - (N d - p) * N e) : ℕ) : ℤ) := by
  classical
  let r := N d - p
  have hr' : 3 ≤ r := hr
  have hrd := (generator_count_bounds (by omega) hlo hhi).2
  have hcut : cutoff d r < d := cutoff_lt_degree hd hr' hrd
  have hp : (N d : ℤ) - r = (p : ℤ) := by
    dsimp [r]
    rw [Nat.cast_sub hhi.le]
    ring
  have hraw : (N (d + e) : ℤ) - (r : ℤ) * N e =
      (p : ℤ) + residual d r e := by dsimp [residual]; omega
  rw [cast_max_sub]
  change expectedSyzygyCoefficient d p (d + e) =
    max (p : ℤ) ((N (d + e) : ℤ) - (r : ℤ) * N e)
  rw [hraw]
  simp only [expectedSyzygyCoefficient, show ¬d + e < d by omega, ite_false,
    Nat.add_sub_cancel_left]
  by_cases hhit : koszulPrefixHit d p e
  · rw [ite_eq_left hhit]
    have he := (koszulPrefixHit_iff_cutoff_le hd hlo hhi hr e).mp hhit
    have hn := (residual_nonpos_iff_cutoff_le hr' ((cutoff_pos d r).trans he)).mpr he
    omega
  · rw [ite_eq_right hhit]
    have he : e < cutoff d r := by
      have := (koszulPrefixHit_iff_cutoff_le hd hlo hhi hr e).not.mp hhit
      change ¬cutoff d r ≤ e at this
      omega
    rw [koszulCoefficient_at_excess_before_second (by omega : 1 ≤ r) (by omega), hp]
    by_cases he0 : e = 0
    · subst e
      simp
    · have hpos := (residual_pos_iff_lt_cutoff hr' (by omega : 1 ≤ e)).mpr he
      omega

/-- The main theorem's piecewise formula is proved equal to the independent,
full Koszul positive-prefix expectation at the conjecture's minimal degree. -/
theorem expectedSyzygyCoefficient_eq_expectedChoppedHilbertFunction {d p : ℕ}
    (hd : 1 ≤ d) (hmin : IsExpectedSyzygyDegree d p) (t : ℕ) :
    expectedSyzygyCoefficient d p t = (expectedChoppedHilbertFunction d p t : ℤ) := by
  classical
  by_cases ht : t < d
  · simp [expectedSyzygyCoefficient, expectedChoppedHilbertFunction, ht]
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ t)
  have hlo := isExpectedSyzygyDegree_lower hmin hd
  by_cases hhi : N d ≤ p
  · have hcount : p = N d := Nat.le_antisymm hmin.1 hhi
    have hr0 : N d - p = 0 := by omega
    simp [expectedSyzygyCoefficient, expectedChoppedHilbertFunction,
      show ¬d + e < d by omega, hhi, hr0,
      koszulPrefixHit_none_of_full_count hcount e, koszulCoefficient_zero]
  have hhi' : p < N d := by omega
  have hlofalse : ¬p ≤ N (d - 1) := by omega
  by_cases hr : N d - p ≤ 2
  · rw [expectedSyzygyCoefficient_small_excess hd hlo hmin.1 hr]
    simp only [expectedChoppedHilbertFunction, show ¬d + e < d by omega,
      ite_false, hhi, hlofalse, hr, ite_true]
    have hn := koszulCoefficient_small_ge_point hd hlo hmin.1 hr e
    rw [koszulCoefficient_small d (N d - p) (d + e) hr] at hn
    exact (Int.toNat_of_nonneg (by omega)).symm
  · have hr' : 3 ≤ N d - p := by omega
    have hd2 : 2 ≤ d := by
      have := (generator_count_bounds hd hlo hhi').2
      omega
    rw [expectedSyzygyCoefficient_many_excess hd2 hlo hhi' hr']
    simp [expectedChoppedHilbertFunction, show ¬d + e < d by omega,
      hhi, hlofalse, hr]

variable {K : Type*} [Field K]

/-- The genuine chopped quotient has the literal expected Koszul coefficients.
The degree is the least one whose form dimension reaches the point count. -/
def ExpectedSyzygyConclusion {p : ℕ} (a : PointCoordinates K p) (d : ℕ) : Prop :=
  IsExpectedSyzygyDegree d p ∧ DistinctPoints K a ∧
  (∀ t, pointHilbertFunction K a t = min (N t) p) ∧
  ∀ t, (choppedHilbertFunction a d t : ℤ) = expectedSyzygyCoefficient d p t

/-- One nonempty polynomial open supplies the Expected Syzygy Conjecture in
all degrees simultaneously. -/
def GenericExpectedSyzygyConclusion (K : Type*) [Field K] (p : ℕ) : Prop :=
  ∃ D : MvPolynomial (Fin p × Fin 2) K,
    (∃ a, MvPolynomial.eval a D ≠ 0) ∧
    ∀ a, MvPolynomial.eval a D ≠ 0 →
      ExpectedSyzygyConclusion (K := K) a (expectedSyzygyDegree p)

/-- Corollary 5.1 follows from the full main conclusion by a proved numerical
comparison, with no additional expectation hypothesis. -/
theorem expectedSyzygyConclusion_of_mainConclusion {d p : ℕ}
    {a : PointCoordinates K p} (hd : 1 ≤ d) (hmin : IsExpectedSyzygyDegree d p)
    (hmain : MainConclusion K a d) : ExpectedSyzygyConclusion a d := by
  refine ⟨hmin, hmain.1, hmain.2.1, ?_⟩
  intro t
  rw [hmain.2.2.1 t, ← expectedSyzygyCoefficient_eq_expectedChoppedHilbertFunction hd hmin t]

lemma expectedSyzygyCoefficient_degree_zero_one (t : ℕ) :
    expectedSyzygyCoefficient 0 1 t = N t := by
  classical
  have hn : ¬koszulPrefixHit 0 1 t :=
    koszulPrefixHit_none_of_full_count (d := 0) (p := 1) (by simp) t
  simp [expectedSyzygyCoefficient, hn, koszulCoefficient_zero]

/-- The sole positive-point-count case in minimal degree zero has the actual
zero chop and satisfies the full coefficient formula over every field. -/
theorem expectedSyzygyConclusion_degree_zero (a : PointCoordinates K 1) :
    ExpectedSyzygyConclusion a 0 := by
  refine ⟨⟨by simp, by intro t ht; omega⟩, ?_, ?_, ?_⟩
  · intro i j h
    exact Subsingleton.elim i j
  · intro t
    have hdim : pointHilbertFunction K a t = 1 := by
      have h0 : Function.Surjective (pointEvaluation K a 0) := by
        intro y
        refine ⟨⟨MvPolynomial.C (y 0), MvPolynomial.isHomogeneous_C _ _⟩, ?_⟩
        ext i
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simp
      have ht := pointEvaluation_surjective_above a (Nat.zero_le t) h0
      rw [pointHilbertFunction_eq_rank, LinearMap.range_eq_top.mpr ht,
        finrank_top]
      simp
    have hn := N_ge_degree_add_one t
    omega
  · intro t
    rw [choppedHilbertFunction_zero a (by decide), expectedSyzygyCoefficient_degree_zero_one]

/-- The positive minimal degree-one cases need no main-theorem assumption. -/
theorem genericExpectedSyzygyConclusion_degree_one [CharZero K]
    (p : ℕ) (hmin : IsExpectedSyzygyDegree 1 p) :
    ∃ D : MvPolynomial (Fin p × Fin 2) K,
      (∃ a, MvPolynomial.eval a D ≠ 0) ∧
      ∀ a, MvPolynomial.eval a D ≠ 0 → ExpectedSyzygyConclusion (K := K) a 1 := by
  have hp : 1 ≤ p := by have := hmin.2 0 (by decide); simp only [N_zero] at this; omega
  obtain ⟨D, hD, hgood⟩ := genericChoppedConclusion_degree_one (K := K) p hp
  exact ⟨D, hD, fun a ha => expectedSyzygyConclusion_of_mainConclusion
    (by decide) hmin (hgood a ha)⟩

/-- Field-uniform Corollary 5.1. The sole current input is the complete main
statement; every truncation comparison and every degree-zero/one edge case
is proved here. -/
theorem genericExpectedSyzygyConclusion_of_mainStatement {K : Type} [Field K] [CharZero K]
    (hmain : MainStatement) (p : ℕ) (hp : 1 ≤ p) :
    GenericExpectedSyzygyConclusion K p := by
  let d := expectedSyzygyDegree p
  have hmin : IsExpectedSyzygyDegree d p := expectedSyzygyDegree_spec p
  by_cases hd0 : d = 0
  · have hp1 : p = 1 := by have := hmin.1; rw [hd0, N_zero] at this; omega
    subst p
    refine ⟨1, ?_, ?_⟩
    · exact ⟨fun _ => 0, by simp⟩
    · intro a ha
      change ExpectedSyzygyConclusion a d
      rw [hd0]
      exact expectedSyzygyConclusion_degree_zero a
  by_cases hd1 : d = 1
  · obtain ⟨D, hD, hgood⟩ := genericExpectedSyzygyConclusion_degree_one
      (K := K) p (hd1 ▸ hmin)
    refine ⟨D, hD, ?_⟩
    intro a ha
    change ExpectedSyzygyConclusion a d
    rw [hd1]
    exact hgood a ha
  · have hd2 : 2 ≤ d := by omega
    obtain ⟨D, hD, hgood⟩ := hmain K d p hd2 hp
    exact ⟨D, hD, fun a ha => expectedSyzygyConclusion_of_mainConclusion
      (by omega) hmin (hgood a ha)⟩

/-- The alternating contribution of the positive Koszul modules to the ideal
piece, in the exact indexing used by GKT Conjecture 1. -/
def koszulIdealCoefficient (d r t : ℕ) : ℤ :=
  ∑ k ∈ Finset.range r,
    (-1 : ℤ)^(k + 2) * (r.choose (k + 1) : ℤ) *
      N₂ ((t : ℤ) - ((k + 1 : ℕ) : ℤ) * d)

lemma koszulIdealCoefficient_eq (d r t : ℕ) :
    koszulIdealCoefficient d r t = (N t : ℤ) - koszulCoefficient d r t := by
  let F : ℕ → ℤ := fun k =>
    (-1 : ℤ)^k * (r.choose k : ℤ) * N₂ ((t : ℤ) - (k : ℤ) * d)
  have hsign : koszulIdealCoefficient d r t = -(∑ k ∈ Finset.range r, F (k + 1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hs : (-1 : ℤ)^(k + 2) = -((-1 : ℤ)^(k + 1)) := by
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      ring
    dsimp [F]
    rw [hs]
    ring
  rw [hsign]
  change -(∑ k ∈ Finset.range r, F (k + 1)) =
    (N t : ℤ) - ∑ k ∈ Finset.range (r + 1), F k
  rw [Finset.sum_range_succ']
  simp [F]

/-- The conjecture's expected dimension of the degree-`d+e` ideal piece. -/
def expectedSyzygyIdealCoefficient (d p e : ℕ) : ℤ := by
  classical
  exact if koszulPrefixHit d p e then (N (d + e) : ℤ) - p
    else koszulIdealCoefficient d (N d - p) (d + e)

lemma expectedSyzygyIdealCoefficient_eq (d p e : ℕ) :
    expectedSyzygyIdealCoefficient d p e =
      (N (d + e) : ℤ) - expectedSyzygyCoefficient d p (d + e) := by
  classical
  simp only [expectedSyzygyIdealCoefficient, expectedSyzygyCoefficient,
    show ¬d + e < d by omega, ite_false, Nat.add_sub_cancel_left]
  split_ifs <;> simp [koszulIdealCoefficient_eq]

/-- The original ideal-dimension formulation of the Expected Syzygy
Conjecture, on the actual homogeneous piece of the actual chopped ideal. -/
theorem expectedSyzygyConclusion_idealCoefficient {d p : ℕ}
    {a : PointCoordinates K p} (h : ExpectedSyzygyConclusion a d) (e : ℕ) :
    (Module.finrank K (idealFormPiece (choppedIdeal K a d) (d + e)) : ℤ) =
      expectedSyzygyIdealCoefficient d p e := by
  have hdim := (idealFormPiece (choppedIdeal K a d) (d + e)).finrank_quotient_add_finrank
  rw [finrank_idealFormQuotient, idealQuotientHilbertFunction_choppedIdeal,
    finrank_plane_forms] at hdim
  have hcast : (choppedHilbertFunction a d (d + e) : ℤ) +
      Module.finrank K (idealFormPiece (choppedIdeal K a d) (d + e)) = N (d + e) := by
    exact_mod_cast hdim
  rw [h.2.2.2 (d + e)] at hcast
  rw [expectedSyzygyIdealCoefficient_eq]
  omega

/-- The numerical cutoff is the actual least positive excess degree at which
the full Koszul coefficient reaches the point count. -/
theorem koszulPositiveCutoff_isLeast {d p : ℕ}
    (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : 3 ≤ N d - p) :
    IsLeast {e : ℕ | 1 ≤ e ∧ koszulCoefficient d (N d - p) (d + e) ≤ p}
      (cutoff d (N d - p)) := by
  have hprefix := (koszulPrefixHit_iff_cutoff_le hd hlo hhi hr
    (cutoff d (N d - p))).mpr le_rfl
  rcases hprefix with ⟨q, hq, hqcut, hhit⟩
  have hcutq := (koszulPrefixHit_iff_cutoff_le hd hlo hhi hr q).mp
    ⟨q, hq, le_rfl, hhit⟩
  have hqeq : q = cutoff d (N d - p) := Nat.le_antisymm hqcut hcutq
  subst q
  refine ⟨⟨cutoff_pos d (N d - p), hhit⟩, ?_⟩
  intro e he
  exact (koszulPrefixHit_iff_cutoff_le hd hlo hhi hr e).mp ⟨e, he.1, le_rfl, he.2⟩

lemma expectedSyzygyCoefficient_degree_zero_empty (t : ℕ) :
    expectedSyzygyCoefficient 0 0 t = 0 := by
  classical
  have hk : koszulCoefficient 0 1 t = 0 := by
    rw [koszulCoefficient_small 0 1 t (by decide)]
    simp [completeIntersectionCoefficient]
  simp [expectedSyzygyCoefficient, hk]

/-- The empty configuration at its minimal degree zero has the unit ideal
as its actual chop and has every Hilbert coefficient zero. -/
theorem expectedSyzygyConclusion_empty (a : PointCoordinates K 0) :
    ExpectedSyzygyConclusion a 0 := by
  refine ⟨⟨by simp, by intro t ht; omega⟩, ?_, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · intro t
    rw [pointHilbertFunction_empty]
    simp
  · intro t
    rw [choppedHilbertFunction_empty_above a 0 t (Nat.zero_le t),
      expectedSyzygyCoefficient_degree_zero_empty]
    rfl

/-- The empty-configuration corollary holds over every field. -/
theorem genericExpectedSyzygyConclusion_empty : GenericExpectedSyzygyConclusion K 0 := by
  have hd : expectedSyzygyDegree 0 = 0 := by
    have h := expectedSyzygyDegree_spec 0
    by_contra hnonzero
    have ht : 0 < expectedSyzygyDegree 0 := by omega
    have := h.2 0 ht
    simp at this
  refine ⟨1, ⟨fun _ => 0, by simp⟩, ?_⟩
  intro a ha
  rw [hd]
  exact expectedSyzygyConclusion_empty a

/-- The complete field-uniform statement of Corollary 5.1, with the empty
configuration included by direct computation. -/
def ExpectedSyzygyStatement : Prop :=
  ∀ (K : Type) [Field K] [CharZero K],
    ∀ p : ℕ, GenericExpectedSyzygyConclusion K p

/-- The full main statement implies the full Expected Syzygy Conjecture in
the plane. No extra numerical or geometric expectation is assumed. -/
theorem expectedSyzygyStatement_of_mainStatement (hmain : MainStatement) :
    ExpectedSyzygyStatement := by
  intro K _ _ p
  by_cases hp : p = 0
  · subst p
    exact genericExpectedSyzygyConclusion_empty
  · exact genericExpectedSyzygyConclusion_of_mainStatement hmain p (by omega)

end ChoppedPlane
