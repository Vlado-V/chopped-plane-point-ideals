module

public import Mathlib

@[expose] public section

/-! Numerical identities for the Hilbert function of a chopped plane point ideal.

All dimension formulas are expressed in `ℤ`. The central identity is doubled,
so that it does not silently rely on truncated natural-number subtraction or
division.
-/
namespace ChoppedPlane

/-- Dimension of ternary forms of nonnegative degree. -/
def N (t : ℕ) : ℕ := (t + 2).choose 2

@[simp] theorem N_zero : N 0 = 1 := by norm_num [N]

/-- The signed-degree convention of the paper. -/
def N₂ (t : ℤ) : ℤ := if 0 ≤ t then (N t.toNat : ℤ) else 0

@[simp] theorem N₂_nat (t : ℕ) : N₂ (t : ℤ) = (N t : ℤ) := by
  simp [N₂]

@[simp] theorem N₂_neg {t : ℤ} (h : t < 0) : N₂ t = 0 := by
  simp [N₂, not_le.mpr h]

theorem N_succ (t : ℕ) : N (t + 1) = N t + (t + 2) := by
  simp only [N]
  have h := Nat.choose_succ_succ (t + 2) 1
  simpa only [Nat.choose_one_right, Nat.add_comm] using h

/-- The polynomial identity for the dimension of degree `t` ternary forms. -/
theorem twice_N (t : ℕ) : 2 * (N t : ℤ) = (t + 1) * (t + 2) := by
  induction t with
  | zero => norm_num
  | succ t ih =>
    rw [N_succ]
    push_cast
    nlinarith


/-- The residual dimension before applying the nonnegativity truncation. -/
def residual (d r e : ℕ) : ℤ :=
  (N (d + e) : ℤ) - (r : ℤ) * (N e : ℤ) - ((N d : ℤ) - r)

/-- Twice the residual, avoiding all division conventions. -/
theorem twice_residual (d r e : ℕ) :
    2 * residual d r e = (e : ℤ) *
      (2 * (d : ℤ) + 3 - 3 * (r : ℤ) - ((r : ℤ) - 1) * (e : ℤ)) := by
  have hd := twice_N d
  have he := twice_N e
  have hde := twice_N (d + e)
  push_cast at hde
  dsimp [residual]
  nlinarith

/-- The paper's expression, with exact integer division. -/
theorem residual_as_half (d r e : ℕ) :
    residual d r e = ((e : ℤ) *
      (2 * (d : ℤ) + 3 - 3 * (r : ℤ) - ((r : ℤ) - 1) * (e : ℤ))) / 2 := by
  rw [← twice_residual]
  omega

@[simp] theorem residual_zero (d r : ℕ) : residual d r 0 = 0 := by
  simp [residual]

/-- The generator count in degree `d+1`. -/
def aCount (d r : ℕ) : ℤ := (d : ℤ) + 2 - 2 * (r : ℤ)

/-- The number of columns in the linear-block construction. -/
def cCount (d r : ℕ) : ℤ := (d : ℤ) + 1 - (r : ℤ)

theorem count_relation (d r : ℕ) : (r : ℤ) + aCount d r = cCount d r + 1 := by
  dsimp [aCount, cCount]
  ring

theorem count_difference (d r : ℕ) : cCount d r - aCount d r = (r : ℤ) - 1 := by
  dsimp [aCount, cCount]
  ring

theorem twice_N₂ {t : ℤ} (h : 0 ≤ t) :
    2 * N₂ t = (t + 1) * (t + 2) := by
  have ht := twice_N t.toNat
  simpa [N₂, h, Int.toNat_of_nonneg h] using ht

/-- The dimension polynomial also vanishes in degrees `-1` and `-2`. -/
theorem twice_N₂_ge_neg_two {t : ℤ} (h : -2 ≤ t) :
    2 * N₂ t = (t + 1) * (t + 2) := by
  by_cases ht : 0 ≤ t
  · exact twice_N₂ ht
  · have cases : t = -2 ∨ t = -1 := by omega
    rcases cases with rfl | rfl <;> norm_num [N₂]

/-- The cokernel dimension polynomial equals the residual for every `e ≥ 0`. -/
theorem block_dimension_identity (d r e : ℕ) :
    aCount d r * N₂ ((e : ℤ) - 1) - cCount d r * N₂ ((e : ℤ) - 2) =
      residual d r e := by
  have h₁ := twice_N₂_ge_neg_two (t := (e : ℤ) - 1) (by omega)
  have h₂ := twice_N₂_ge_neg_two (t := (e : ℤ) - 2) (by omega)
  have h₃ := twice_residual d r e
  dsimp [aCount, cCount]
  nlinarith

/-- With at most zero extra generators the residual is already nonpositive
in every positive excess degree. -/
theorem residual_nonpos_of_aCount_nonpos {d r e : ℕ}
    (hr : 3 ≤ r) (ha : aCount d r ≤ 0) (he : 1 ≤ e) :
    residual d r e ≤ 0 := by
  have h := twice_residual d r e
  have hlin : 2 * (d : ℤ) + 3 - 3 * (r : ℤ) -
      ((r : ℤ) - 1) * (e : ℤ) ≤ 0 := by
    dsimp [aCount] at ha
    have hr' : 3 ≤ (r : ℤ) := by exact_mod_cast hr
    have he' : 1 ≤ (e : ℤ) := by exact_mod_cast he
    nlinarith
  have he' : 0 ≤ (e : ℤ) := by omega
  have := mul_nonpos_of_nonneg_of_nonpos he' hlin
  omega


/-- The rational zero of the residual's decreasing linear factor. -/
def residualThreshold (d r : ℕ) : ℚ :=
  (2 * (d : ℚ) + 3 - 3 * (r : ℚ)) / ((r : ℚ) - 1)

/-- The least positive excess degree where the chopped ideal fills the point ideal. -/
def cutoff (d r : ℕ) : ℕ := max 1 ⌈residualThreshold d r⌉₊

theorem cutoff_pos (d r : ℕ) : 1 ≤ cutoff d r := le_max_left _ _

/-- Natural ceiling is integer ceiling truncated at zero. The outer maximum
makes this precisely the signed-ceiling convention in the paper. -/
theorem cutoff_as_intceil (d r : ℕ) :
    cutoff d r = max 1 (⌈residualThreshold d r⌉.toNat) := by
  rfl

theorem cutoff_le_iff {d r e : ℕ} (he : 1 ≤ e) :
    cutoff d r ≤ e ↔ residualThreshold d r ≤ (e : ℚ) := by
  simp only [cutoff, max_le_iff, he, true_and, Nat.ceil_le]

/-- For positive `e` the residual is nonpositive exactly at or past the cutoff. -/
theorem residual_nonpos_iff_cutoff_le {d r e : ℕ} (hr : 3 ≤ r) (he : 1 ≤ e) :
    residual d r e ≤ 0 ↔ cutoff d r ≤ e := by
  have heZ : 0 < (e : ℤ) := by omega
  have hrQ : 0 < (r : ℚ) - 1 := by
    have hrQ' : 3 ≤ (r : ℚ) := by exact_mod_cast hr
    linarith
  have hsign : residual d r e ≤ 0 ↔
      2 * (d : ℤ) + 3 - 3 * (r : ℤ) - ((r : ℤ) - 1) * (e : ℤ) ≤ 0 := by
    constructor
    · intro h
      apply nonpos_of_mul_nonpos_right _ heZ
      rw [← twice_residual]
      omega
    · intro h
      have hmul := mul_nonpos_of_nonneg_of_nonpos heZ.le h
      rw [← twice_residual] at hmul
      omega
  rw [hsign, cutoff_le_iff he]
  dsimp [residualThreshold]
  rw [div_le_iff₀ hrQ]
  have hcast :
      (2 * (d : ℤ) + 3 - 3 * (r : ℤ) - ((r : ℤ) - 1) * (e : ℤ) ≤ 0) ↔
      (2 * (d : ℚ) + 3 - 3 * (r : ℚ) - ((r : ℚ) - 1) * (e : ℚ) ≤ 0) := by
    exact_mod_cast (Iff.rfl :
      (2 * (d : ℤ) + 3 - 3 * (r : ℤ) - ((r : ℤ) - 1) * (e : ℤ) ≤ 0) ↔
      (2 * (d : ℤ) + 3 - 3 * (r : ℤ) - ((r : ℤ) - 1) * (e : ℤ) ≤ 0))
  rw [hcast]
  constructor <;> intro h <;> nlinarith

theorem residual_pos_iff_lt_cutoff {d r e : ℕ} (hr : 3 ≤ r) (he : 1 ≤ e) :
    0 < residual d r e ↔ e < cutoff d r := by
  rw [← not_le, residual_nonpos_iff_cutoff_le hr he, not_le]

theorem residual_nonpos_at_cutoff {d r : ℕ} (hr : 3 ≤ r) :
    residual d r (cutoff d r) ≤ 0 :=
  (residual_nonpos_iff_cutoff_le hr (cutoff_pos d r)).mpr le_rfl

/-- The cutoff really is the least positive degree with zero truncated residual. -/
theorem cutoff_is_least {d r : ℕ} (hr : 3 ≤ r) :
    IsLeast {e : ℕ | 1 ≤ e ∧ residual d r e ≤ 0} (cutoff d r) := by
  refine ⟨⟨cutoff_pos d r, residual_nonpos_at_cutoff hr⟩, ?_⟩
  intro e he
  exact (residual_nonpos_iff_cutoff_le hr he.1).mp he.2

/-- The zero is bounded by `d-3` whenever there are at least three generators. -/
theorem residualThreshold_le {d r : ℕ} (hr : 3 ≤ r) :
    residualThreshold d r ≤ (d : ℚ) - 3 := by
  have hrQ : 3 ≤ (r : ℚ) := by exact_mod_cast hr
  have hdQ : 0 ≤ (d : ℚ) := by positivity
  dsimp [residualThreshold]
  rw [div_le_iff₀ (by linarith : 0 < (r : ℚ) - 1)]
  nlinarith

/-- The first filled degree occurs strictly before degree `2d`. -/
theorem cutoff_lt_degree {d r : ℕ} (hd : 2 ≤ d) (hr : 3 ≤ r) (hrd : r ≤ d) :
    cutoff d r < d := by
  have hd3 : 3 ≤ d := by omega
  have hcast : ((d - 3 : ℕ) : ℚ) = (d : ℚ) - 3 := by
    rw [Nat.cast_sub hd3]
    norm_num
  have hceil : ⌈residualThreshold d r⌉₊ ≤ d - 3 := by
    rw [Nat.ceil_le, hcast]
    exact residualThreshold_le hr
  dsimp [cutoff]
  omega


/-- The two maximum formulas in Theorem 1.1 agree. -/
theorem hilbert_max_identity (d r e : ℕ) :
    max ((N d : ℤ) - r) ((N (d + e) : ℤ) - (r : ℤ) * (N e : ℤ)) =
      ((N d : ℤ) - r) + max (residual d r e) 0 := by
  dsimp [residual]
  omega

/-- Coefficient of the Hilbert–Burch numerator in degree `d+e`. -/
theorem hilbertBurch_coefficient_identity (d r e : ℕ) :
    (N (d + e) : ℤ) - (r : ℤ) * (N e : ℤ) -
      aCount d r * N₂ ((e : ℤ) - 1) +
      cCount d r * N₂ ((e : ℤ) - 2) = (N d : ℤ) - r := by
  have h := block_dimension_identity d r e
  dsimp [residual] at h
  linarith

/-- The cokernel maximum of the linear block is the residual maximum. -/
theorem block_max_identity (d r e : ℕ) :
    max (aCount d r * N₂ ((e : ℤ) - 1) -
      cCount d r * N₂ ((e : ℤ) - 2)) 0 = max (residual d r e) 0 := by
  rw [block_dimension_identity]

/-- If `a ≤ 0`, filling takes place in the first positive excess degree. -/
theorem cutoff_eq_one_of_aCount_nonpos {d r : ℕ}
    (hr : 3 ≤ r) (ha : aCount d r ≤ 0) : cutoff d r = 1 := by
  have h := residual_nonpos_of_aCount_nonpos hr ha (e := 1) le_rfl
  have hcut := (residual_nonpos_iff_cutoff_le hr (e := 1) le_rfl).mp h
  exact le_antisymm hcut (cutoff_pos d r)

/-- The intermediate point-count range gives `1 ≤ r ≤ d`. -/
theorem generator_count_bounds {d p : ℕ} (hd : 1 ≤ d)
    (hlo : N (d - 1) < p) (hhi : p < N d) :
    1 ≤ N d - p ∧ N d - p ≤ d := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  subst d
  have hdim : N n.succ = N n + n + 2 := by
    simpa [Nat.add_assoc] using N_succ n
  simp only [Nat.succ_sub_one] at hlo
  omega

/-- At and beyond the cutoff the residual truncation is identically zero. -/
theorem max_residual_eq_zero_of_cutoff_le {d r e : ℕ}
    (hr : 3 ≤ r) (he : cutoff d r ≤ e) : max (residual d r e) 0 = 0 := by
  have hepos : 1 ≤ e := (cutoff_pos d r).trans he
  exact max_eq_right ((residual_nonpos_iff_cutoff_le hr hepos).mpr he)

/-- The cutoff occurs before the second Koszul terms in degree `2d`. -/
theorem cutoff_before_second_koszul {d r : ℕ}
    (hd : 2 ≤ d) (hr : 3 ≤ r) (hrd : r ≤ d) : d + cutoff d r < 2 * d := by
  have h := cutoff_lt_degree hd hr hrd
  omega


/-- The signed Hilbert–Burch numerator coefficient. -/
def hbCoefficient (d r : ℕ) (t : ℤ) : ℤ :=
  N₂ t - (r : ℤ) * N₂ (t - d) -
    aCount d r * N₂ (t - d - 1) + cCount d r * N₂ (t - d - 2)

theorem hbCoefficient_below_degree {d r : ℕ} {t : ℤ} (ht : t < (d : ℤ)) :
    hbCoefficient d r t = N₂ t := by
  have h₀ : t - (d : ℤ) < 0 := by omega
  have h₁ : t - (d : ℤ) - 1 < 0 := by omega
  have h₂ : t - (d : ℤ) - 2 < 0 := by omega
  simp [hbCoefficient, N₂_neg h₀, N₂_neg h₁, N₂_neg h₂]

theorem hbCoefficient_at_or_above_degree (d r e : ℕ) :
    hbCoefficient d r (d + e) = (N d : ℤ) - r := by
  dsimp [hbCoefficient]
  have h₀ : (d : ℤ) + (e : ℤ) - (d : ℤ) = (e : ℤ) := by ring
  rw [h₀, N₂_nat]
  rw [show (d : ℤ) + (e : ℤ) = ((d + e : ℕ) : ℤ) by push_cast; rfl, N₂_nat]
  exact hilbertBurch_coefficient_identity d r e

/-- The complete coefficient formula, including negative degrees. -/
theorem hbCoefficient_formula (d r : ℕ) (t : ℤ) :
    hbCoefficient d r t = if t < (d : ℤ) then N₂ t else (N d : ℤ) - r := by
  split_ifs with h
  · exact hbCoefficient_below_degree h
  · have hnonneg : 0 ≤ t - (d : ℤ) := by omega
    have hrepr : t = (d : ℤ) + ((t - (d : ℤ)).toNat : ℤ) := by omega
    rw [hrepr]
    exact hbCoefficient_at_or_above_degree d r (t - (d : ℤ)).toNat

/-- Counts of the linear and quadratic columns in the nonpositive-`a` construction. -/
def linearColumnCount (d r : ℕ) : ℤ := 2 * (r : ℤ) - d - 2

def quadraticColumnCount (d r : ℕ) : ℤ := (d : ℤ) + 1 - r

theorem column_count_sum (d r : ℕ) :
    linearColumnCount d r + quadraticColumnCount d r = (r : ℤ) - 1 := by
  dsimp [linearColumnCount, quadraticColumnCount]
  ring

theorem column_degree_sum (d r : ℕ) :
    linearColumnCount d r + 2 * quadraticColumnCount d r = (d : ℤ) := by
  dsimp [linearColumnCount, quadraticColumnCount]
  ring

theorem nonpositive_hbCoefficient (d r : ℕ) (t : ℤ) :
    N₂ t - (r : ℤ) * N₂ (t - d) +
      linearColumnCount d r * N₂ (t - d - 1) +
      quadraticColumnCount d r * N₂ (t - d - 2) =
      if t < (d : ℤ) then N₂ t else (N d : ℤ) - r := by
  rw [← hbCoefficient_formula]
  dsimp [linearColumnCount, quadraticColumnCount, hbCoefficient, aCount, cCount]
  ring

theorem first_minor_degree (d r : ℕ) : 2 * ((r : ℤ) - 1) + aCount d r = (d : ℤ) := by
  dsimp [aCount]
  ring

theorem second_minor_degree (d r : ℕ) : 2 * (r : ℤ) + aCount d r - 1 = (d : ℤ) + 1 := by
  dsimp [aCount]
  ring

theorem cCount_pos {d r : ℕ} (hrd : r ≤ d) : 0 < cCount d r := by
  dsimp [cCount]
  omega

theorem linearColumnCount_nonneg {d r : ℕ} (ha : aCount d r ≤ 0) :
    0 ≤ linearColumnCount d r := by
  dsimp [linearColumnCount, aCount] at *
  omega

theorem quadraticColumnCount_pos {d r : ℕ} (hrd : r ≤ d) :
    0 < quadraticColumnCount d r := by
  exact cCount_pos hrd

/-- Positivity at a positive integer is exactly being below the rational zero. -/
theorem residual_pos_iff_lt_threshold {d r e : ℕ} (hr : 3 ≤ r) (he : 1 ≤ e) :
    0 < residual d r e ↔ (e : ℚ) < residualThreshold d r := by
  rw [← not_le, residual_nonpos_iff_cutoff_le hr he, cutoff_le_iff he, not_le]

/-- Coercing the natural Hilbert-function maximum gives the integer maximum. -/
theorem cast_max_sub (p n m : ℕ) :
    ((max p (n - m) : ℕ) : ℤ) = max (p : ℤ) ((n : ℤ) - (m : ℤ)) := by
  by_cases h : m ≤ n
  · simp [Nat.cast_max, Nat.cast_sub h]
  · have hn : n - m = 0 := by omega
    have hi : (n : ℤ) - (m : ℤ) ≤ (p : ℤ) := by omega
    simp [hn, max_eq_left hi]

/-- Natural-valued form of the main maximum identity. -/
theorem hilbert_max_nat_identity {d r : ℕ} (hr : r ≤ N d) (e : ℕ) :
    ((max (N d - r) (N (d + e) - r * N e) : ℕ) : ℤ) =
      ((N d : ℤ) - r) + max (residual d r e) 0 := by
  rw [cast_max_sub, Nat.cast_sub hr, Nat.cast_mul]
  exact hilbert_max_identity d r e


/-- There are at least `t+1` ternary forms of degree `t`. -/
theorem N_ge_degree_add_one (t : ℕ) : t + 1 ≤ N t := by
  have h := twice_N t
  have ht : 0 ≤ (t : ℤ) := by positivity
  have hi : (t : ℤ) + 1 ≤ (N t : ℤ) := by nlinarith
  exact_mod_cast hi

theorem point_count_positive {d r : ℕ} (hrd : r ≤ d) : 1 ≤ N d - r := by
  have h := N_ge_degree_add_one d
  omega

@[simp] theorem residual_one (d r : ℕ) : residual d r 1 = aCount d r := by
  have h := twice_residual d r 1
  dsimp [aCount]
  norm_num at h
  linarith

theorem block_rank_gap {d r : ℕ} (hr : 3 ≤ r) : 2 ≤ cCount d r - aCount d r := by
  rw [count_difference]
  omega

/-- The cutoff is bounded by the explicit integer upper bound from the paper. -/
theorem cutoff_le_max {d r : ℕ} (hd : 3 ≤ d) (hr : 3 ≤ r) :
    cutoff d r ≤ max 1 (d - 3) := by
  have hceil : ⌈residualThreshold d r⌉₊ ≤ d - 3 := by
    rw [Nat.ceil_le, Nat.cast_sub hd]
    norm_num
    exact residualThreshold_le hr
  exact max_le_max le_rfl hceil

end ChoppedPlane
