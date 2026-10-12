module

public import Mathlib.Tactic

@[expose] public section

/-!
# Binary coefficient boundary lemma

The coefficient equations for `y bᵢ + z bᵢ₊₁ = 0` propagate along diagonals.
If the degree is smaller than the number of equations, each diagonal reaches
one of the two zero boundaries. This proof uses no division and no restriction
on the characteristic.
-/

namespace ChoppedPlane

variable {K : Type*} [AddZeroClass K]

/-- A coefficient below the row diagonal propagates to the left boundary. -/
theorem binary_coeff_lower_left {a t : ℕ} (A : ℕ → ℕ → K)
    (hleft : ∀ i < a, A (i + 1) 0 = 0)
    (hrec : ∀ i < a, ∀ j < t, A (i + 1) (j + 1) + A i j = 0)
    (j : ℕ) (hjt : j ≤ t) (i : ℕ) (hia : i ≤ a) (hji : j < i) :
    A i j = 0 := by
  induction j generalizing i with
  | zero =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      exact hleft r (by omega)
  | succ j ih =>
      obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
      have hprev : A r j = 0 := ih (by omega) r (by omega) (by omega)
      have h := hrec r (by omega) j (by omega)
      simpa only [hprev, add_zero] using h

/-- A coefficient with room above it propagates to the right boundary. -/
theorem binary_coeff_upper_right {a t : ℕ} (A : ℕ → ℕ → K)
    (hright : ∀ i < a, A i t = 0)
    (hrec : ∀ i < a, ∀ j < t, A (i + 1) (j + 1) + A i j = 0)
    (k : ℕ) (hkt : k ≤ t) (i : ℕ) (hik : i + k < a) :
    A i (t - k) = 0 := by
  induction k generalizing i with
  | zero =>
      simpa only [Nat.sub_zero] using hright i (by omega)
  | succ k ih =>
      have hprev : A (i + 1) (t - k) = 0 :=
        ih (by omega) (i + 1) (by omega)
      have hcol : t - k = (t - (k + 1)) + 1 := by omega
      rw [hcol] at hprev
      have h := hrec i (by omega) (t - (k + 1)) (by omega)
      simpa only [hprev, zero_add] using h

/-- Every binary coefficient is zero when the degree is below the row count. -/
theorem binary_coeff_boundary_zero {a t : ℕ} (A : ℕ → ℕ → K)
    (hleft : ∀ i < a, A (i + 1) 0 = 0)
    (hright : ∀ i < a, A i t = 0)
    (hrec : ∀ i < a, ∀ j < t, A (i + 1) (j + 1) + A i j = 0)
    (hta : t < a) (i : ℕ) (hia : i ≤ a) (j : ℕ) (hjt : j ≤ t) :
    A i j = 0 := by
  by_cases hji : j < i
  · exact binary_coeff_lower_left A hleft hrec j hjt i hia hji
  · have h := binary_coeff_upper_right A hright hrec (t - j) (by omega)
        i (by omega)
    have hcol : t - (t - j) = j := by omega
    simpa only [hcol] using h

end ChoppedPlane
