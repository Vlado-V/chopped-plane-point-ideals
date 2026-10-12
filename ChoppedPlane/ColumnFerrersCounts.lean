module

public import ChoppedPlane.ColumnFerrers
public import ChoppedPlane.FerrersCounts

@[expose] public section

/-! Exact cardinalities of the weak-upper-triangular column Ferrers diagrams. -/
namespace ChoppedPlane.ColumnFerrers
open scoped BigOperators
variable {c : ℕ}

/-- The weak upper triangle adds precisely the diagonal square blocks to the
strict upper triangle. -/
theorem selected_card_eq_diagonal_add_pairs (ε : Fin c → ℕ) :
    Fintype.card (SelectedIndex ε) = (∑ i, ε i ^ 2) + Ferrers.weightedPairs ε := by
  classical
  rw [selected_card]
  let w := fun ij : Fin c × Fin c => ε ij.1 * ε ij.2
  have hpoint (ij : Fin c × Fin c) :
      (if ij.1 ≤ ij.2 then w ij else 0) =
      (if ij.1 = ij.2 then ε ij.1 ^ 2 else 0) +
      (if ij.1 < ij.2 then w ij else 0) := by
    rcases lt_trichotomy ij.1 ij.2 with h | h | h
    · simp [h, le_of_lt h, ne_of_lt h]
    · simp [h, w, pow_two]
    · simp [not_le_of_gt h, ne_of_gt h, not_lt_of_gt h]
  have hweak : (∑ ij : Fin c × Fin c, if ij.1 ≤ ij.2 then w ij else 0) =
      ∑ ij : {ij : Fin c × Fin c // ij.1 ≤ ij.2}, w ij.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  have hdiag : (∑ ij : Fin c × Fin c, if ij.1 = ij.2 then ε ij.1 ^ 2 else 0) =
      ∑ i, ε i ^ 2 := by simp [Fintype.sum_prod_type]
  have hlt : (∑ ij : Fin c × Fin c, if ij.1 < ij.2 then w ij else 0) =
      Ferrers.weightedPairs ε := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (by simp) _
  change (∑ ij : {ij : Fin c × Fin c // ij.1 ≤ ij.2}, w ij.val) = _
  rw [← hweak]
  calc
    _ = ∑ ij : Fin c × Fin c,
      ((if ij.1 = ij.2 then ε ij.1 ^ 2 else 0) +
       (if ij.1 < ij.2 then w ij else 0)) := by
      apply Finset.sum_congr rfl
      intro ij _
      exact hpoint ij
    _ = _ := by rw [Finset.sum_add_distrib, hdiag, hlt]

/-- The universal doubled cardinality formula for the column profile. -/
theorem selected_card_square (ε : Fin c → ℕ) :
    2 * Fintype.card (SelectedIndex ε) = (∑ i, ε i) ^ 2 + (∑ i, ε i ^ 2) := by
  rw [selected_card_eq_diagonal_add_pairs]
  have h := Ferrers.weightedPairs_square ε
  omega

/-- For a column profile of total degree `d` and `q = d + 1 - r`
quadratic entries, the actual seed has `N(d) - r` selected points. -/
theorem selected_card_of_sums (ε : Fin c → ℕ) (d r q : ℕ)
    (hsum : (∑ i, ε i) = d)
    (hsquares : (∑ i, ε i ^ 2) = d + 2 * q)
    (hq : q + r = d + 1) :
    Fintype.card (SelectedIndex ε) = (d + 2).choose 2 - r := by
  have hsq := selected_card_square ε
  rw [hsum, hsquares] at hsq
  have hN : 2 * N d = (d + 1) * (d + 2) := by exact_mod_cast twice_N d
  have hcount : Fintype.card (SelectedIndex ε) + r = N d := by nlinarith
  change Fintype.card (SelectedIndex ε) = N d - r
  omega


/-- Any positive column profile with only linear and quadratic entries already
has exactly the point count required by its Hilbert–Burch generating degree. -/
theorem selected_card_one_two (ε : Fin c → ℕ) (hε : ∀ j, ε j = 1 ∨ ε j = 2) :
    Fintype.card (SelectedIndex ε) = N (∑ j, ε j) - (c + 1) := by
  classical
  let q := (Finset.univ.filter (fun j => ε j = 2)).card
  have hpoint (j : Fin c) : ε j = 1 + (if ε j = 2 then 1 else 0) := by
    rcases hε j with hj | hj <;> simp [hj]
  have hsum : (∑ j, ε j) = c + q := by
    calc
      _ = ∑ j : Fin c, (1 + (if ε j = 2 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hpoint j
      _ = _ := by simp [Finset.sum_add_distrib, q]
  have hsquarepoint (j : Fin c) :
      ε j ^ 2 = ε j + 2 * (if ε j = 2 then 1 else 0) := by
    rcases hε j with hj | hj <;> simp [hj]
  have hsquares : (∑ j, ε j ^ 2) = (∑ j, ε j) + 2 * q := by
    calc
      _ = ∑ j : Fin c, (ε j + 2 * (if ε j = 2 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hsquarepoint j
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp [q]
  apply selected_card_of_sums ε (∑ j, ε j) (c + 1) q rfl hsquares
  omega

/-- The column profile with `q` quadratics among `c` positive entries. -/
def columnProfile (c q : ℕ) : Fin c → ℕ := fun i => if i.val < q then 2 else 1

theorem columnProfile_pos (c q : ℕ) (i : Fin c) : 0 < columnProfile c q i := by
  unfold columnProfile
  split_ifs <;> omega

theorem columnProfile_sum (c q : ℕ) (hq : q ≤ c) :
    (∑ i, columnProfile c q i) = c + q := by
  let e : Fin (q + (c - q)) ≃ Fin c := finCongr (by omega)
  have he (i : Fin (q + (c - q))) :
      Ferrers.positiveProfile q (c - q) i = columnProfile c q (e i) := by
    simp [Ferrers.positiveProfile, columnProfile, e]
  have h := Fintype.sum_equiv e (Ferrers.positiveProfile q (c - q)) (columnProfile c q) he
  rw [Ferrers.positiveProfile_sum] at h
  omega

theorem columnProfile_square_sum (c q : ℕ) (hq : q ≤ c) :
    (∑ i, columnProfile c q i ^ 2) = c + 3 * q := by
  let e : Fin (q + (c - q)) ≃ Fin c := finCongr (by omega)
  have he (i : Fin (q + (c - q))) :
      Ferrers.positiveProfile q (c - q) i ^ 2 = columnProfile c q (e i) ^ 2 := by
    simp [Ferrers.positiveProfile, columnProfile, e]
  have h := Fintype.sum_equiv e (fun i => Ferrers.positiveProfile q (c - q) i ^ 2)
    (fun i => columnProfile c q i ^ 2) he
  rw [Ferrers.positiveProfile_square_sum] at h
  omega

/-- The nonpositive-extra-generator range uses `c = r - 1` columns and
`q = d + 1 - r` quadratic columns. -/
theorem columnProfile_selected_card {d r : ℕ} (hr : 1 ≤ r) (hupper : r ≤ d + 1)
    (hlower : d + 2 ≤ 2 * r) :
    Fintype.card (SelectedIndex (columnProfile (r - 1) (d + 1 - r))) =
      (d + 2).choose 2 - r := by
  have hq : d + 1 - r ≤ r - 1 := by omega
  apply selected_card_of_sums _ d r (d + 1 - r)
  · rw [columnProfile_sum _ _ hq]
    omega
  · rw [columnProfile_square_sum _ _ hq]
    omega
  · omega

end ChoppedPlane.ColumnFerrers
