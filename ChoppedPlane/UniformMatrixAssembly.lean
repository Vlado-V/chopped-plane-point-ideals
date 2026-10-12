module

public import ChoppedPlane.MatrixWitness

@[expose] public section

/-! Balanced sums reduce arbitrary column excess to excess two and three. -/
noncomputable section
namespace ChoppedPlane
variable {K : Type*} [Field K]

/-- The row budget can be split into one excess-three block and balanced
excess-two blocks with common rank thresholds. -/
theorem odd_block_row_budget (a k m : ℕ)
    (hlow : (2*k+3)*m ≤ 2*a) (hhigh : 2*a < (2*k+3)*(m+1)) :
    ∃ A r : ℕ, r ≤ k ∧ a = A + (k*m+r) ∧
      3*m ≤ 2*A ∧ 2*A ≤ 3*(m+1) := by
  let lo := (3*m+1)/2
  let hi := 3*(m+1)/2
  have halow : k*m+lo ≤ a := by
    have h : 2*(k*m)+3*m ≤ 2*a := by nlinarith [hlow]
    dsimp [lo]
    omega
  have hahigh : a ≤ k*m+k+hi := by
    have h : 2*a < 2*(k*m)+2*k+3*m+3 := by nlinarith [hhigh]
    dsimp [hi]
    omega
  have hlohi : lo ≤ hi := by dsimp [lo, hi]; omega
  let A := max lo (a-(k*m+k))
  have hAlo : lo ≤ A := le_max_left _ _
  have hAhi : A ≤ hi := by dsimp [A]; omega
  have hAa : k*m+A ≤ a := by dsimp [A]; omega
  let r := a-(k*m+A)
  refine ⟨A, r, ?_, ?_, ?_, ?_⟩
  · dsimp [r, A]
    omega
  · dsimp [r]
    omega
  · dsimp [lo] at hAlo
    omega
  · dsimp [hi] at hAhi
    omega

/-- Honest excess-three witnesses supply every odd excess. This lemma only
assembles already proved matrix ranks; it introduces no geometric input. -/
theorem exists_odd_extra_columns_maximalRank_of_three
    (hthree : ∀ A : ℕ, ∃ L : LinearMatrix K A (A+3),
      ∀ t, LinearMatrixMaximalRank L t)
    (a k : ℕ) :
    ∃ L : LinearMatrix K a (a+(2*k+3)),
      ∀ t, LinearMatrixMaximalRank L t := by
  let m := 2*a/(2*k+3)
  have hlo : (2*k+3)*m ≤ 2*a := by
    dsimp [m]
    simpa [Nat.mul_comm] using Nat.div_mul_le_self (2*a) (2*k+3)
  have hhi : 2*a < (2*k+3)*(m+1) := by
    dsimp [m]
    exact Nat.lt_mul_div_succ (2*a) (by omega)
  obtain ⟨A, r, hr, ha, hAlo, hAhi⟩ := odd_block_row_budget a k m hlo hhi
  obtain ⟨L₃, hmax₃⟩ := hthree A
  obtain ⟨L₂, hinj₂, hsurj₂⟩ := exists_balanced_toeplitz_blocks (K := K) k m r hr
  have hcol : a+(2*k+3) = (A+3)+(k*m+r+2*k) := by omega
  rw [hcol, ha]
  refine ⟨linearMatrixBlock L₃ L₂, ?_⟩
  intro t
  by_cases ht : t < m
  · apply linearMatrixMaximalRank_of_injective
    apply linearMatrixBlock_injective
    · apply (linearMatrixMaximalRank_iff_injective L₃ t
        ((matrixSource_le_target_iff K A (A+3) t).mpr ?_)).mp (hmax₃ t)
      have h : 3*(t+1) ≤ 2*A := by omega
      nlinarith
    · exact hinj₂ t ht
  · apply linearMatrixMaximalRank_of_surjective
    apply linearMatrixBlock_surjective
    · apply (linearMatrixMaximalRank_iff_surjective L₃ t
        ((matrixTarget_le_source_iff K A (A+3) t).mpr ?_)).mp (hmax₃ t)
      have h : 2*A ≤ 3*(t+1) := by omega
      nlinarith
    · exact hsurj₂ t (by omega)

/-- A uniform excess-three theorem completes the uniform all-excess theorem. -/
theorem exists_linearMatrix_maximalRank_of_three
    (hthree : ∀ A : ℕ, ∃ L : LinearMatrix K A (A+3),
      ∀ t, LinearMatrixMaximalRank L t)
    (a c : ℕ) (hac : a < c) (hgap : 2 ≤ c-a) :
    ∃ L : LinearMatrix K a c, ∀ t, LinearMatrixMaximalRank L t := by
  have hc : c = a+(c-a) := by omega
  by_cases heven : (c-a)%2 = 0
  · have h : c = a+2*((c-a)/2) := by omega
    rw [h]
    exact exists_even_extra_columns_maximalRank a ((c-a)/2) (by omega)
  · have h : c = a+(2*((c-a-3)/2)+3) := by omega
    rw [h]
    exact exists_odd_extra_columns_maximalRank_of_three hthree a ((c-a-3)/2)

end ChoppedPlane
