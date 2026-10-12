module

public import ChoppedPlane.HilbertBurch

@[expose] public section

/-! Integral coefficients can be descended from two coprime principal
localizations. This is the finite algebra step used in the odd-rank matrix
construction; it applies to every coefficient of a finite free module. -/
noncomputable section
namespace ChoppedPlane
open IsFractionRing IsLocalization

variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [Field F] [Algebra R F] [IsFractionRing R F]

/-- Two relatively prime integer multiples force a fraction to be integral. -/
theorem isInteger_of_coprime_integer_multiples (x : F) (u v : R)
    (huv : IsRelPrime u v)
    (hu : IsInteger R (algebraMap R F u * x))
    (hv : IsInteger R (algebraMap R F v * x)) : IsInteger R x := by
  apply isInteger_of_isUnit_den
  exact huv (reduced_den_dvd_of_integer_multiple x u hu)
    (reduced_den_dvd_of_integer_multiple x v hv)

/-- Membership in both principal localizations descends to the original UFD. -/
theorem isInteger_of_coprime_powers (x : F) (u v : R)
    (huv : IsRelPrime u v) (m n : ℕ)
    (hu : IsInteger R (algebraMap R F (u ^ m) * x))
    (hv : IsInteger R (algebraMap R F (v ^ n) * x)) : IsInteger R x := by
  exact isInteger_of_coprime_integer_multiples x _ _ (huv.pow (m := m) (n := n)) hu hv

/-- Coefficientwise descent for a free module from two principal localizations. -/
theorem free_coefficients_coprime_descent {ι : Type*} (x : ι → F) (u v : R)
    (huv : IsRelPrime u v)
    (h : ∀ i, (∃ m, IsInteger R (algebraMap R F (u ^ m) * x i)) ∧
      (∃ n, IsInteger R (algebraMap R F (v ^ n) * x i))) :
    ∃ y : ι → R, ∀ i, algebraMap R F (y i) = x i := by
  have hi (i : ι) : IsInteger R (x i) := by
    obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h i
    exact isInteger_of_coprime_powers (x i) u v huv m n hm hn
  exact Classical.axiomOfChoice hi

end ChoppedPlane
