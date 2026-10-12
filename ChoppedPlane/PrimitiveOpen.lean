module

public import ChoppedPlane.RegularPair
public import ChoppedPlane.HilbertBurch
public import ChoppedPlane.Saturation

@[expose] public section

/-! Coprime minors and degree cuts give actual primitive maximal-minor families.
The coprime pair is detected on a principal polynomial open. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K] {c d : ℕ}

/-- A common divisor of all maximal minors divides the entire cofactor ideal. -/
theorem cofactorIdeal_le_principal_of_common_divisor
    {R : Type*} [CommRing R] (B : Matrix (Fin (c + 1)) (Fin c) R) (u : R)
    (hu : ∀ i, u ∣ maximalMinor B i) : cofactorIdeal B ≤ Ideal.span {u} := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change signedMaximalMinor B i ∈ Ideal.span ({u} : Set R)
  apply Ideal.mem_span_singleton.mpr
  exact dvd_mul_of_dvd_right (hu i) ((-1) ^ i.val)

/-- Relatively prime members of the minor ideal force primitive maximal minors. -/
theorem primitiveMaximalMinors_of_relPrime_ideal_pair
    {R : Type*} [CommRing R] (B : Matrix (Fin (c + 1)) (Fin c) R)
    (f g : R) (hf : f ∈ cofactorIdeal B) (hg : g ∈ cofactorIdeal B)
    (hcop : IsRelPrime f g) : PrimitiveMaximalMinors B := by
  intro u hu
  have hle := cofactorIdeal_le_principal_of_common_divisor B u hu
  exact hcop ((Ideal.mem_span_singleton).mp (hle hf))
    ((Ideal.mem_span_singleton).mp (hle hg))

/-- A polynomial family with a coprime equal-degree minor pair has primitive
maximal minors on a nonempty principal open containing the witness. -/
theorem primitiveMaximalMinors_principal_open_of_pair {ι : Type*}
    (F : (ι → K) → Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (q : (ι → K) → Fin 2 → Forms K 3 d) (hpoly : IsPolynomialFamily q)
    (i j : Fin (c + 1))
    (hqi : ∀ a, (q a 0).val = maximalMinor (F a) i)
    (hqj : ∀ a, (q a 1).val = maximalMinor (F a) j)
    (hd : 0 < d) (a₀ : ι → K)
    (h₀ : (q a₀ 0).val ≠ 0)
    (hcop₀ : IsRelPrime (q a₀ 0).val (q a₀ 1).val) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → PrimitiveMaximalMinors (F a) := by
  obtain ⟨D, hD, hgood⟩ := pair_regular_principal_open hd q hpoly a₀ h₀ hcop₀
  refine ⟨D, hD, fun a ha => primitiveMaximalMinors_of_relPrime_pair (F a) i j ?_⟩
  rw [← hqi a, ← hqj a]
  exact (hgood a ha).1

/-- The same rank-open argument applies to any equal-degree pair lying in the
cofactor ideal, including its signed maximal-minor generators. -/
theorem primitiveMaximalMinors_principal_open_of_ideal_pair {ι : Type*}
    (F : (ι → K) → Matrix (Fin (c + 1)) (Fin c) (Poly K 3))
    (q : (ι → K) → Fin 2 → Forms K 3 d) (hpoly : IsPolynomialFamily q)
    (hq : ∀ a i, (q a i).val ∈ cofactorIdeal (F a))
    (hd : 0 < d) (a₀ : ι → K)
    (h₀ : (q a₀ 0).val ≠ 0)
    (hcop₀ : IsRelPrime (q a₀ 0).val (q a₀ 1).val) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧
      ∀ a, eval a D ≠ 0 → PrimitiveMaximalMinors (F a) := by
  obtain ⟨D, hD, hgood⟩ := pair_regular_principal_open hd q hpoly a₀ h₀ hcop₀
  exact ⟨D, hD, fun a ha => primitiveMaximalMinors_of_relPrime_ideal_pair (F a)
    _ _ (hq a 0) (hq a 1) (hgood a ha).1⟩

/-- A binary degree cut makes the restricted minors primitive as soon as the
coordinate powers are relatively prime. -/
theorem primitiveMaximalMinors_of_binary_degree_cut
    (B : Matrix (Fin (c + 1)) (Fin c) (Poly K 2)) (N : ℕ)
    (hcut : ∀ f : Forms K 2 N, f.val ∈ cofactorIdeal B)
    (hcop : IsRelPrime (X (R := K) (0 : Fin 2)) (X (R := K) (1 : Fin 2))) :
    PrimitiveMaximalMinors B := by
  apply primitiveMaximalMinors_of_relPrime_ideal_pair B (X 0 ^ N) (X 1 ^ N)
  · exact hcut ⟨_, isHomogeneous_X_pow (0 : Fin 2) N⟩
  · exact hcut ⟨_, isHomogeneous_X_pow (1 : Fin 2) N⟩
  · exact hcop.pow

end ChoppedPlane
