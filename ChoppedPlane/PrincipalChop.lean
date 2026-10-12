module

public import ChoppedPlane.ChoppedFunctions
public import ChoppedPlane.Numerics
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.MvPolynomial.Nilpotent
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-! The one-generator case of Theorem 1.1.  The one-dimensional hypothesis is
on the actual homogeneous evaluation kernel, and the resulting generator,
ideal equality, regular sequence and all Hilbert coefficients are proved. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K] {p d : ℕ}

/-- A one-dimensional evaluation kernel has a nonzero homogeneous generator. -/
theorem exists_principal_pointDegreeSpace (a : PointCoordinates K p)
    (hdim : finrank K (pointDegreePiece K a d) = 1) :
    ∃ f : Forms K 3 d, f.val ≠ 0 ∧
      pointDegreeSpace K a d = Submodule.span K {f.val} := by
  have hne : pointDegreePiece K a d ≠ ⊥ :=
    (Submodule.isAtom_iff_finrank_eq_one.mpr hdim).ne_bot
  obtain ⟨f, hf, hfzero⟩ := (pointDegreePiece K a d).ne_bot_iff.mp hne
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim hf hfzero
  refine ⟨f, ?_, ?_⟩
  · intro h
    apply hfzero
    exact Subtype.ext h
  · rw [pointDegreeSpace, hspan, Submodule.map_span]
    simp only [Set.image_singleton, Submodule.subtype_apply]

/-- Every nonzero homogeneous form of positive degree is a regular sequence
of length one in the genuine polynomial ring. -/
theorem nonzero_form_regular_singleton (f : Forms K 3 d) (hf : f.val ≠ 0)
    (hd : 0 < d) : RingTheory.Sequence.IsRegular (Poly K 3) [f.val] := by
  refine ⟨(RingTheory.Sequence.isWeaklyRegular_singleton_iff (Poly K 3) f.val).mpr ?_, ?_⟩
  · apply IsSMulRegular.of_right_eq_zero_of_smul
    intro x hx
    exact (mul_eq_zero.mp hx).resolve_left hf
  · change (⊤ : Ideal (Poly K 3)) ≠ Ideal.ofList [f.val] * ⊤
    rw [Ideal.mul_top, Ideal.ofList_singleton]
    intro htop
    have hu : IsUnit f.val := Ideal.span_singleton_eq_top.mp htop.symm
    have hzero := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    have hdeg := f.property.totalDegree hf
    omega

/-- Taking the ideal span after the coefficient-field span preserves the
single generator. -/
theorem choppedIdeal_eq_singleton_of_space_eq (a : PointCoordinates K p)
    (f : Forms K 3 d)
    (hspan : pointDegreeSpace K a d = Submodule.span K {f.val}) :
    choppedIdeal K a d = Ideal.span {f.val} := by
  rw [choppedIdeal, hspan]
  exact Submodule.span_span_of_tower K (Poly K 3) {f.val}

/-- The coefficient of `(1-u^d)/(1-u)^3` is the Hilbert function of the
actual principal chop in every degree. -/
theorem principal_chop_hilbert_coefficients (a : PointCoordinates K p)
    (f : Forms K 3 d) (hf : f.val ≠ 0)
    (hspan : pointDegreeSpace K a d = Submodule.span K {f.val}) (t : ℕ) :
    (choppedHilbertFunction a d t : ℤ) = N₂ t - N₂ ((t : ℤ) - d) := by
  by_cases ht : t < d
  · rw [choppedHilbertFunction_below_degree a ht, N₂_nat,
      N₂_neg (by omega : (t : ℤ) - d < 0)]
    simp [N]
  · have hdt : d ≤ t := by omega
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdt
    have hN : N e ≤ N (d + e) := Nat.choose_le_choose 2 (by omega)
    have heZ : ((d + e : ℕ) : ℤ) - d = (e : ℤ) := by push_cast; ring
    rw [heZ, N₂_nat, N₂_nat]
    change (generatedHilbertFunction (pointDegreeSpace K a d) (d + e) : ℤ) = _
    rw [hspan, single_generator_hilbertFunction f hf]
    change ((N (d + e) - N e : ℕ) : ℤ) = _
    exact Nat.cast_sub hN

/-- All assertions of the one-generator case, without assuming an already
proved Hilbert formula or regularity for the point configuration. -/
theorem principal_chop_conclusion (a : PointCoordinates K p) (hd : 0 < d)
    (hdim : finrank K (pointDegreePiece K a d) = 1) :
    ∃ f : Forms K 3 d,
      f.val ≠ 0 ∧
      pointDegreeSpace K a d = Submodule.span K {f.val} ∧
      choppedIdeal K a d = Ideal.span {f.val} ∧
      RingTheory.Sequence.IsRegular (Poly K 3) [f.val] ∧
      ∀ t : ℕ, (choppedHilbertFunction a d t : ℤ) = N₂ t - N₂ ((t : ℤ) - d) := by
  obtain ⟨f, hf, hspan⟩ := exists_principal_pointDegreeSpace a hdim
  exact ⟨f, hf, hspan, choppedIdeal_eq_singleton_of_space_eq a f hspan,
    nonzero_form_regular_singleton f hf hd,
    principal_chop_hilbert_coefficients a f hf hspan⟩


/-- The regular-generator witness in the finite-family format of the main
statement. -/
theorem principal_chop_regular_generators (a : PointCoordinates K p) (hd : 0 < d)
    (hdim : finrank K (pointDegreePiece K a d) = 1) :
    ∃ f : Fin 1 → Forms K 3 d,
      Ideal.span (Set.range (fun i => (f i).val)) = choppedIdeal K a d ∧
      RingTheory.Sequence.IsRegular (Poly K 3) (List.ofFn (fun i => (f i).val)) := by
  obtain ⟨f, hf, hspan, hIdeal, hregular, hcoeff⟩ := principal_chop_conclusion a hd hdim
  refine ⟨fun _ => f, ?_, ?_⟩
  · simpa using hIdeal.symm
  · simpa using hregular

/-- Natural-valued version of every principal-chop Hilbert coefficient. -/
theorem principal_chop_hilbert_coefficients_nat (a : PointCoordinates K p)
    (f : Forms K 3 d) (hf : f.val ≠ 0)
    (hspan : pointDegreeSpace K a d = Submodule.span K {f.val}) (t : ℕ) :
    choppedHilbertFunction a d t = (N₂ t - N₂ ((t : ℤ) - d)).toNat := by
  simpa using congrArg Int.toNat (principal_chop_hilbert_coefficients a f hf hspan t)

end ChoppedPlane
