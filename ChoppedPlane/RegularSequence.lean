module

public import ChoppedPlane.Homogeneous
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.MvPolynomial.Basic

@[expose] public section

noncomputable section

namespace ChoppedPlane

open scoped Pointwise

/-- In a domain with divisor decomposition, a relatively prime pair is a
    regular sequence whenever its generated ideal is proper. -/
theorem regular_pair_of_relPrime {R : Type*} [CommRing R] [IsDomain R]
    [DecompositionMonoid R] (f g : R) (hf : f ≠ 0) (hcop : IsRelPrime f g)
    (hproper : Ideal.ofList [f,g] ≠ ⊤) :
    RingTheory.Sequence.IsRegular R [f,g] := by
  have hfirst : IsSMulRegular R f := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro x hx
    exact (mul_eq_zero.mp hx).resolve_left hf
  have hsecond : IsSMulRegular (QuotSMulTop f R) g := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem (f • (⊤ : Submodule R R)) g).mpr
    intro x hx
    rw [Submodule.mem_smul_pointwise_iff_exists] at hx ⊢
    obtain ⟨y,hy,hey⟩ := hx
    have hdiv : f ∣ g * x := ⟨y, by simpa only [smul_eq_mul] using hey.symm⟩
    obtain ⟨q,hq⟩ := hcop.dvd_of_dvd_mul_left hdiv
    exact ⟨q,Submodule.mem_top,by simpa only [smul_eq_mul] using hq.symm⟩
  refine ⟨?_,?_⟩
  · apply (RingTheory.Sequence.isWeaklyRegular_cons_iff R f [g]).mpr
    refine ⟨hfirst,?_⟩
    exact (RingTheory.Sequence.isWeaklyRegular_singleton_iff (QuotSMulTop f R) g).mpr hsecond
  · intro h
    apply hproper
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using h.symm

/-- Positive-degree homogeneous forms vanish at the affine origin. -/
theorem homogeneous_eval_origin_eq_zero {K : Type*} [Field K] {n d : ℕ}
    (hd : 0 < d) (f : Forms K n d) : MvPolynomial.eval (fun _ => 0) f.val = 0 := by
  have h := homogeneous_eval_scale f.property (fun _ => (0 : K)) 0
  simpa [zero_pow (Nat.ne_zero_of_lt hd)] using h

/-- Relatively prime positive-degree homogeneous forms form a regular sequence
    in the actual polynomial ring. -/
theorem homogeneous_regular_pair {K : Type*} [Field K] {n d : ℕ}
    (hd : 0 < d) (f g : Forms K n d) (hf : f.val ≠ 0)
    (hcop : IsRelPrime f.val g.val) :
    RingTheory.Sequence.IsRegular (Poly K n) [f.val,g.val] := by
  apply regular_pair_of_relPrime f.val g.val hf hcop
  intro htop
  have hle : Ideal.ofList [f.val,g.val] ≤ RingHom.ker (MvPolynomial.eval (fun _ => 0)) := by
    apply Ideal.span_le.mpr
    intro p hp
    simp at hp
    rcases hp with rfl | rfl
    · exact homogeneous_eval_origin_eq_zero hd f
    · exact homogeneous_eval_origin_eq_zero hd g
  have h1 := hle (htop ▸ (Submodule.mem_top : (1 : Poly K n) ∈ ⊤))
  exact one_ne_zero (by simpa only [RingHom.mem_ker, map_one] using h1)

end ChoppedPlane
