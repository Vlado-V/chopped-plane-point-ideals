module

public import ChoppedPlane.Homogeneous
public import Mathlib

@[expose] public section

/-! The affine chart obtained by setting the last plane coordinate to one. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial
variable {K : Type*} [Field K]

/-- Dehomogenization in the plane's last coordinate. -/
def affineDehom : Poly K 3 →ₐ[K] Poly K 2 :=
  MvPolynomial.aeval ![X 0, X 1, 1]

@[simp] theorem affineDehom_X_zero : affineDehom (X 0 : Poly K 3) = X 0 := by
  simp [affineDehom]

@[simp] theorem affineDehom_X_one : affineDehom (X 1 : Poly K 3) = X 1 := by
  simp [affineDehom]

@[simp] theorem affineDehom_X_two : affineDehom (X 2 : Poly K 3) = 1 := by
  simp [affineDehom]

alias affineDehom_X0 := affineDehom_X_zero
alias affineDehom_X1 := affineDehom_X_one
alias affineDehom_X2 := affineDehom_X_two

/-- Renaming the two affine variables into the first two plane variables is a
right inverse to dehomogenization. -/
theorem affineDehom_comp_rename :
    (affineDehom (K := K)).comp (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3)) =
      AlgHom.id K (Poly K 2) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [affineDehom]

@[simp] theorem affineDehom_rename (p : Poly K 2) :
    affineDehom (MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) p) = p :=
  AlgHom.congr_fun affineDehom_comp_rename p

theorem affineDehom_surjective : Function.Surjective (affineDehom (K := K)) :=
  fun p => ⟨MvPolynomial.rename (Fin.castSucc : Fin 2 → Fin 3) p, affineDehom_rename p⟩

/-- The dehomogenization kernel is the equation that the last coordinate is one. -/
theorem affineDehom_ker : RingHom.ker (affineDehom (K := K)).toRingHom =
    Ideal.span {(X 2 : Poly K 3) - 1} := by
  classical
  let J : Ideal (Poly K 3) := Ideal.span {(X 2 : Poly K 3) - 1}
  let q : Poly K 3 →ₐ[K] (Poly K 3 ⧸ J) := Ideal.Quotient.mkₐ K J
  let φ : Poly K 2 →ₐ[K] (Poly K 3 ⧸ J) :=
    MvPolynomial.aeval ![q (X 0), q (X 1)]
  have hqz : q (X 2) = 1 := by
    have hzmem : (X 2 : Poly K 3) - 1 ∈ J :=
      Ideal.subset_span (Set.mem_singleton _)
    have hz : q ((X 2 : Poly K 3) - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hzmem
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  have hfactor : φ.comp (affineDehom (K := K)) = q := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [φ, hqz]
  have hle : J ≤ RingHom.ker (affineDehom (K := K)).toRingHom := by
    apply Ideal.span_le.mpr
    rintro p (rfl : p = (X 2 : Poly K 3) - 1)
    change affineDehom ((X 2 : Poly K 3) - 1) = 0
    simp
  apply le_antisymm
  · intro p hp
    change p ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hp0 : affineDehom p = 0 := hp
    have h := AlgHom.congr_fun hfactor p
    simpa only [AlgHom.comp_apply, hp0, map_zero, q, Ideal.Quotient.mkₐ_eq_mk] using h.symm
  · exact hle

/-- Equality after dehomogenization is divisibility by the chart equation. -/
theorem affineDehom_eq_iff (f g : Poly K 3) :
    affineDehom f = affineDehom g ↔ (X 2 - 1 : Poly K 3) ∣ f - g := by
  rw [← sub_eq_zero, ← map_sub]
  change f - g ∈ RingHom.ker (affineDehom (K := K)).toRingHom ↔ _
  rw [affineDehom_ker, Ideal.mem_span_singleton]

end ChoppedPlane
