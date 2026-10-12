module

public import ChoppedPlane.LaurentChartComplex
public import ChoppedPlane.FiniteCechDuality

@[expose] public section

/-!
# Cross descent on the actual graded Laurent quotient

The spaces here are the genuine supported Laurent spaces, and the final map
is the actual negative-exponent projection of an overlap multiplier.  The
proof is a coefficient diagram chase: the two cross images agree, hence give
a polynomial directional kernel; its vanishing gives local linear-form
preimages, and overlap injectivity makes those preimages agree.
-/

noncomputable section
namespace ChoppedPlane.ConcreteCech

open LaurentPairing LaurentChartComplex

variable {K : Type*} [Field K]
variable {ι κ η N : Type*} [AddCommGroup N] [Module K N]

/-- The actual overlap operator restricted to its two homogeneous components. -/
def overlapMap (g : ι → ℤ) (h : κ → ℤ) (a b : ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hL : ∀ p ∈ overlapGrade g a, L p ∈ overlapGrade h b) :
    overlapGrade (K := K) g a →ₗ[K] overlapGrade (K := K) h b :=
  (L.comp (overlapGrade (K := K) g a).subtype).codRestrict _
    (fun p => hL p.val p.property)

/-- Multiplication on top Laurent representatives, with negative-exponent projection. -/
def topMap (g : ι → ℤ) (h : κ → ℤ) (a b : ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hL : ∀ p ∈ overlapGrade g a, L p ∈ overlapGrade h b) :
    topGrade (K := K) g a →ₗ[K] topGrade (K := K) h b :=
  (topProjection h b).comp ((overlapMap g h a b L hL).comp
    (Submodule.inclusion (topGrade_le_overlapGrade g a)))

@[simp] theorem overlapMap_val (g : ι → ℤ) (h : κ → ℤ) (a b : ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hL : ∀ p ∈ overlapGrade g a, L p ∈ overlapGrade h b)
    (p : overlapGrade (K := K) g a) : (overlapMap g h a b L hL p).val = L p.val := rfl

/-- The actual top operator is literal negative-exponent projection after multiplication. -/
theorem topMap_val (g : ι → ℤ) (h : κ → ℤ) (a b : ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hL : ∀ p ∈ overlapGrade g a, L p ∈ overlapGrade h b)
    (p : topGrade (K := K) g a) :
    (topMap g h a b L hL p).val = freeNegativePart (L p.val) := by
  classical
  ext e
  change (topProjection h b
    (overlapMap g h a b L hL
      (Submodule.inclusion (topGrade_le_overlapGrade g a) p))).val e = _
  rw [topProjection_coeff, overlapMap_val]
  rcases e with ⟨i,e⟩
  rw [freeNegativePart_apply]
  by_cases hg : (i,e) ∈ gradeIndices h b
  · simp only [topIndices, Set.mem_ofPred_eq, hg, true_and]
    rfl
  · have hz : L p.val (i,e) = 0 :=
      (Finsupp.mem_supported' K _).mp
        (hL p.val (topGrade_le_overlapGrade g a p.property)) (i,e) hg
    simp [topIndices, hg, hz]

/-- A top representative is unchanged by projecting it to the top quotient. -/
theorem topProjection_inclusion (g : ι → ℤ) (a : ℤ) (p : topGrade (K := K) g a) :
    topProjection g a (Submodule.inclusion (topGrade_le_overlapGrade g a) p) = p := by
  apply Subtype.ext
  ext e
  rw [topProjection_coeff]
  by_cases he : e ∈ topIndices g a
  · simp [he]
  · simp [he, (Finsupp.mem_supported' K _).mp p.property e he]

/-- The coefficient-level cross chase on the genuine chart supports. -/
theorem overlap_preimage_of_cross
    (g : ι → ℤ) (h : κ → ℤ) (j : η → ℤ) (a b c : ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (Q : FreeLaurent K κ →ₗ[K] FreeLaurent K η)
    (D : FreeLaurent K η →ₗ[K] N)
    (hQU : ∀ p ∈ uChartGrade h b, Q p ∈ uChartGrade j c)
    (hQV : ∀ p ∈ vChartGrade h b, Q p ∈ vChartGrade j c)
    (hQL : ∀ p, Q (L p) = 0)
    (hDQ : ∀ p, D (Q p) = 0)
    (hLinj : ∀ p ∈ overlapGrade g a, L p = 0 → p = 0)
    (hglobal : ∀ p ∈ positiveGrade j c, D p = 0 → p = 0)
    (hlocalU : ∀ p ∈ uChartGrade h b, Q p = 0 →
      ∃ x ∈ uChartGrade g a, L x = p)
    (hlocalV : ∀ p ∈ vChartGrade h b, Q p = 0 →
      ∃ x ∈ vChartGrade g a, L x = p)
    (p : FreeLaurent K ι) (hp : p ∈ overlapGrade g a)
    (hLp : L p ∈ uChartGrade h b ⊔ vChartGrade h b) :
    p ∈ uChartGrade g a ⊔ vChartGrade g a := by
  obtain ⟨u,hu,v,hv,huv⟩ := Submodule.mem_sup.mp hLp
  have hsum : Q u + Q v = 0 := by
    rw [← map_add, huv]
    exact hQL p
  have hQuPoly : Q u ∈ positiveGrade j c := by
    rw [← chart_intersection]
    refine ⟨hQU u hu, ?_⟩
    have heq : Q u = -(Q v) := eq_neg_of_add_eq_zero_left hsum
    rw [heq]
    exact (vChartGrade (K := K) j c).neg_mem (hQV v hv)
  have hQu : Q u = 0 := hglobal (Q u) hQuPoly (hDQ u)
  have hQv : Q v = 0 := by simpa [hQu] using hsum
  obtain ⟨x,hx,hxL⟩ := hlocalU u hu hQu
  obtain ⟨y,hy,hyL⟩ := hlocalV v hv hQv
  have hzgrade : p - (x + y) ∈ overlapGrade g a :=
    (overlapGrade (K := K) g a).sub_mem hp
      ((overlapGrade (K := K) g a).add_mem
        (uChartGrade_le_overlapGrade g a hx) (vChartGrade_le_overlapGrade g a hy))
  have hzL : L (p - (x + y)) = 0 := by
    rw [map_sub, map_add, hxL, hyL, huv, sub_self]
  have hz := hLinj _ hzgrade hzL
  have heq : p = x + y := sub_eq_zero.mp hz
  rw [heq]
  exact Submodule.add_mem_sup hx hy

/-- If the global directional kernel vanishes, multiplication on the actual
finite top Laurent quotient is injective. -/
theorem topMap_injective_of_cross
    (g : ι → ℤ) (h : κ → ℤ) (j : η → ℤ) (a b c : ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (Q : FreeLaurent K κ →ₗ[K] FreeLaurent K η)
    (D : FreeLaurent K η →ₗ[K] N)
    (hL : ∀ p ∈ overlapGrade g a, L p ∈ overlapGrade h b)
    (hQU : ∀ p ∈ uChartGrade h b, Q p ∈ uChartGrade j c)
    (hQV : ∀ p ∈ vChartGrade h b, Q p ∈ vChartGrade j c)
    (hQL : ∀ p, Q (L p) = 0)
    (hDQ : ∀ p, D (Q p) = 0)
    (hLinj : ∀ p ∈ overlapGrade g a, L p = 0 → p = 0)
    (hglobal : ∀ p ∈ positiveGrade j c, D p = 0 → p = 0)
    (hlocalU : ∀ p ∈ uChartGrade h b, Q p = 0 →
      ∃ x ∈ uChartGrade g a, L x = p)
    (hlocalV : ∀ p ∈ vChartGrade h b, Q p = 0 →
      ∃ x ∈ vChartGrade g a, L x = p) :
    Function.Injective (topMap g h a b L hL) := by
  have hz : ∀ p : topGrade (K := K) g a, topMap g h a b L hL p = 0 → p = 0 := by
    intro p hp
    have hLp : L p.val ∈ uChartGrade h b ⊔ vChartGrade h b := by
      exact (topProjection_eq_zero_iff h b
        (overlapMap g h a b L hL
          (Submodule.inclusion (topGrade_le_overlapGrade g a) p))).mp hp
    have hpSum := overlap_preimage_of_cross g h j a b c L Q D
      hQU hQV hQL hDQ hLinj hglobal hlocalU hlocalV
      p.val (topGrade_le_overlapGrade g a p.property) hLp
    have hpTop : topProjection g a
        (Submodule.inclusion (topGrade_le_overlapGrade g a) p) = 0 :=
      (topProjection_eq_zero_iff g a _).mpr hpSum
    rw [topProjection_inclusion] at hpTop
    exact hpTop
  intro p q hpq
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hpq, sub_self]

end ChoppedPlane.ConcreteCech
