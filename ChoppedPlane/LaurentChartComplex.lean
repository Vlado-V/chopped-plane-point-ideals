module

public import ChoppedPlane.LaurentPairing
public import ChoppedPlane.BinaryChartRings

@[expose] public section

/-!
# The actual graded two-chart Laurent complex

All spaces are supported subspaces of the free binary Laurent module.  The
kernel of the chart difference is exactly the diagonal polynomial part.  In
a degree below every free generator this polynomial part vanishes, so the
chart difference is injective.
-/

noncomputable section
set_option maxHeartbeats 300000
attribute [local instance] Classical.propDecidable
namespace ChoppedPlane.LaurentChartComplex

open LaurentPairing Module
variable {K : Type*} [Field K] {ι : Type*}

/-- Laurent monomials of a fixed total degree, with free-generator shifts. -/
def gradeIndices (g : ι → ℤ) (k : ℤ) : Set (ι × (ℤ × ℤ)) :=
  {e | e.2.1 + e.2.2 + g e.1 = k}

/-- The `u` chart has no negative powers of `v`. -/
def uChartIndices (g : ι → ℤ) (k : ℤ) : Set (ι × (ℤ × ℤ)) :=
  {e | e ∈ gradeIndices g k ∧ 0 ≤ e.2.2}

/-- The `v` chart has no negative powers of `u`. -/
def vChartIndices (g : ι → ℤ) (k : ℤ) : Set (ι × (ℤ × ℤ)) :=
  {e | e ∈ gradeIndices g k ∧ 0 ≤ e.2.1}

/-- The degree-`k` overlap, allowing both exponents to be integral. -/
def overlapGrade (g : ι → ℤ) (k : ℤ) : Submodule K (FreeLaurent K ι) :=
  Finsupp.supported K K (gradeIndices g k)

def uChartGrade (g : ι → ℤ) (k : ℤ) : Submodule K (FreeLaurent K ι) :=
  Finsupp.supported K K (uChartIndices g k)

def vChartGrade (g : ι → ℤ) (k : ℤ) : Submodule K (FreeLaurent K ι) :=
  Finsupp.supported K K (vChartIndices g k)

theorem uChartGrade_le_overlapGrade (g : ι → ℤ) (k : ℤ) :
    uChartGrade (K := K) g k ≤ overlapGrade (K := K) g k :=
  Finsupp.supported_mono fun _ h => h.1

theorem vChartGrade_le_overlapGrade (g : ι → ℤ) (k : ℤ) :
    vChartGrade (K := K) g k ≤ overlapGrade (K := K) g k :=
  Finsupp.supported_mono fun _ h => h.1

/-- The two genuine affine charts intersect in binary polynomials. -/
theorem chart_intersection (g : ι → ℤ) (k : ℤ) :
    uChartGrade (K := K) g k ⊓ vChartGrade (K := K) g k = positiveGrade (K := K) g k := by
  rw [uChartGrade, vChartGrade, ← Finsupp.supported_inter, positiveGrade]
  congr 1
  ext e
  simp only [Set.mem_inter_iff, uChartIndices, vChartIndices, gradeIndices,
    positiveIndices, Set.mem_ofPred_eq]
  tauto

theorem positiveGrade_le_uChartGrade (g : ι → ℤ) (k : ℤ) :
    positiveGrade (K := K) g k ≤ uChartGrade (K := K) g k := by
  rw [← chart_intersection]
  exact inf_le_left

theorem positiveGrade_le_vChartGrade (g : ι → ℤ) (k : ℤ) :
    positiveGrade (K := K) g k ≤ vChartGrade (K := K) g k := by
  rw [← chart_intersection]
  exact inf_le_right

/-- The actual difference map of the two affine-chart restrictions. -/
def chartDifference (g : ι → ℤ) (k : ℤ) :
    (uChartGrade (K := K) g k × vChartGrade (K := K) g k) →ₗ[K]
      overlapGrade (K := K) g k where
  toFun p := ⟨p.1.val - p.2.val,
    (overlapGrade (K := K) g k).sub_mem
      (uChartGrade_le_overlapGrade (K := K) g k p.1.property)
      (vChartGrade_le_overlapGrade (K := K) g k p.2.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change (p.1.val + q.1.val) - (p.2.val + q.2.val) =
      (p.1.val - p.2.val) + (q.1.val - q.2.val)
    abel
  map_smul' c p := by
    apply Subtype.ext
    change c • p.1.val - c • p.2.val = c • (p.1.val - p.2.val)
    exact (smul_sub c p.1.val p.2.val).symm

@[simp] theorem chartDifference_val (g : ι → ℤ) (k : ℤ)
    (p : uChartGrade (K := K) g k × vChartGrade (K := K) g k) :
    (chartDifference (K := K) g k p).val = p.1.val - p.2.val := rfl

/-- Restricting a polynomial to both charts is the diagonal map. -/
def chartDiagonal (g : ι → ℤ) (k : ℤ) :
    positiveGrade (K := K) g k →ₗ[K] (uChartGrade (K := K) g k × vChartGrade (K := K) g k) :=
  (Submodule.inclusion (positiveGrade_le_uChartGrade (K := K) g k)).prod
    (Submodule.inclusion (positiveGrade_le_vChartGrade (K := K) g k))

@[simp] theorem chartDiagonal_val_fst (g : ι → ℤ) (k : ℤ)
    (p : positiveGrade (K := K) g k) : (chartDiagonal (K := K) g k p).1.val = p.val := rfl

@[simp] theorem chartDiagonal_val_snd (g : ι → ℤ) (k : ℤ)
    (p : positiveGrade (K := K) g k) : (chartDiagonal (K := K) g k p).2.val = p.val := rfl

@[simp] theorem chartDifference_diagonal (g : ι → ℤ) (k : ℤ)
    (p : positiveGrade (K := K) g k) : chartDifference (K := K) g k (chartDiagonal (K := K) g k p) = 0 := by
  apply Subtype.ext
  simp

theorem chartDifference_eq_zero_iff (g : ι → ℤ) (k : ℤ)
    (p : uChartGrade (K := K) g k × vChartGrade (K := K) g k) :
    chartDifference (K := K) g k p = 0 ↔ p.1.val = p.2.val := by
  rw [← Subtype.val_inj]
  change p.1.val - p.2.val = 0 ↔ _
  exact sub_eq_zero

/-- Exactness at the actual pair of graded chart spaces. -/
theorem ker_chartDifference (g : ι → ℤ) (k : ℤ) :
    LinearMap.ker (chartDifference (K := K) g k) = LinearMap.range (chartDiagonal (K := K) g k) := by
  ext p
  rw [LinearMap.mem_ker, chartDifference_eq_zero_iff]
  constructor
  · intro hp
    have hm : p.1.val ∈ positiveGrade (K := K) g k := by
      rw [← chart_intersection]
      exact ⟨p.1.property, hp.symm ▸ p.2.property⟩
    refine ⟨⟨p.1.val, hm⟩, ?_⟩
    apply Prod.ext <;> apply Subtype.ext
    · rfl
    · exact hp
  · rintro ⟨q, rfl⟩
    rfl

/-- A polynomial component below all generator degrees is zero. -/
theorem positiveGrade_eq_bot_of_lt (g : ι → ℤ) (k : ℤ) (hk : ∀ i, k < g i) :
    positiveGrade (K := K) g k = ⊥ := by
  have hs : positiveIndices g k = ∅ := by
    ext e
    simp only [positiveIndices, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    have hi := hk e.1
    omega
  rw [positiveGrade, hs, Finsupp.supported_empty]

/-- There are no nonzero polynomial sections in a degree below every generator. -/
theorem positiveGrade_zero_of_lt (g : ι → ℤ) (k : ℤ) (hk : ∀ i, k < g i)
    (p : positiveGrade (K := K) g k) : p = 0 := by
  apply Subtype.ext
  have heq := positiveGrade_eq_bot_of_lt (K := K) g k hk
  have hp : (p.val : FreeLaurent K ι) ∈ (⊥ : Submodule K (FreeLaurent K ι)) :=
    heq ▸ p.property
  exact (Submodule.mem_bot K).mp hp

/-- Injectivity of the genuine chart difference in the negative range. -/
theorem chartDifference_injective_of_lt (g : ι → ℤ) (k : ℤ) (hk : ∀ i, k < g i) :
    Function.Injective (chartDifference (K := K) g k) := by
  intro p q hpq
  have h : p.1.val - p.2.val = q.1.val - q.2.val :=
    congrArg Subtype.val hpq
  have heq : p.1.val - q.1.val = p.2.val - q.2.val := by
    calc
      p.1.val - q.1.val =
          (p.1.val - p.2.val) - (q.1.val - q.2.val) + (p.2.val - q.2.val) := by abel
      _ = p.2.val - q.2.val := by rw [h, sub_self, zero_add]
  have hm : p.1.val - q.1.val ∈ positiveGrade (K := K) g k := by
    rw [← chart_intersection]
    exact ⟨(uChartGrade (K := K) g k).sub_mem p.1.property q.1.property,
      heq.symm ▸ (vChartGrade (K := K) g k).sub_mem p.2.property q.2.property⟩
  have hz : p.1.val - q.1.val = 0 := by
    have hb : p.1.val - q.1.val ∈ (⊥ : Submodule K (FreeLaurent K ι)) :=
      positiveGrade_eq_bot_of_lt (K := K) g k hk ▸ hm
    exact (Submodule.mem_bot K).mp hb
  apply Prod.ext <;> apply Subtype.ext
  · exact sub_eq_zero.mp hz
  · exact sub_eq_zero.mp (heq.symm.trans hz)

/-- The chart sum consists of the degree-`k` monomials with at least one
nonnegative exponent. -/
theorem chart_sum_eq_supported (g : ι → ℤ) (k : ℤ) :
    uChartGrade (K := K) g k ⊔ vChartGrade (K := K) g k =
      Finsupp.supported K K
        {e | e ∈ gradeIndices g k ∧ (0 ≤ e.2.2 ∨ 0 ≤ e.2.1)} := by
  rw [uChartGrade, vChartGrade, ← Finsupp.supported_union]
  congr 1
  ext e
  simp only [Set.mem_union, uChartIndices, vChartIndices, Set.mem_ofPred_eq]
  tauto

/-- The image of the actual chart difference is the actual sum of chart spaces. -/
theorem chartDifference_mem_range_iff (g : ι → ℤ) (k : ℤ)
    (p : overlapGrade (K := K) g k) :
    p ∈ LinearMap.range (chartDifference (K := K) g k) ↔
      p.val ∈ uChartGrade (K := K) g k ⊔ vChartGrade (K := K) g k := by
  constructor
  · rintro ⟨q, rfl⟩
    rw [chartDifference_val]
    simpa only [sub_eq_add_neg] using
      Submodule.add_mem_sup q.1.property ((vChartGrade (K := K) g k).neg_mem q.2.property)
  · intro hp
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hp
    refine ⟨(⟨u, hu⟩, ⟨-v, (vChartGrade (K := K) g k).neg_mem hv⟩), ?_⟩
    apply Subtype.ext
    simpa using huv

/-- Strictly negative monomials of the same generator-shifted degree. -/
def topIndices (g : ι → ℤ) (k : ℤ) : Set (ι × (ℤ × ℤ)) :=
  {e | e ∈ gradeIndices g k ∧ e.2.1 < 0 ∧ e.2.2 < 0}

/-- The genuine finite-degree top Laurent quotient representatives. -/
def topGrade (g : ι → ℤ) (k : ℤ) : Submodule K (FreeLaurent K ι) :=
  Finsupp.supported K K (topIndices g k)

theorem topGrade_le_overlapGrade (g : ι → ℤ) (k : ℤ) :
    topGrade (K := K) g k ≤ overlapGrade (K := K) g k :=
  Finsupp.supported_mono fun _ h => h.1

/-- Projection of a graded Laurent section to its actual top quotient. -/
def topProjection (g : ι → ℤ) (k : ℤ) :
    overlapGrade (K := K) g k →ₗ[K] topGrade (K := K) g k := by
  classical
  exact (Finsupp.restrictDom K K (topIndices g k)).comp (overlapGrade (K := K) g k).subtype

@[simp] theorem topProjection_coeff (g : ι → ℤ) (k : ℤ)
    (p : overlapGrade (K := K) g k) (e : ι × (ℤ × ℤ)) :
    (topProjection (K := K) g k p).val e = if e ∈ topIndices g k then p.val e else 0 := by
  classical
  change (p.val.filter (· ∈ topIndices g k)) e = _
  simp [Finsupp.filter]

theorem topProjection_surjective (g : ι → ℤ) (k : ℤ) :
    Function.Surjective (topProjection (K := K) g k) := by
  intro p
  refine ⟨⟨p.val, topGrade_le_overlapGrade (K := K) g k p.property⟩, ?_⟩
  apply Subtype.ext
  ext e
  by_cases he : e ∈ topIndices g k
  · simp [he]
  · simp [he, (Finsupp.mem_supported' K _).mp p.property e he]

/-- Projection vanishes exactly on the sum of the actual affine-chart spaces. -/
theorem topProjection_eq_zero_iff (g : ι → ℤ) (k : ℤ)
    (p : overlapGrade (K := K) g k) :
    topProjection (K := K) g k p = 0 ↔ p.val ∈ uChartGrade (K := K) g k ⊔ vChartGrade (K := K) g k := by
  rw [chart_sum_eq_supported, Finsupp.mem_supported']
  constructor
  · intro hp e he
    by_cases hg : e ∈ gradeIndices g k
    · have hn : e ∈ topIndices g k := by
        change e ∈ gradeIndices g k ∧ e.2.1 < 0 ∧ e.2.2 < 0
        change ¬(e ∈ gradeIndices g k ∧ (0 ≤ e.2.2 ∨ 0 ≤ e.2.1)) at he
        have hnn : ¬(0 ≤ e.2.2 ∨ 0 ≤ e.2.1) := fun hn => he ⟨hg, hn⟩
        exact ⟨hg, by omega⟩
      have hz := congrArg (fun z : topGrade (K := K) g k => z.val e) hp
      simpa [hn] using hz
    · exact (Finsupp.mem_supported' K _).mp p.property e hg
  · intro hp
    apply Subtype.ext
    ext e
    by_cases he : e ∈ topIndices g k
    · have hn : e ∉ {e | e ∈ gradeIndices g k ∧ (0 ≤ e.2.2 ∨ 0 ≤ e.2.1)} := by
        obtain ⟨_, ha, hb⟩ := he
        change ¬(_ ∧ (0 ≤ e.2.2 ∨ 0 ≤ e.2.1))
        omega
      simp [he, hp e hn]
    · simp [he]

/-- Exactness of the genuine graded two-chart complex at the overlap. -/
theorem ker_topProjection (g : ι → ℤ) (k : ℤ) :
    LinearMap.ker (topProjection (K := K) g k) = LinearMap.range (chartDifference (K := K) g k) := by
  ext p
  rw [LinearMap.mem_ker, topProjection_eq_zero_iff, chartDifference_mem_range_iff]

/-- Compatibility with the shifted dual grade used by the residue pairing. -/
theorem topGrade_eq_negativeGrade (g : ι → ℤ) (k : ℤ) :
    topGrade (K := K) g k = negativeGrade (fun i => 2 - g i) (-k) := by
  rw [topGrade, negativeGrade]
  congr 1
  ext e
  simp only [topIndices, gradeIndices, negativeIndices, Set.mem_ofPred_eq]
  omega

/-- In the `2-g` shifted chart module, the actual quotient has exactly the
negative grade paired with degree-`r` polynomials. -/
theorem topGrade_dual_shift_eq (g : ι → ℤ) (r : ℤ) :
    topGrade (K := K) (fun i => 2 - g i) (-r) = negativeGrade (K := K) g r := by
  rw [topGrade, negativeGrade]
  congr 1
  ext e
  simp only [topIndices, gradeIndices, negativeIndices, Set.mem_ofPred_eq]
  omega

/-- Actual top representatives in the residue-compatible dual shifts. -/
def topGradeNegativeEquiv (g : ι → ℤ) (r : ℤ) :
    topGrade (K := K) (fun i => 2 - g i) (-r) ≃ₗ[K] negativeGrade (K := K) g r :=
  LinearEquiv.ofEq _ _ (topGrade_dual_shift_eq (K := K) g r)

/-- The actual top quotient representatives are perfectly dual to polynomials. -/
def topGradeResidueDualEquiv [Finite ι] (g : ι → ℤ) (r : ℤ) :
    topGrade (K := K) (fun i => 2 - g i) (-r) ≃ₗ[K]
      Module.Dual K (positiveGrade (K := K) g r) :=
  (topGradeNegativeEquiv (K := K) g r).trans (residueDualEquiv g r)

/-- Projection of all free Laurent coefficients to one generator-shifted degree. -/
def gradeProjection (g : ι → ℤ) (k : ℤ) : FreeLaurent K ι →ₗ[K] FreeLaurent K ι :=
  (overlapGrade (K := K) g k).subtype.comp
    (Finsupp.restrictDom K K (gradeIndices g k))

@[simp] theorem gradeProjection_coeff (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι) (e : ι × (ℤ × ℤ)) :
    gradeProjection g k p e = if e ∈ gradeIndices g k then p e else 0 := by
  change (p.filter (· ∈ gradeIndices g k)) e = _
  simp [Finsupp.filter]

theorem gradeProjection_mem_overlapGrade (g : ι → ℤ) (k : ℤ) (p : FreeLaurent K ι) :
    gradeProjection g k p ∈ overlapGrade (K := K) g k :=
  (Finsupp.restrictDom K K (gradeIndices g k) p).property

/-- Fixed points of the coefficient projection are exactly the actual graded space. -/
theorem mem_overlapGrade_iff_gradeProjection_eq (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι) :
    p ∈ overlapGrade (K := K) g k ↔ gradeProjection g k p = p := by
  constructor
  · intro hp
    ext e
    by_cases he : e ∈ gradeIndices g k
    · simp [he]
    · simp [he, (Finsupp.mem_supported' K p).mp hp e he]
  · intro hp
    rw [← hp]
    exact gradeProjection_mem_overlapGrade g k p

@[simp] theorem gradeProjection_single (g : ι → ℤ) (k : ℤ)
    (e : ι × (ℤ × ℤ)) (c : K) :
    gradeProjection g k (Finsupp.single e c) =
      if e ∈ gradeIndices g k then Finsupp.single e c else 0 := by
  change (Finsupp.single e c).filter (· ∈ gradeIndices g k) = _
  by_cases he : e ∈ gradeIndices g k
  · rw [Finsupp.filter_single_of_pos (· ∈ gradeIndices g k) he, ite_eq_left he]
  · rw [Finsupp.filter_single_of_neg (· ∈ gradeIndices g k) he, ite_eq_right he]

/-- A pure component has zero projection to any different degree. -/
theorem gradeProjection_zero_of_ne (g : ι → ℤ) {j k : ℤ} (hjk : j ≠ k)
    (p : FreeLaurent K ι) (hp : p ∈ overlapGrade (K := K) g j) :
    gradeProjection g k p = 0 := by
  ext e
  by_cases he : e ∈ gradeIndices g k
  · have hj : e ∉ gradeIndices g j := by
      intro hj
      exact hjk (hj.symm.trans he)
    simp [he, (Finsupp.mem_supported' K p).mp hp e hj]
  · simp [he]

/-- Coefficient projection preserves the actual `u` chart support. -/
theorem gradeProjection_preserves_uChartSupport (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι)
    (hp : p ∈ Finsupp.supported K K {e : ι × (ℤ × ℤ) | 0 ≤ e.2.2}) :
    gradeProjection g k p ∈ uChartGrade (K := K) g k := by
  apply (Finsupp.mem_supported' K _).mpr
  intro e he
  by_cases hg : e ∈ gradeIndices g k
  · have hu : ¬0 ≤ e.2.2 := by
      intro hu
      exact he ⟨hg, hu⟩
    simp [hg, (Finsupp.mem_supported' K p).mp hp e hu]
  · simp [hg]

/-- Coefficient projection preserves the actual `v` chart support. -/
theorem gradeProjection_preserves_vChartSupport (g : ι → ℤ) (k : ℤ)
    (p : FreeLaurent K ι)
    (hp : p ∈ Finsupp.supported K K {e : ι × (ℤ × ℤ) | 0 ≤ e.2.1}) :
    gradeProjection g k p ∈ vChartGrade (K := K) g k := by
  apply (Finsupp.mem_supported' K _).mpr
  intro e he
  by_cases hg : e ∈ gradeIndices g k
  · have hv : ¬0 ≤ e.2.1 := by
      intro hv
      exact he ⟨hg, hv⟩
    simp [hg, (Finsupp.mem_supported' K p).mp hp e hv]
  · simp [hg]

/-- Any actual operator of a fixed degree shift commutes with graded projection.
The hypothesis only states closure of concrete supported subspaces; the proof
expands the finitely supported input into its actual Laurent monomials. -/
theorem gradeProjection_commutes_of_degree_shift {κ : Type*}
    (g : ι → ℤ) (h : κ → ℤ) (d : ℤ)
    (T : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hT : ∀ j : ℤ, ∀ p : FreeLaurent K ι,
      p ∈ overlapGrade (K := K) g j → T p ∈ overlapGrade (K := K) h (j + d))
    (k : ℤ) :
    (gradeProjection h (k + d)).comp T = T.comp (gradeProjection g k) := by
  apply LinearMap.ext
  intro p
  change gradeProjection h (k + d) (T p) = T (gradeProjection g k p)
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single e c =>
      have hm : Finsupp.single e c ∈ overlapGrade (K := K) g
          (e.2.1 + e.2.2 + g e.1) :=
        Finsupp.single_mem_supported K c rfl
      have ht := hT _ _ hm
      by_cases he : e ∈ gradeIndices g k
      · have heq : e.2.1 + e.2.2 + g e.1 = k := he
        rw [heq] at ht
        rw [gradeProjection_single, ite_eq_left he]
        exact (mem_overlapGrade_iff_gradeProjection_eq h (k + d) _).mp ht
      · have hne : e.2.1 + e.2.2 + g e.1 + d ≠ k + d := by
          intro hh
          apply he
          change e.2.1 + e.2.2 + g e.1 = k
          omega
        rw [gradeProjection_zero_of_ne h hne _ ht, gradeProjection_single, ite_eq_right he, map_zero]

section ActualChartModules

open BinaryChartRings
variable [Finite ι]

/-- Embed a genuine free module over the `u` chart into Laurent coefficients. -/
def uFreeEmbedding : (ι → URing K) →ₗ[K] FreeLaurent K ι :=
  (freeLaurentEquiv (K := K) (ι := ι)).symm.toLinearMap.comp
    ((uEmbedding (K := K)).toLinearMap.compLeft ι)

/-- Embed a genuine free module over the `v` chart into Laurent coefficients. -/
def vFreeEmbedding : (ι → VRing K) →ₗ[K] FreeLaurent K ι :=
  (freeLaurentEquiv (K := K) (ι := ι)).symm.toLinearMap.comp
    ((vEmbedding (K := K)).toLinearMap.compLeft ι)

@[simp] theorem freeLaurentEquiv_uFreeEmbedding (p : ι → URing K) (i : ι) :
    freeLaurentEquiv (uFreeEmbedding p) i = uEmbedding (p i) := by
  simp [uFreeEmbedding]

@[simp] theorem freeLaurentEquiv_vFreeEmbedding (p : ι → VRing K) (i : ι) :
    freeLaurentEquiv (vFreeEmbedding p) i = vEmbedding (p i) := by
  simp [vFreeEmbedding]

theorem uFreeEmbedding_injective : Function.Injective (uFreeEmbedding (K := K) (ι := ι)) := by
  intro p q hpq
  funext i
  apply uEmbedding_injective
  have hi := congrArg (fun f => freeLaurentEquiv f i) hpq
  simpa using hi

theorem vFreeEmbedding_injective : Function.Injective (vFreeEmbedding (K := K) (ι := ι)) := by
  intro p q hpq
  funext i
  apply vEmbedding_injective
  have hi := congrArg (fun f => freeLaurentEquiv f i) hpq
  simpa using hi

/-- Actual free chart modules have exactly the expected Laurent support. -/
theorem range_uFreeEmbedding :
    LinearMap.range (uFreeEmbedding (K := K) (ι := ι)) =
      Finsupp.supported K K {e : ι × (ℤ × ℤ) | 0 ≤ e.2.2} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply (Finsupp.mem_supported' K _).mpr
    intro e he
    have hi : uEmbedding (q e.1) ∈ chartU := by
      rw [← range_uEmbedding]
      exact ⟨q e.1, rfl⟩
    have hz := AddMonoidAlgebra.mem_supported'.mp hi e.2 he
    have hc := freeLaurentEquiv_coeff (uFreeEmbedding q) e.1 e.2
    rw [freeLaurentEquiv_uFreeEmbedding] at hc
    exact hc.symm.trans hz
  · intro hp
    have hi : ∀ i, freeLaurentEquiv p i ∈ chartU := by
      intro i
      apply AddMonoidAlgebra.mem_supported'.mpr
      intro e he
      rw [freeLaurentEquiv_coeff]
      exact (Finsupp.mem_supported' K _).mp hp (i, e) he
    have hr : ∀ i, ∃ q : URing K, uEmbedding q = freeLaurentEquiv p i := by
      intro i
      obtain ⟨q, hq⟩ := (show freeLaurentEquiv p i ∈ LinearMap.range (uEmbedding (K := K)).toLinearMap from ((range_uEmbedding (K := K)).symm ▸ hi i))
      exact ⟨q, hq⟩
    choose q hq using hr
    refine ⟨q, ?_⟩
    apply freeLaurentEquiv.injective
    funext i
    simpa using hq i

/-- Actual free chart modules have exactly the expected Laurent support. -/
theorem range_vFreeEmbedding :
    LinearMap.range (vFreeEmbedding (K := K) (ι := ι)) =
      Finsupp.supported K K {e : ι × (ℤ × ℤ) | 0 ≤ e.2.1} := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩
    apply (Finsupp.mem_supported' K _).mpr
    intro e he
    have hi : vEmbedding (q e.1) ∈ chartV := by
      rw [← range_vEmbedding]
      exact ⟨q e.1, rfl⟩
    have hz := AddMonoidAlgebra.mem_supported'.mp hi e.2 he
    have hc := freeLaurentEquiv_coeff (vFreeEmbedding q) e.1 e.2
    rw [freeLaurentEquiv_vFreeEmbedding] at hc
    exact hc.symm.trans hz
  · intro hp
    have hi : ∀ i, freeLaurentEquiv p i ∈ chartV := by
      intro i
      apply AddMonoidAlgebra.mem_supported'.mpr
      intro e he
      rw [freeLaurentEquiv_coeff]
      exact (Finsupp.mem_supported' K _).mp hp (i, e) he
    have hr : ∀ i, ∃ q : VRing K, vEmbedding q = freeLaurentEquiv p i := by
      intro i
      obtain ⟨q, hq⟩ := (show freeLaurentEquiv p i ∈ LinearMap.range (vEmbedding (K := K)).toLinearMap from ((range_vEmbedding (K := K)).symm ▸ hi i))
      exact ⟨q, hq⟩
    choose q hq using hr
    refine ⟨q, ?_⟩
    apply freeLaurentEquiv.injective
    funext i
    simpa using hq i

/-- The supported degree space is the actual embedded `u` chart module of that degree. -/
theorem uChartGrade_eq_overlap_inf_range (g : ι → ℤ) (k : ℤ) :
    uChartGrade (K := K) g k = overlapGrade (K := K) g k ⊓ LinearMap.range uFreeEmbedding := by
  rw [range_uFreeEmbedding, overlapGrade, ← Finsupp.supported_inter, uChartGrade]
  rfl

/-- The supported degree space is the actual embedded `v` chart module of that degree. -/
theorem vChartGrade_eq_overlap_inf_range (g : ι → ℤ) (k : ℤ) :
    vChartGrade (K := K) g k = overlapGrade (K := K) g k ⊓ LinearMap.range vFreeEmbedding := by
  rw [range_vFreeEmbedding, overlapGrade, ← Finsupp.supported_inter, vChartGrade]
  rfl

end ActualChartModules
end ChoppedPlane.LaurentChartComplex
