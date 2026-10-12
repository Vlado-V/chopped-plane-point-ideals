module

public import ChoppedPlane.ChopRankOpen
public import ChoppedPlane.EasyRange

@[expose] public section

/-!
# Finite witness transfer in the many-generator range

These theorems prove the finite-to-infinite-degree transfer using actual
point ideals. The existence of the finite witness remains an explicit input;
it is not assumed as part of the final manuscript statement.
-/
noncomputable section
set_option maxHeartbeats 800000
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K] {p d e : ℕ}

/-- Equal quotient dimensions force equality of the two actual homogeneous
pieces, because the chopped piece is contained in the point-ideal piece. -/
theorem chopEqualsPointPiece_iff_hilbert_eq (a : PointCoordinates K p) :
    ChopEqualsPointPiece K a d (d + e) ↔
      choppedHilbertFunction a d (d + e) = pointHilbertFunction K a (d + e) := by
  constructor
  · exact choppedHilbertFunction_eq_point_of_piece_eq a
  · intro hdim
    have h₁ := (generatedProducts (d := d) (pointDegreeSpace K a d) e).finrank_quotient_add_finrank
    have h₂ := (pointDegreePiece K a (d + e)).finrank_quotient_add_finrank
    rw [generated_finrank_eq_hilbertFunction _ (pointDegreeSpace_homogeneous a) e] at h₁
    change pointHilbertFunction K a (d + e) + _ = _ at h₂
    change generatedHilbertFunction _ _ = _ at hdim
    have hrank : finrank K (generatedProducts (d := d) (pointDegreeSpace K a d) e) =
        finrank K (pointDegreePiece K a (d + e)) := by omega
    have hEq := Submodule.eq_of_le_of_finrank_eq
      (generatedProducts_le_pointDegreePiece (d := d) (e := e) a) hrank
    intro f
    rw [show f.val ∈ choppedIdeal K a d ↔
      f ∈ generatedProducts (d := d) (pointDegreeSpace K a d) e from
        form_mem_ideal_iff e _ (pointDegreeSpace_homogeneous a) f]
    rw [hEq]
    exact (homogeneous_mem_pointIdeal_iff a f).symm

/-- Convert formwise equality to equality of ambient homogeneous pieces. -/
theorem pointDegreeSpace_eq_chop_of_piece_eq {t : ℕ} (a : PointCoordinates K p)
    (h : ChopEqualsPointPiece K a d t) :
    pointDegreeSpace K a t = idealDegreeSpace (choppedIdeal K a d) t := by
  rw [pointDegreeSpace_eq_idealDegreeSpace]
  ext P
  constructor
  · rintro ⟨hhom,hmem⟩
    exact ⟨hhom,(h ⟨P,hhom⟩).mpr hmem⟩
  · rintro ⟨hhom,hmem⟩
    exact ⟨hhom,(h ⟨P,hhom⟩).mp hmem⟩

/-- Interpolation in the chopped degree propagates equality at any later base
    degree to all degrees beyond that base. -/
theorem chopEqualsPointPiece_above {q : ℕ} (a : PointCoordinates K p)
    (hq : d + 1 ≤ q) (hs : Function.Surjective (pointEvaluation K a d))
    (hbase : ChopEqualsPointPiece K a d q) :
    ∀ t, q ≤ t → ChopEqualsPointPiece K a d t := by
  have hsurj := pointEvaluation_surjective_of_le a hs (show d ≤ q - 1 by omega)
  have hall := pointDegreeSpace_eq_of_degree_eq a (by omega : 1 ≤ q) hsurj
    (choppedIdeal K a d) (choppedIdeal_le_pointIdeal a)
    (pointDegreeSpace_eq_chop_of_piece_eq a hbase)
  intro t ht f
  have heq := hall t ht
  rw [pointDegreeSpace_eq_idealDegreeSpace] at heq
  have hh := congrArg (fun U : Submodule K (Poly K 3) => f.val ∈ U) heq
  simpa [idealDegreeSpace,f.property] using hh.symm

/-- In the intermediate range, the expected maximum equals the point count
    precisely at and beyond the numerical cutoff. -/
theorem intermediate_max_eq_point_iff {d p e : ℕ}
    (hp : p < N d) (hr : 3 ≤ N d - p) (he : 1 ≤ e) :
    max p (N (d + e) - (N d - p) * N e) = p ↔ cutoff d (N d - p) ≤ e := by
  let r := N d - p
  have hpr : N d - r = p := by dsimp [r]; omega
  have hcast : ((N d - r : ℕ) : ℤ) = (N d : ℤ) - (r : ℤ) := by
    rw [Nat.cast_sub (show r ≤ N d by dsimp [r]; omega)]
  have hformula := hilbert_max_nat_identity (d := d) (r := r)
    (show r ≤ N d by dsimp [r]; omega) e
  rw [hpr,← hcast,hpr] at hformula
  have hsign := residual_nonpos_iff_cutoff_le (d := d) (r := r) hr he
  constructor
  · intro hmax
    have hres : residual d r e ≤ 0 := by rw [hmax] at hformula; omega
    exact hsign.mp hres
  · intro hcut
    have hres := hsign.mpr hcut
    have hmax : max (residual d r e) 0 = 0 := max_eq_right hres
    rw [hmax] at hformula
    dsimp [r] at hformula
    omega

end ChoppedPlane

namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- The expected point quotient is already constant from the chopped degree in
    the intermediate point-count range. -/
theorem pointHilbertFunction_above_intermediate {p d e : ℕ} (a : PointCoordinates K p)
    (hp : p < N d) (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p) :
    pointHilbertFunction K a (d + e) = p := by
  rw [hpoint,min_eq_right]
  exact hp.le.trans (by dsimp [N]; exact Nat.choose_le_choose 2 (by omega))

/-- All numerical maximum formulas imply the complete actual-ideal conclusion,
    including the least positive filling degree. -/
theorem mainConclusion_of_intermediate_formula {p d : ℕ} (a : PointCoordinates K p)
    (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d) (hr : 3 ≤ N d - p)
    (hdist : DistinctPoints K a)
    (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p)
    (hchop : ∀ e, choppedHilbertFunction a d (d + e) =
      max p (N (d + e) - (N d - p) * N e)) : MainConclusion K a d := by
  have hrd : N d - p ≤ d := (generator_count_bounds (by omega) hlo hhi).2
  refine ⟨hdist,hpoint,?_,?_,?_,?_⟩
  · intro t
    by_cases ht : t < d
    · rw [choppedHilbertFunction_below_degree a ht]
      simp [expectedChoppedHilbertFunction,ht,N]
    · obtain ⟨e,rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ t)
      rw [hchop]
      simp only [expectedChoppedHilbertFunction,ht,ite_false,
        not_le.mpr hhi,not_le.mpr hlo]
      have hr2 : ¬ N d - p ≤ 2 := by omega
      simp only [hr2, ite_false, Nat.add_sub_cancel_left]
  · intro hh
    omega
  · intro hh
    omega
  · intro _ _
    dsimp only
    constructor
    · intro hh
      omega
    · intro _
      refine ⟨cutoff_lt_degree hd hr hrd,?_⟩
      intro e he
      rw [chopEqualsPointPiece_iff_hilbert_eq,hchop,
        pointHilbertFunction_above_intermediate a hhi hpoint]
      exact intermediate_max_eq_point_iff hhi hr he

/-- Interpolation and the finite formulas through the cutoff imply all formulas
    in every degree, by propagation in the actual point ideal. -/
theorem intermediate_formula_of_finite_witness {p d : ℕ} (a : PointCoordinates K p)
    (hhi : p < N d) (hr : 3 ≤ N d - p)
    (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p)
    (hs : Function.Surjective (pointEvaluation K a d))
    (hfinite : ∀ e, e ≤ cutoff d (N d - p) →
      choppedHilbertFunction a d (d + e) = max p (N (d + e) - (N d - p) * N e)) :
    ∀ e, choppedHilbertFunction a d (d + e) = max p (N (d + e) - (N d - p) * N e) := by
  have hcut : max p (N (d + cutoff d (N d - p)) -
      (N d - p) * N (cutoff d (N d - p))) = p :=
    (intermediate_max_eq_point_iff hhi hr (cutoff_pos d (N d - p))).mpr le_rfl
  have hbase : ChopEqualsPointPiece K a d (d + cutoff d (N d - p)) := by
    apply (chopEqualsPointPiece_iff_hilbert_eq a).mpr
    rw [hfinite _ le_rfl,hcut,pointHilbertFunction_above_intermediate a hhi hpoint]
  have hfill := chopEqualsPointPiece_above a
    (by have hh := cutoff_pos d (N d - p); omega) hs hbase
  intro e
  by_cases he : e ≤ cutoff d (N d - p)
  · exact hfinite e he
  · have hce : cutoff d (N d - p) ≤ e := by omega
    have hepos : 1 ≤ e := (cutoff_pos d (N d - p)).trans hce
    rw [choppedHilbertFunction_eq_point_of_piece_eq a (hfill _ (by omega)),
      pointHilbertFunction_above_intermediate a hhi hpoint,
      (intermediate_max_eq_point_iff hhi hr hepos).mpr hce]

end ChoppedPlane

namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- A single interpolation witness attaining the predicted chopped dimensions
    in finitely many degrees proves the complete generic theorem in the
    many-generator range. The finite witness is an explicit construction
    obligation, rather than an assumption hidden in the statement. -/
theorem genericChoppedConclusion_intermediate_of_witness [CharZero K]
    (d p : ℕ) (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : 3 ≤ N d - p) (a₀ : PointCoordinates K p)
    (hs : Function.Surjective (pointEvaluation K a₀ d))
    (hwitness : ∀ e, e ≤ cutoff d (N d - p) →
      choppedHilbertFunction a₀ d (d + e) = max p (N (d + e) - (N d - p) * N e)) :
    GenericChoppedConclusion K d p := by
  classical
  let c := cutoff d (N d - p)
  choose D hD hupper using fun i : Fin (c + 1) =>
    choppedHilbertFunction_principal_upper a₀ hs i.val
  obtain ⟨G,hG,hgeneral⟩ := generic_pointHilbertFunction (K := K) p
  let E := G * ∏ i, D i
  have hne : E ≠ 0 := by
    apply mul_ne_zero
    · obtain ⟨a,ha⟩ := hG
      intro hz
      simp only [hz,map_zero] at ha
      exact ha rfl
    · apply Finset.prod_ne_zero_iff.mpr
      intro i _ hz
      have hh := hD i
      simp only [hz,map_zero] at hh
      exact hh rfl
  have hex : ∃ a : PointCoordinates K p, eval a E ≠ 0 := by
    by_contra! h
    exact hne (MvPolynomial.funext h)
  refine ⟨E,hex,?_⟩
  intro a ha
  have hparts : eval a G ≠ 0 ∧ ∀ i, eval a (D i) ≠ 0 := by
    simpa only [E,map_mul,map_prod,mul_ne_zero_iff,Finset.prod_ne_zero_iff,
      Finset.mem_univ,forall_true_left] using ha
  obtain ⟨hdist,hpoint⟩ := hgeneral a hparts.1
  have hpoint' : ∀ t, pointHilbertFunction K a t = min (N t) p := by
    simpa only [N] using hpoint
  have hsa : Function.Surjective (pointEvaluation K a d) :=
    (hupper ⟨0,by omega⟩ a (hparts.2 ⟨0,by omega⟩)).1
  have hfinite : ∀ e, e ≤ cutoff d (N d - p) →
      choppedHilbertFunction a d (d + e) = max p (N (d + e) - (N d - p) * N e) := by
    intro e he
    have hi : e < c + 1 := by dsimp [c]; omega
    have hu := (hupper ⟨e,hi⟩ a (hparts.2 ⟨e,hi⟩)).2
    rw [hwitness e he] at hu
    have hpd : pointHilbertFunction K a d = p := by
      rw [hpoint',min_eq_right hhi.le]
    have hk : finrank K (pointDegreePiece K a d) = N d - p := by
      rw [pointDegreePiece_finrank,hpd]
      rfl
    have hl := choppedHilbertFunction_lower_bounds (d := d) (e := e) a
    rw [pointHilbertFunction_above_intermediate a hhi hpoint',hk] at hl
    exact le_antisymm hu hl
  exact mainConclusion_of_intermediate_formula a hd hlo hhi hr hdist hpoint'
    (intermediate_formula_of_finite_witness a hhi hr hpoint' hsa hfinite)

end ChoppedPlane
