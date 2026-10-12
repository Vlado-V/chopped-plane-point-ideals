module

public import ChoppedPlane.GeneralPoints
public import ChoppedPlane.GridSelection
public import ChoppedPlane.KernelRankOpen
public import ChoppedPlane.RegularPair
public import ChoppedPlane.Statement

@[expose] public section

/-! The full two-generator case on a genuine nonempty principal open in the
actual point configuration space. The grid supplies a witness; polynomial
kernel charts transfer regularity to general configurations. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K] {d p : ℕ}

/-- Positive-degree relatively prime forms are independent generators. -/
theorem pair_forms_linearIndependent (q : Fin 2 → Forms K 3 d) (hd : 0 < d)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val) :
    LinearIndependent K q := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let a : Fin 2 → Forms K 3 0 := fun j => ⟨C (c j), isHomogeneous_C _ _⟩
  have ham : multiplication q a = 0 := by
    apply Subtype.ext
    have hh := congrArg Subtype.val hc
    rw [multiplication_val, Fin.sum_univ_two]
    change (q 0).val * C (c 0) + (q 1).val * C (c 1) = 0
    rw [mul_comm (q 0).val (C (c 0)), mul_comm (q 1).val (C (c 1)),
      MvPolynomial.C_mul', MvPolynomial.C_mul']
    simpa only [Fin.sum_univ_two, Submodule.coe_add, Submodule.coe_smul,
      Submodule.coe_zero] using hh
  have ha : a = 0 := (injective_iff_map_eq_zero _).mp
    (pair_multiplication_injective_below q hq hcop (by omega : 0 < d)) a ham
  have hh := congrArg (fun a : Fin 2 → Forms K 3 0 => (a i).val) ha
  simpa [a] using hh

/-- A regular pair spanning the actual degree equations supplies the full
conclusion in the two-generator range. -/
theorem mainConclusion_two_generator (a : PointCoordinates K p)
    (hd : 2 ≤ d) (hlo : N (d - 1) < p) (hhi : p < N d) (hr : N d - p = 2)
    (hdist : DistinctPoints K a)
    (hpoint : ∀ t, pointHilbertFunction K a t = min (N t) p)
    (q : Fin 2 → Forms K 3 d) (hspace : generatorSpace q = pointDegreeSpace K a d)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val) :
    MainConclusion K a d := by
  have hregular : ChopHasRegularGenerators K a d 2 := by
    refine ⟨q, ?_, ?_⟩
    · rw [choppedIdeal, ← hspace, generatorSpace]
      exact (Submodule.span_span_of_tower K (Poly K 3) (Set.range (fun i => (q i).val))).symm
    · have hs := homogeneous_regular_pair (by omega : 0 < d) (q 0) (q 1) hq hcop
      simpa [List.ofFn_succ] using hs
  refine ⟨hdist, hpoint, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < d
    · simpa only [expectedChoppedHilbertFunction, ht, ite_true, N] using
        choppedHilbertFunction_below_degree a ht
    · have hseries := congrArg Int.toNat (pair_generatedHilbertFunction q hq hcop t)
      rw [hspace] at hseries
      simpa [choppedHilbertFunction, expectedChoppedHilbertFunction, ht,
        not_le.mpr hhi, not_le.mpr hlo, hr, completeIntersectionCoefficient] using hseries
  · intro h; omega
  · intro h; omega
  · intro _ _
    dsimp only
    rw [hr]
    constructor
    · intro _; exact hregular
    · intro h; omega

/-- The grid witness supplies two actual equations spanning precisely the
configuration's degree-`d` ideal. -/
theorem exists_two_generator_witness [CharZero K] (d : ℕ) (hd : 0 < d) :
    ∃ (a : PointCoordinates K ((d + 2).choose 2 - 2)) (q : Fin 2 → Forms K 3 d),
      pointDegreePiece K a d = Submodule.span K (Set.range q) ∧
      LinearIndependent K q ∧ (q 0).val ≠ 0 ∧ IsRelPrime (q 0).val (q 1).val := by
  classical
  let α : Fin d → K := fun i => (i.val : K)
  have hα : Function.Injective α := by intro i j hij; exact Fin.ext (Nat.cast_injective hij)
  obtain ⟨a, _, hkernel, _⟩ := Grid.exists_grid_subset hd α α hα hα
  let q : Fin 2 → Forms K 3 d := ![Grid.firstForm α, Grid.secondForm α]
  refine ⟨a, q, ?_, Grid.first_second_linearIndependent hd α α,
    Grid.planeFirst_ne_zero α, Grid.plane_equations_relPrime α α⟩
  ext f
  rw [mem_pointDegreePiece, hkernel]
  have hrange : Set.range q = {Grid.firstForm α, Grid.secondForm α} :=
    Matrix.range_cons_cons_empty _ _ _
  rw [hrange, Submodule.mem_span_pair]
  constructor
  · rintro ⟨b,c,h⟩; exact ⟨b,c,h.symm⟩
  · rintro ⟨b,c,h⟩; exact ⟨b,c,h.symm⟩

/-- A regular degree-`d` pair spanning point equations survives on a genuine
nonempty polynomial neighborhood of the witness. -/
theorem regular_pair_point_principal_open [CharZero K] (d : ℕ) (hd : 0 < d) :
    ∃ D : MvPolynomial (Fin ((d + 2).choose 2 - 2) × Fin 2) K,
      (∃ a, eval a D ≠ 0) ∧ ∀ a, eval a D ≠ 0 →
      ∃ q : Fin 2 → Forms K 3 d,
        generatorSpace q = pointDegreeSpace K a d ∧ (q 0).val ≠ 0 ∧
          IsRelPrime (q 0).val (q 1).val := by
  classical
  let p := (d + 2).choose 2 - 2
  obtain ⟨a₀, q₀, hkernel₀, hlin₀, hq₀, hcop₀⟩ := exists_two_generator_witness (K := K) d hd
  have hdim₀ : finrank K (pointDegreePiece K a₀ d) = 2 := by
    rw [hkernel₀, finrank_span_eq_card hlin₀, Fintype.card_fin]
  have hsurj₀ : Function.Surjective (pointEvaluation K a₀ d) := by
    apply pointEvaluation_surjective_of_hilbert_eq a₀
    have hh := (pointDegreePiece K a₀ d).finrank_quotient_add_finrank
    rw [hdim₀, finrank_plane_forms] at hh
    change pointHilbertFunction K a₀ d + 2 = _ at hh
    omega
  obtain ⟨D₀, C, hC, hD₀, hker, hchart, hfix⟩ := polynomial_kernel_chart
    (fun a : PointCoordinates K p => pointEvaluation K a d)
    (pointEvaluation_isPolynomialFamily p d) a₀ hsurj₀
  let q (a : PointCoordinates K p) : Fin 2 → Forms K 3 d := fun i => C a (q₀ i)
  have hqpoly : IsPolynomialFamily q := by
    intro ell
    exact hC
      { toFun := fun T => ell (fun i => T (q₀ i))
        map_add' := by
          intro T T'
          change ell ((fun i => T (q₀ i)) + (fun i => T' (q₀ i))) = _
          exact ell.map_add _ _
        map_smul' := by
          intro c T
          change ell (c • (fun i => T (q₀ i))) = c • ell (fun i => T (q₀ i))
          exact ell.map_smul c _ }
  have hq₀mem (i : Fin 2) : q₀ i ∈ (pointEvaluation K a₀ d).ker := by
    change q₀ i ∈ pointDegreePiece K a₀ d
    rw [hkernel₀]
    exact Submodule.subset_span ⟨i,rfl⟩
  have hqfix : q a₀ = q₀ := by funext i; exact hfix _ (hq₀mem i)
  obtain ⟨D₁, hD₁, hpair⟩ := pair_regular_principal_open hd q hqpoly a₀
    (by simpa [hqfix] using hq₀) (by simpa [hqfix] using hcop₀)
  refine ⟨D₀ * D₁, ⟨a₀, by rw [map_mul, hD₀, one_mul]; exact hD₁⟩, ?_⟩
  intro a ha
  have hparts : eval a D₀ ≠ 0 ∧ eval a D₁ ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using ha
  obtain ⟨hcop, _, _⟩ := hpair a hparts.2
  have hq : (q a 0).val ≠ 0 := by
    intro hz
    have hunit : IsUnit (q a 1).val := hcop (by simp only [hz]; exact dvd_zero _) dvd_rfl
    have hc := MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hunit
    have ht := (q a 1).property.totalDegree (IsUnit.ne_zero hunit)
    omega
  have hlin := pair_forms_linearIndependent (q a) hd hq hcop
  have hspanle : Submodule.span K (Set.range (q a)) ≤ pointDegreePiece K a d := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hker a ⟨q₀ i,rfl⟩
  have hdim : finrank K (pointDegreePiece K a d) = 2 := by
    have h₀ := (pointEvaluation K a₀ d).finrank_range_add_finrank_ker
    have h₁ := (pointEvaluation K a d).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj₀, finrank_top] at h₀
    rw [LinearMap.range_eq_top.mpr (hchart a hparts.1).2, finrank_top] at h₁
    change _ + finrank K (pointDegreePiece K a₀ d) = _ at h₀
    change _ + finrank K (pointDegreePiece K a d) = _ at h₁
    omega
  have hspan : Submodule.span K (Set.range (q a)) = pointDegreePiece K a d := by
    apply Submodule.eq_of_le_of_finrank_eq hspanle
    rw [finrank_span_eq_card hlin, Fintype.card_fin, hdim]
  refine ⟨q a, ?_, hq, hcop⟩
  rw [pointDegreeSpace, ← hspan, Submodule.map_span]
  rw [generatorSpace, ← Set.range_comp]
  rfl

/-- Full Theorem 1.1 in the two-generator range, with no extra rank or regularity
hypothesis and one common open for all degrees. -/
theorem genericChoppedConclusion_two_generator [CharZero K]
    (hd : 2 ≤ d) (_hp : 1 ≤ p) (hlo : N (d - 1) < p) (hhi : p < N d)
    (hr : N d - p = 2) : GenericChoppedConclusion K d p := by
  have hp : p = (d + 2).choose 2 - 2 := by dsimp [N] at hhi hr; omega
  subst p
  obtain ⟨D₀, hD₀, hpoint⟩ := generic_pointHilbertFunction (K := K) ((d + 2).choose 2 - 2)
  obtain ⟨D₁, hD₁, hpair⟩ := regular_pair_point_principal_open (K := K) d (by omega)
  have hD₀ne : D₀ ≠ 0 := by rintro rfl; simp at hD₀
  have hD₁ne : D₁ ≠ 0 := by rintro rfl; simp at hD₁
  have hprodne : D₀ * D₁ ≠ 0 := mul_ne_zero hD₀ne hD₁ne
  have hex : ∃ a, eval a (D₀ * D₁) ≠ 0 := by
    by_contra! h
    exact hprodne (MvPolynomial.funext h)
  refine ⟨D₀ * D₁, hex, ?_⟩
  intro a ha
  have hparts : eval a D₀ ≠ 0 ∧ eval a D₁ ≠ 0 := by
    simpa only [map_mul, mul_ne_zero_iff] using ha
  obtain ⟨hdist, hpoint⟩ := hpoint a hparts.1
  obtain ⟨q, hspace, hq, hcop⟩ := hpair a hparts.2
  exact mainConclusion_two_generator a hd hlo hhi hr hdist (by simpa only [N] using hpoint)
    q hspace hq hcop

end ChoppedPlane
