module

public import ChoppedPlane.LaurentChartComplex

@[expose] public section

/-!
# Graded local exactness by actual coefficient projection

An ungraded local preimage can be projected to the necessary coefficient
degree whenever the actual operator commutes with coefficient projection.
The second part projects preimages in the literal Laurent images of free
modules over the two genuine binary chart rings.
-/

noncomputable section
namespace ChoppedPlane.GradedLocalExactness

variable {K : Type*} [Field K]
variable {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
variable [Module K U] [Module K V] [Module K W]

/-- Project an actual local preimage to its required coefficient degree. -/
theorem graded_preimage
    (G : ℤ → Submodule K U) (H : ℤ → Submodule K V)
    (pU : ℤ → U →ₗ[K] U) (pV : ℤ → V →ₗ[K] V)
    (hpU : ∀ k u, pU k u ∈ G k)
    (hpV : ∀ k v, v ∈ H k → pV k v = v)
    (L : U →ₗ[K] V) (Q : V →ₗ[K] W)
    (hexact : ∀ v, Q v = 0 ↔ v ∈ LinearMap.range L)
    (a b : ℤ) (hcomm : L.comp (pU a) = (pV b).comp L)
    (v : V) (hv : v ∈ H b) (hq : Q v = 0) :
    ∃ u : U, u ∈ G a ∧ L u = v := by
  obtain ⟨u, hu⟩ := (hexact v).mp hq
  refine ⟨pU a u, hpU a u, ?_⟩
  have hc := LinearMap.congr_fun hcomm u
  change L (pU a u) = pV b (L u) at hc
  rw [hc, hu, hpV b v hv]

/-- Kernel/range exactness also gives graded preimages under projection. -/
theorem graded_preimage_of_kernel_range
    (G : ℤ → Submodule K U) (H : ℤ → Submodule K V)
    (pU : ℤ → U →ₗ[K] U) (pV : ℤ → V →ₗ[K] V)
    (hpU : ∀ k u, pU k u ∈ G k)
    (hpV : ∀ k v, v ∈ H k → pV k v = v)
    (L : U →ₗ[K] V) (Q : V →ₗ[K] W)
    (hexact : LinearMap.ker Q = LinearMap.range L)
    (a b : ℤ) (hcomm : L.comp (pU a) = (pV b).comp L)
    (v : V) (hv : v ∈ H b) (hq : Q v = 0) :
    ∃ u : U, u ∈ G a ∧ L u = v := by
  apply graded_preimage G H pU pV hpU hpV L Q _ a b hcomm v hv hq
  intro w
  rw [← LinearMap.mem_ker, hexact]

/-- The actual operator restricted to the specified source and target grades. -/
def gradedRestriction (L : U →ₗ[K] V) (G : Submodule K U) (H : Submodule K V)
    (hL : ∀ u, u ∈ G → L u ∈ H) : G →ₗ[K] H :=
  (L.domRestrict G).codRestrict H (fun u => hL u.val u.property)

@[simp] theorem gradedRestriction_val (L : U →ₗ[K] V)
    (G : Submodule K U) (H : Submodule K V)
    (hL : ∀ u, u ∈ G → L u ∈ H) (u : G) :
    (gradedRestriction L G H hL u).val = L u.val := rfl

/-- Restricting an actual local complex to compatible coefficient degrees
preserves exactness; no graded preimage hypothesis is postulated. -/
theorem graded_kernel_range
    (G : ℤ → Submodule K U) (H : ℤ → Submodule K V)
    (pU : ℤ → U →ₗ[K] U) (pV : ℤ → V →ₗ[K] V)
    (hpU : ∀ k u, pU k u ∈ G k)
    (hpV : ∀ k v, v ∈ H k → pV k v = v)
    (L : U →ₗ[K] V) (Q : V →ₗ[K] W)
    (hexact : ∀ v, Q v = 0 ↔ v ∈ LinearMap.range L)
    (a b : ℤ) (hcomm : L.comp (pU a) = (pV b).comp L)
    (hL : ∀ u, u ∈ G a → L u ∈ H b) :
    LinearMap.ker (Q.domRestrict (H b)) =
      LinearMap.range (gradedRestriction L (G a) (H b) hL) := by
  ext v
  rw [LinearMap.mem_ker]
  change Q v.val = 0 ↔ _
  constructor
  · intro hv
    obtain ⟨u, hu, hlu⟩ := graded_preimage G H pU pV hpU hpV L Q hexact
      a b hcomm v.val v.property hv
    exact ⟨⟨u, hu⟩, Subtype.ext hlu⟩
  · rintro ⟨u, rfl⟩
    exact (hexact _).mpr ⟨u.val, rfl⟩

/-- The degree-`d` version, with the necessary preimage degree `k-d`. -/
theorem graded_preimage_of_shift
    (G : ℤ → Submodule K U) (H : ℤ → Submodule K V)
    (pU : ℤ → U →ₗ[K] U) (pV : ℤ → V →ₗ[K] V)
    (hpU : ∀ k u, pU k u ∈ G k)
    (hpV : ∀ k v, v ∈ H k → pV k v = v)
    (L : U →ₗ[K] V) (Q : V →ₗ[K] W)
    (hexact : ∀ v, Q v = 0 ↔ v ∈ LinearMap.range L)
    (d : ℤ) (hcomm : ∀ k, L.comp (pU k) = (pV (k + d)).comp L)
    (k : ℤ) (v : V) (hv : v ∈ H k) (hq : Q v = 0) :
    ∃ u : U, u ∈ G (k - d) ∧ L u = v := by
  apply graded_preimage G H pU pV hpU hpV L Q hexact (k - d) k _ v hv hq
  simpa using hcomm (k - d)

section ActualLaurentCharts

open LaurentPairing LaurentChartComplex BinaryChartRings
variable {ι κ : Type*} [Finite ι]

/-- Project an actual `u` chart preimage into the necessary coefficient degree.
The preimage lies in the image of the genuine chart-ring module. -/
theorem uChart_preimage_by_projection
    (g : ι → ℤ) (h : κ → ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hL : ∀ j x, x ∈ overlapGrade (K := K) g j →
      L x ∈ overlapGrade (K := K) h (j + 1))
    (k : ℤ) (p : FreeLaurent K κ) (hp : p ∈ uChartGrade (K := K) h k)
    (hpreimage : ∃ x : FreeLaurent K ι,
      x ∈ LinearMap.range (uFreeEmbedding (K := K) (ι := ι)) ∧ L x = p) :
    ∃ x : FreeLaurent K ι, x ∈ uChartGrade (K := K) g (k - 1) ∧ L x = p := by
  obtain ⟨x, hx, hlx⟩ := hpreimage
  refine ⟨gradeProjection g (k - 1) x, ?_, ?_⟩
  · apply gradeProjection_preserves_uChartSupport g (k - 1) x
    simpa only [range_uFreeEmbedding] using hx
  · have hc : gradeProjection h k (L x) = L (gradeProjection g (k - 1) x) := by
      have hc := LinearMap.congr_fun
        (gradeProjection_commutes_of_degree_shift g h 1 L hL (k - 1)) x
      simpa only [LinearMap.comp_apply, sub_add_cancel] using hc
    rw [← hc, hlx]
    exact (mem_overlapGrade_iff_gradeProjection_eq h k p).mp
      (uChartGrade_le_overlapGrade (K := K) h k hp)

/-- Project an actual `v` chart preimage into the necessary coefficient degree. -/
theorem vChart_preimage_by_projection
    (g : ι → ℤ) (h : κ → ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (hL : ∀ j x, x ∈ overlapGrade (K := K) g j →
      L x ∈ overlapGrade (K := K) h (j + 1))
    (k : ℤ) (p : FreeLaurent K κ) (hp : p ∈ vChartGrade (K := K) h k)
    (hpreimage : ∃ x : FreeLaurent K ι,
      x ∈ LinearMap.range (vFreeEmbedding (K := K) (ι := ι)) ∧ L x = p) :
    ∃ x : FreeLaurent K ι, x ∈ vChartGrade (K := K) g (k - 1) ∧ L x = p := by
  obtain ⟨x, hx, hlx⟩ := hpreimage
  refine ⟨gradeProjection g (k - 1) x, ?_, ?_⟩
  · apply gradeProjection_preserves_vChartSupport g (k - 1) x
    simpa only [range_vFreeEmbedding] using hx
  · have hc : gradeProjection h k (L x) = L (gradeProjection g (k - 1) x) := by
      have hc := LinearMap.congr_fun
        (gradeProjection_commutes_of_degree_shift g h 1 L hL (k - 1)) x
      simpa only [LinearMap.comp_apply, sub_add_cancel] using hc
    rw [← hc, hlx]
    exact (mem_overlapGrade_iff_gradeProjection_eq h k p).mp
      (vChartGrade_le_overlapGrade (K := K) h k hp)

variable [Finite κ]

/-- Actual `u` chart local exactness specializes to its coefficient grades. -/
theorem uChart_graded_local_preimage
    (g : ι → ℤ) (h : κ → ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (Q : FreeLaurent K κ →ₗ[K] W)
    (hL : ∀ j x, x ∈ overlapGrade (K := K) g j →
      L x ∈ overlapGrade (K := K) h (j + 1))
    (hexact : ∀ p : FreeLaurent K κ,
      p ∈ LinearMap.range (uFreeEmbedding (K := K) (ι := κ)) → Q p = 0 →
      ∃ x : FreeLaurent K ι,
        x ∈ LinearMap.range (uFreeEmbedding (K := K) (ι := ι)) ∧ L x = p)
    (k : ℤ) (p : FreeLaurent K κ) (hp : p ∈ uChartGrade (K := K) h k)
    (hq : Q p = 0) :
    ∃ x : FreeLaurent K ι, x ∈ uChartGrade (K := K) g (k - 1) ∧ L x = p := by
  apply uChart_preimage_by_projection g h L hL k p hp
  apply hexact p _ hq
  rw [uChartGrade_eq_overlap_inf_range] at hp
  exact hp.2

/-- Actual `v` chart local exactness specializes to its coefficient grades. -/
theorem vChart_graded_local_preimage
    (g : ι → ℤ) (h : κ → ℤ)
    (L : FreeLaurent K ι →ₗ[K] FreeLaurent K κ)
    (Q : FreeLaurent K κ →ₗ[K] W)
    (hL : ∀ j x, x ∈ overlapGrade (K := K) g j →
      L x ∈ overlapGrade (K := K) h (j + 1))
    (hexact : ∀ p : FreeLaurent K κ,
      p ∈ LinearMap.range (vFreeEmbedding (K := K) (ι := κ)) → Q p = 0 →
      ∃ x : FreeLaurent K ι,
        x ∈ LinearMap.range (vFreeEmbedding (K := K) (ι := ι)) ∧ L x = p)
    (k : ℤ) (p : FreeLaurent K κ) (hp : p ∈ vChartGrade (K := K) h k)
    (hq : Q p = 0) :
    ∃ x : FreeLaurent K ι, x ∈ vChartGrade (K := K) g (k - 1) ∧ L x = p := by
  apply vChart_preimage_by_projection g h L hL k p hp
  apply hexact p _ hq
  rw [vChartGrade_eq_overlap_inf_range] at hp
  exact hp.2

end ActualLaurentCharts
end ChoppedPlane.GradedLocalExactness
