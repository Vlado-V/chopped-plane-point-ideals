module

public import ChoppedPlane.BinaryChartRings
public import ChoppedPlane.QWeylModule

@[expose] public section

/-!
# Binary polynomial maps into the two actual affine charts

Both chart substitutions become the same binary Laurent substitution after
the chart embeddings. This compatibility uses the literal polynomial rings.
-/

noncomputable section
namespace ChoppedPlane.QWeyl

open MvPolynomial BinaryChartRings LaurentPairing

variable {K : Type*} [Field K]

/-- Substitute the two binary variables into the actual `u` chart. -/
def binaryUChart : BinaryRing K →ₐ[K] URing K :=
  aeval ![uU, vU]

/-- Substitute the two binary variables into the actual `v` chart. -/
def binaryVChart : BinaryRing K →ₐ[K] VRing K :=
  aeval ![uV, vV]

/-- The shared binary substitution into the overlap Laurent ring. -/
def binaryChartLaurentMap : BinaryRing K →ₐ[K] BinaryLaurent K :=
  aeval ![U, V]

@[simp] theorem binaryUChart_binaryU :
    binaryUChart (binaryU K) = (uU : URing K) := by
  simp [binaryUChart, binaryU]

@[simp] theorem binaryUChart_binaryV :
    binaryUChart (binaryV K) = (vU : URing K) := by
  simp [binaryUChart, binaryV]

@[simp] theorem binaryVChart_binaryU :
    binaryVChart (binaryU K) = (uV : VRing K) := by
  simp [binaryVChart, binaryU]

@[simp] theorem binaryVChart_binaryV :
    binaryVChart (binaryV K) = (vV : VRing K) := by
  simp [binaryVChart, binaryV]

@[simp] theorem binaryChartLaurentMap_binaryU :
    binaryChartLaurentMap (binaryU K) = (U : BinaryLaurent K) := by
  simp [binaryChartLaurentMap, binaryU]

@[simp] theorem binaryChartLaurentMap_binaryV :
    binaryChartLaurentMap (binaryV K) = (V : BinaryLaurent K) := by
  simp [binaryChartLaurentMap, binaryV]

/-- The `u` chart polynomial map agrees with the canonical overlap map. -/
theorem uEmbedding_comp_binaryUChart :
    (uEmbedding (K := K)).comp binaryUChart = binaryChartLaurentMap := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [binaryUChart, binaryChartLaurentMap]

/-- The `v` chart polynomial map agrees with the same canonical overlap map. -/
theorem vEmbedding_comp_binaryVChart :
    (vEmbedding (K := K)).comp binaryVChart = binaryChartLaurentMap := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [binaryVChart, binaryChartLaurentMap]

@[simp] theorem uEmbedding_binaryUChart (f : BinaryRing K) :
    uEmbedding (binaryUChart f) = binaryChartLaurentMap f := by
  change ((uEmbedding (K := K)).comp binaryUChart) f = _
  rw [uEmbedding_comp_binaryUChart]

@[simp] theorem vEmbedding_binaryVChart (f : BinaryRing K) :
    vEmbedding (binaryVChart f) = binaryChartLaurentMap f := by
  change ((vEmbedding (K := K)).comp binaryVChart) f = _
  rw [vEmbedding_comp_binaryVChart]

theorem binaryCharts_agree_on_overlap (f : BinaryRing K) :
    uEmbedding (binaryUChart f) = vEmbedding (binaryVChart f) := by
  simp

end ChoppedPlane.QWeyl
