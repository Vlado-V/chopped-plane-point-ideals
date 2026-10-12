module

public import ChoppedPlane.QWeylModule
public import Mathlib.Algebra.Algebra.Tower

@[expose] public section

/-! The actual quotient-ring module action is compatible with the original
coefficient-field action on the free coefficient vectors. -/
noncomputable section
namespace ChoppedPlane.QWeyl
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

abbrev cyclicModuleScalarTower (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) :
    letI := cyclicModuleStructure F Z hZ
    IsScalarTower K (CyclicCubicRing A F) (Fin 3 → A) := by
  let := cyclicModuleStructure F Z hZ
  refine ⟨?_⟩
  intro k r m
  change cyclicActionHom F Z hZ (k • r) m = k • cyclicActionHom F Z hZ r m
  have hcoeff : k • r = cyclicCoefficientHom F (algebraMap K A k) * r := by
    exact (Algebra.smul_def k r).trans (by rfl)
  rw [hcoeff, map_mul, Module.End.mul_apply, cyclicActionHom_coefficient]
  funext i
  simp [Algebra.smul_def, Module.algebraMap_end_apply]

abbrev cyclicModuleSMulCommClass (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) :
    letI := cyclicModuleStructure F Z hZ
    SMulCommClass K (CyclicCubicRing A F) (Fin 3 → A) := by
  let := cyclicModuleStructure F Z hZ
  refine ⟨?_⟩
  intro k r m
  change k • cyclicActionHom F Z hZ r m = cyclicActionHom F Z hZ r (k • m)
  have hsmul (v : Fin 3 → A) : k • v = algebraMap K A k • v := by
    funext i
    simp [Pi.smul_apply, Algebra.smul_def]
  rw [hsmul, hsmul]
  exact ((cyclicActionHom F Z hZ r).map_smul (algebraMap K A k) m).symm

theorem cyclicModule_algebraMap_smul (F : A) (Z : Module.End A (Fin 3 → A))
    (hZ : Z ^ 3 = F • 1) :
    letI := cyclicModuleStructure F Z hZ
    ∀ (k : K) (m : Fin 3 → A),
      algebraMap K (CyclicCubicRing A F) k • m = k • m := by
  intro k m
  change cyclicActionHom F Z hZ (cyclicCoefficientHom F (algebraMap K A k)) m = k • m
  rw [cyclicActionHom_coefficient]
  funext i
  simp [Algebra.smul_def, Module.algebraMap_end_apply]

end ChoppedPlane.QWeyl
