module

public import ChoppedPlane.LaurentAuxiliaryScalarOperators

@[expose] public section

/-! Actual coefficientwise projection of the tensor auxiliary maps commutes
with their finite monomial formulas. This identifies literal top-Laurent
projection after finite multiplication with the projected coefficient action. -/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module SymmetricDerivative FiniteCech
variable {K : Type*} [Field K]
variable {V W P Q : Type*} [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [AddCommGroup P] [Module K P]
  [AddCommGroup Q] [Module K Q]

/-- Actual coefficient projection after three-operator differentiation. -/
theorem operatorDifferential_project (T : Fin 3 → V →ₗ[K] W)
    (ι : P →ₗ[K] V) (ρ : W →ₗ[K] Q) (t : ℕ) (p : Sym (Fin 3) (t + 1) → P) :
    operatorDifferential (fun i => ρ.comp ((T i).comp ι)) t p =
      fun s => ρ (operatorDifferential T t (fun b => ι (p b)) s) := by
  funext s
  simp only [operatorDifferential_coeff, map_sum, map_smul, LinearMap.comp_apply]

/-- Actual coefficient projection after three-operator auxiliary multiplication. -/
theorem auxiliaryOperatorMultiply_project (T : Fin 3 → V →ₗ[K] W)
    (ι : P →ₗ[K] V) (ρ : W →ₗ[K] Q) (t : ℕ) (p : Sym (Fin 3) t → P) :
    auxiliaryOperatorMultiply (fun i => ρ.comp ((T i).comp ι)) t p =
      fun s => ρ (auxiliaryOperatorMultiply T t (fun b => ι (p b)) s) := by
  funext s
  simp only [auxiliaryOperatorMultiply_apply, map_sum, map_smul, LinearMap.comp_apply]

section Scalar
variable {R : Type*} [CommRing R] [Algebra K R]
variable {M : Type*} [AddCommGroup M] [Module R M] [Module K M] [IsScalarTower K R M]

/-- A literal projected finite tensor derivative is its projected scalar-action
coefficient operator, over the actual coefficient algebra. -/
theorem finiteDirectional_project (f : Fin 3 → R) (ι : P →ₗ[K] M) (ρ : M →ₗ[K] Q)
    (t : ℕ) (p : Sym (Fin 3) (t + 1) → P) :
    operatorDifferential (fun i => ρ.comp ((scalarAction (K := K) (f i)).comp ι)) t p =
      fun s => ρ (finiteDirectional f t (fun b => ι (p b)) s) := by
  rw [finiteDirectional_eq_operatorDifferential (K := K)]
  exact operatorDifferential_project _ _ _ _ _

/-- A literal projected finite tensor multiplication is its projected
scalar-action auxiliary coefficient operator. -/
theorem finiteMultiply_project (f : Fin 3 → R) (ι : P →ₗ[K] M) (ρ : M →ₗ[K] Q)
    (t : ℕ) (p : Sym (Fin 3) t → P) :
    auxiliaryOperatorMultiply (fun i => ρ.comp ((scalarAction (K := K) (f i)).comp ι)) t p =
      fun s => ρ (finiteMultiply f t (fun b => ι (p b)) s) := by
  rw [finiteMultiply_eq_auxiliaryOperatorMultiply (K := K)]
  exact auxiliaryOperatorMultiply_project _ _ _ _ _

end Scalar
end ChoppedPlane.LaurentPairing
