module

public import ChoppedPlane.SymmetricCoordinates
public import ChoppedPlane.Homogeneous

@[expose] public section

/-! Coefficient extension and scaling for the actual module-valued symmetric
kernel. These maps are explicit on the finite coefficient representation. -/
noncomputable section
namespace ChoppedPlane.SymmetricDerivative
open MvPolynomial
open scoped TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
variable {σ τ : Type*} {θ : R →+* S}

/-- Extend module coefficients along a semilinear coefficient map. -/
def tensorBaseChange (ψ : M →ₛₗ[θ] N) :
    (MvPolynomial σ R ⊗[R] M) →ₛₗ[θ] (MvPolynomial σ S ⊗[S] N) := by
  classical
  let a : (MvPolynomial σ R ⊗[R] M) →+ (MvPolynomial σ S ⊗[S] N) :=
    (tensorCoefficients (R := S) (M := N) (σ := σ)).symm.toAddEquiv.toAddMonoidHom.comp
      ((Finsupp.mapRange.addMonoidHom ψ.toAddMonoidHom).comp
        (tensorCoefficients (R := R) (M := M) (σ := σ)).toAddEquiv.toAddMonoidHom)
  refine { a with map_smul' := ?_ }
  intro r P
  apply (tensorCoefficients (R := S) (M := N)).injective
  ext s
  simp [a, ψ.map_smulₛₗ]

@[simp] theorem tensorCoefficients_baseChange (ψ : M →ₛₗ[θ] N)
    (P : MvPolynomial σ R ⊗[R] M) (s : σ →₀ ℕ) :
    tensorCoefficients (tensorBaseChange ψ P) s = ψ (tensorCoefficients P s) := by
  classical
  simp [tensorBaseChange]

@[simp] theorem tensorBaseChange_tmul (ψ : M →ₛₗ[θ] N)
    (P : MvPolynomial σ R) (m : M) :
    tensorBaseChange ψ (P ⊗ₜ[R] m) = MvPolynomial.map θ P ⊗ₜ[S] ψ m := by
  apply tensorCoefficients.injective
  ext s
  simp [ψ.map_smulₛₗ, coeff_map]

/-- Injectivity of coefficient extension does not require flatness. -/
theorem tensorBaseChange_injective (ψ : M →ₛₗ[θ] N) (hψ : Function.Injective ψ) :
    Function.Injective (tensorBaseChange (σ := σ) ψ) := by
  intro P Q h
  apply tensorCoefficients.injective
  ext s
  apply hψ
  simpa using congrArg (fun A => tensorCoefficients A s) h

/-- Coefficient extension preserves auxiliary homogeneous degree. -/
theorem tensorBaseChange_homogeneous (ψ : M →ₛₗ[θ] N)
    {n : ℕ} {P : MvPolynomial σ R ⊗[R] M} (hP : TensorHomogeneous n P) :
    TensorHomogeneous n (tensorBaseChange ψ P) := by
  apply (tensorHomogeneous_iff_coefficients n _).mpr
  intro s hs
  rw [tensorCoefficients_baseChange, (tensorHomogeneous_iff_coefficients n _).mp hP s hs,
    map_zero]

/-- A linear auxiliary substitution commutes with coefficient extension. -/
theorem tensorBaseChange_substitution (ψ : M →ₛₗ[θ] N)
    (L : σ → MvPolynomial τ R) (P : MvPolynomial σ R ⊗[R] M) :
    tensorBaseChange ψ ((aeval L).toLinearMap.rTensor M P) =
      (aeval (fun i => MvPolynomial.map θ (L i))).toLinearMap.rTensor N (tensorBaseChange ψ P) := by
  induction P using TensorProduct.inductionOn with
  | tmul P m =>
    simp only [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, tensorBaseChange_tmul]
    congr 1
    change MvPolynomial.map θ (eval₂ C L P) =
      eval₂ C (MvPolynomial.map θ ∘ L) (MvPolynomial.map θ P)
    exact map_eval₂ θ L P
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- A common scalar factor in all auxiliary substitutions appears to the
power of the auxiliary homogeneous degree. -/
theorem tensor_substitution_scale (a : R) (L : σ → MvPolynomial τ R)
    {n : ℕ} (P : MvPolynomial σ R ⊗[R] M) (hP : TensorHomogeneous n P) :
    (aeval (fun i => a • L i)).toLinearMap.rTensor M P =
      a ^ n • (aeval L).toLinearMap.rTensor M P := by
  have hs : (aeval (fun i => a • L i)).toLinearMap.comp (homogeneousComponent n) =
      (a ^ n • (aeval L : MvPolynomial σ R →ₐ[R] MvPolynomial τ R).toLinearMap).comp (homogeneousComponent n) := by
    apply LinearMap.ext
    intro Q
    change aeval (fun i => a • L i) (homogeneousComponent n Q) =
      a ^ n • aeval L (homogeneousComponent n Q)
    simpa only [aeval_def, algebraMap_eq, C_mul', ← map_pow] using
      ChoppedPlane.homogeneous_eval₂_scale (homogeneousComponent_isHomogeneous n Q)
        C L (C a)
  have ht := congrArg (fun T : MvPolynomial σ R →ₗ[R] MvPolynomial τ R => T.rTensor M) hs
  simp only [LinearMap.rTensor_comp, LinearMap.rTensor_smul] at ht
  have h := LinearMap.congr_fun ht P
  dsimp only [TensorHomogeneous] at hP
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, hP] using h

/-- Directional differentiation commutes with semilinear coefficient extension. -/
theorem tensorBaseChange_directional (ψ : M →ₛₗ[θ] N)
    (f : Fin 3 → R) (P : AuxTensor (R := R) (M := M)) :
    tensorBaseChange ψ (tensorDirectional f P) =
      tensorDirectional (fun i => θ (f i)) (tensorBaseChange ψ P) := by
  apply tensorCoefficients.injective
  ext s
  simp only [tensorCoefficients_baseChange, tensorCoefficients_directional,
    map_sum, ψ.map_smulₛₗ, map_mul, map_natCast]

@[simp] theorem binaryCoefficients_baseChange (ψ : M →ₛₗ[θ] N)
    (n : ℕ) (P : BinaryTensor (R := R) (M := M)) (j : Fin (n + 1)) :
    binaryCoefficients n (tensorBaseChange ψ P) j = ψ (binaryCoefficients n P j) :=
  tensorCoefficients_baseChange ψ P _

/-- The finite symmetric kernel basis commutes with extension of coefficients. -/
theorem tensorBaseChange_kernelSynthesis (ψ : M →ₛₗ[θ] N)
    (A : Matrix (Fin 3) (Fin 3) R) (n : ℕ) (c : Fin (n + 1) → M) :
    tensorBaseChange ψ (kernelSynthesis A n c) =
      kernelSynthesis (A.map θ) n (fun j => ψ (c j)) := by
  simp only [kernelSynthesis, map_sum, tensorBaseChange_tmul]
  congr 1
  ext j
  congr 1
  simp [linearForm, map_sum, map_mul, map_pow]

end ChoppedPlane.SymmetricDerivative
