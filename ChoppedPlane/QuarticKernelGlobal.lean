module

public import ChoppedPlane.QuarticKernelCoordinates
public import ChoppedPlane.QWeylModule

@[expose] public section

/-! Global polynomial coefficients for the quartic directional kernel.
The two scalar minors clear coordinates to exactly the auxiliary degree;
relative primality then descends every coordinate in the binary free module. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace ChoppedPlane.QWeyl
open MvPolynomial Module
open ChoppedPlane.SymmetricDerivative
open scoped TensorProduct

variable {B F K : Type*} [CommRing B] [IsDomain B] [UniqueFactorizationMonoid B]
  [Field F] [Algebra B F] [IsFractionRing B F]
  [Field K] [CharZero K] [Algebra K F]

/-- The two chart matrices use the same symmetric kernel basis. -/
theorem quarticKernelSynthesis_charts {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (u v z a b : R) (n : ℕ) (c : Fin (n + 1) → M) :
    kernelSynthesis (quarticKernelMatrixU u v z a) n c =
      kernelSynthesis (quarticKernelMatrixV u v z b) n c := by
  simp only [kernelSynthesis, quarticKernelMatrixU, quarticKernelMatrixV,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- The row-zero lift has no influence on the symmetric kernel expression. -/
theorem quarticKernelSynthesis_lift {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (u v z a b : R) (n : ℕ) (c : Fin (n + 1) → M) :
    kernelSynthesis (quarticKernelMatrixU u v z a) n c =
      kernelSynthesis (quarticKernelMatrixU u v z b) n c := by
  simp only [kernelSynthesis, quarticKernelMatrixU,
    Matrix.cons_val_one, Matrix.cons_val_two]

/-- Both cleared substitutions are integral and commute with coefficient maps. -/
theorem quarticClearU_map {R S : Type*} [CommRing R] [CommRing S]
    (θ : R →+* S) (u v z : R) :
    (fun i => MvPolynomial.map θ (quarticClearU u v z i)) =
      quarticClearU (θ u) (θ v) (θ z) := by
  funext i
  fin_cases i <;> simp [quarticClearU]

theorem quarticClearV_map {R S : Type*} [CommRing R] [CommRing S]
    (θ : R →+* S) (u v z : R) :
    (fun i => MvPolynomial.map θ (quarticClearV u v z i)) =
      quarticClearV (θ u) (θ v) (θ z) := by
  funext i
  fin_cases i <;> simp [quarticClearV]

include K

/-- The actual module-valued quartic kernel has global binary-polynomial
coefficients. No localization membership is assumed: it is proved by the
explicit two inverse matrices. -/
theorem quartic_kernel_descends
    (u v : B) (Z : End B (Fin 3 → B)) (Z' : End F (Fin 3 → F))
    (hZ : Z ^ 3 = (u ^ 3 + v ^ 3) • 1)
    (hZ' : Z' ^ 3 = (algebraMap B F (u ^ 3 + v ^ 3)) • 1)
    (hT : ∀ m, cyclicVectorBaseChange (algebraMap B F) (Z m) =
      Z' (cyclicVectorBaseChange (algebraMap B F) m))
    (hu : quarticU u v ≠ 0) (hv : quarticV u v ≠ 0)
    (hcop : IsRelPrime (quarticU u v) (quarticV u v)) :
    let := cyclicModuleStructure (u ^ 3 + v ^ 3) Z hZ
    ∀ {n : ℕ} (P : AuxTensor (R := CyclicCubicRing B (u ^ 3 + v ^ 3))
        (M := Fin 3 → B)), TensorHomogeneous n P →
      tensorDirectional (quarticRow
        (cyclicCoefficientHom (u ^ 3 + v ^ 3) u)
        (cyclicCoefficientHom (u ^ 3 + v ^ 3) v)
        (cyclicRoot (u ^ 3 + v ^ 3))) P = 0 →
      ∃ c : Fin (n + 1) → Fin 3 → B,
        kernelSynthesis (quarticKernelMatrixU
          (cyclicCoefficientHom (u ^ 3 + v ^ 3) u)
          (cyclicCoefficientHom (u ^ 3 + v ^ 3) v)
          (cyclicRoot (u ^ 3 + v ^ 3)) 0) n c = P := by
  dsimp only
  let G := u ^ 3 + v ^ 3
  let φ : B →+* F := algebraMap B F
  let R₀ := CyclicCubicRing B G
  let R₁ := CyclicCubicRing F (φ G)
  let := cyclicModuleStructure G Z hZ
  let := cyclicModuleStructure (φ G) Z' hZ'
  let θ : R₀ →+* R₁ := cyclicBaseChangeHom φ G
  let ψ : (Fin 3 → B) →ₛₗ[θ] (Fin 3 → F) :=
    cyclicModuleBaseChange φ G (cyclicVectorBaseChange φ) Z Z' hZ hZ' hT
  let u₀ : R₀ := cyclicCoefficientHom G u
  let v₀ : R₀ := cyclicCoefficientHom G v
  let z₀ : R₀ := cyclicRoot G
  let u₁ : R₁ := cyclicCoefficientHom (φ G) (φ u)
  let v₁ : R₁ := cyclicCoefficientHom (φ G) (φ v)
  let z₁ : R₁ := cyclicRoot (φ G)
  have hθu : θ u₀ = u₁ := cyclicBaseChangeHom_coefficient φ G u
  have hθv : θ v₀ = v₁ := cyclicBaseChangeHom_coefficient φ G v
  have hθz : θ z₀ = z₁ := cyclicBaseChangeHom_root φ G
  have hz : z₁ ^ 3 = u₁ ^ 3 + v₁ ^ 3 := by
    simpa only [u₁, v₁, z₁, G, map_add, map_pow] using cyclicRoot_cube (φ G)
  have hfu : quarticU u₁ v₁ = cyclicCoefficientHom (φ G) (φ (quarticU u v)) := by
    simp only [u₁, v₁, quarticU, map_mul, map_add, map_pow, map_ofNat]
  have hfv : quarticV u₁ v₁ = cyclicCoefficientHom (φ G) (φ (quarticV u v)) := by
    simp only [u₁, v₁, quarticV, map_mul, map_add, map_pow, map_ofNat, map_neg]
  let a := cyclicCoefficientHom (φ G) ((φ (quarticU u v))⁻¹)
  let b := cyclicCoefficientHom (φ G) ((φ (quarticV u v))⁻¹)
  have ha : quarticU u₁ v₁ * a = 1 := by
    rw [hfu, ← map_mul, mul_inv_cancel₀ (by
      simpa only [map_zero] using (IsFractionRing.injective B F).ne hu), map_one]
  have hb : quarticV u₁ v₁ * b = 1 := by
    rw [hfv, ← map_mul, mul_inv_cancel₀ (by
      simpa only [map_zero] using (IsFractionRing.injective B F).ne hv), map_one]
  let A := quarticKernelMatrixU u₁ v₁ z₁ a
  let A' := quarticKernelMatrixV u₁ v₁ z₁ b
  let D := quarticKernelInverseU u₁ v₁ z₁ a
  let D' := quarticKernelInverseV u₁ v₁ z₁ b
  have hAD : A * D = 1 := quarticKernelMatrixU_mul_inverse _ _ _ _ hz ha
  have hA'D' : A' * D' = 1 := quarticKernelMatrixV_mul_inverse _ _ _ _ hz hb
  intro n P hP hδ
  let P' := tensorBaseChange ψ P
  have hP' : TensorHomogeneous n P' := tensorBaseChange_homogeneous ψ hP
  have hδ' : tensorDirectional (quarticRow u₁ v₁ z₁) P' = 0 := by
    have hd := congrArg (tensorBaseChange ψ) hδ
    rw [tensorBaseChange_directional, map_zero] at hd
    have hr : (fun i => θ (quarticRow u₀ v₀ z₀ i)) = quarticRow u₁ v₁ z₁ := by
      funext i
      fin_cases i <;> simp [quarticRow, quarticU, quarticV, quarticZ,
        map_ofNat, hθu, hθv, hθz]
    rw [hr] at hd
    exact hd
  obtain ⟨c, hc, huniq⟩ :=
    (tensor_directional_finite_kernel (K := K) _ A D hAD
      (mul_eq_one_comm.mp hAD)
      (quarticKernelMatrixU_direction _ _ _ _ hz ha) P' hP').mp hδ'
  have hcU : kernelCoordinates D P' = binarySynthesis n c := by
    rw [← hc, ← kernelEmbedding_synthesis, kernelCoordinates_embedding _ _ hAD]
  have hcV : kernelCoordinates D' P' = binarySynthesis n c := by
    rw [← hc, quarticKernelSynthesis_charts _ _ _ _ b,
      ← kernelEmbedding_synthesis, kernelCoordinates_embedding _ _ hA'D']
  let CU := (aeval (quarticClearU u₀ v₀ z₀)).toLinearMap.rTensor (Fin 3 → B) P
  let CV := (aeval (quarticClearV u₀ v₀ z₀)).toLinearMap.rTensor (Fin 3 → B) P
  have hCU : tensorBaseChange ψ CU =
      (aeval (quarticClearU u₁ v₁ z₁)).toLinearMap.rTensor (Fin 3 → F) P' := by
    rw [tensorBaseChange_substitution, quarticClearU_map, hθu, hθv, hθz]
  have hCV : tensorBaseChange ψ CV =
      (aeval (quarticClearV u₁ v₁ z₁)).toLinearMap.rTensor (Fin 3 → F) P' := by
    rw [tensorBaseChange_substitution, quarticClearV_map, hθu, hθv, hθz]
  have hclearU := quarticCoordinatesU_clear u₁ v₁ z₁ a ha P' hP'
  have hclearV := quarticCoordinatesV_clear u₁ v₁ z₁ b hb P' hP'
  rw [hcU, ← hCU] at hclearU
  rw [hcV, ← hCV] at hclearV
  have huInt (j : Fin (n + 1)) (i : Fin 3) :
      IsLocalization.IsInteger B (φ (quarticU u v ^ n) * c j i) := by
    have h := congrArg (fun Q : BinaryTensor (R := R₁) (M := Fin 3 → F) =>
      binaryCoefficients n Q j) hclearU
    have hs (r : R₁) (Q : BinaryTensor (R := R₁) (M := Fin 3 → F)) :
        binaryCoefficients n (r • Q) j = r • binaryCoefficients n Q j := by
      simp only [binaryCoefficients, LinearEquiv.map_smul, Finsupp.smul_apply]
    rw [hs, binaryCoefficients_synthesis, binaryCoefficients_baseChange,
      hfu, ← map_pow, ← map_pow, cyclicModule_coefficient_smul] at h
    have hi := congrFun h i
    exact ⟨binaryCoefficients n CU j i, hi.symm⟩
  have hvInt (j : Fin (n + 1)) (i : Fin 3) :
      IsLocalization.IsInteger B (φ (quarticV u v ^ n) * c j i) := by
    have h := congrArg (fun Q : BinaryTensor (R := R₁) (M := Fin 3 → F) =>
      binaryCoefficients n Q j) hclearV
    have hs (r : R₁) (Q : BinaryTensor (R := R₁) (M := Fin 3 → F)) :
        binaryCoefficients n (r • Q) j = r • binaryCoefficients n Q j := by
      simp only [binaryCoefficients, LinearEquiv.map_smul, Finsupp.smul_apply]
    rw [hs, binaryCoefficients_synthesis, binaryCoefficients_baseChange,
      hfv, ← map_pow, ← map_pow, cyclicModule_coefficient_smul] at h
    have hi := congrFun h i
    exact ⟨binaryCoefficients n CV j i, hi.symm⟩
  obtain ⟨d, hd⟩ := ChoppedPlane.free_coefficients_coprime_descent
    (fun ji : Fin (n + 1) × Fin 3 => c ji.1 ji.2)
    (quarticU u v) (quarticV u v) hcop
    (fun ji => ⟨⟨n, huInt ji.1 ji.2⟩, ⟨n, hvInt ji.1 ji.2⟩⟩)
  let c₀ : Fin (n + 1) → Fin 3 → B := fun j i => d (j, i)
  have hψc (j : Fin (n + 1)) : ψ (c₀ j) = c j := by
    funext i
    exact hd (j, i)
  refine ⟨c₀, ?_⟩
  apply tensorBaseChange_injective ψ (by
    intro m m' hm
    funext i
    apply IsFractionRing.injective B F
    exact congrFun hm i)
  rw [tensorBaseChange_kernelSynthesis]
  have hmatrix : (quarticKernelMatrixU u₀ v₀ z₀ 0).map θ =
      quarticKernelMatrixU u₁ v₁ z₁ 0 := by
    ext i j
    change θ (quarticKernelMatrixU u₀ v₀ z₀ 0 i j) = _
    fin_cases i <;> fin_cases j <;>
      simp [quarticKernelMatrixU, quadraticOne, quadraticTwo, hθu, hθv, hθz]
  rw [hmatrix]
  simp only [hψc]
  rw [quarticKernelSynthesis_lift _ _ _ 0 a]
  exact hc

end ChoppedPlane.QWeyl
