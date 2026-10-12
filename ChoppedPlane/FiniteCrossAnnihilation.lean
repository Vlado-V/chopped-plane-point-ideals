module

public import ChoppedPlane.FiniteAuxiliaryMaps

@[expose] public section

/-! The cross substitution is annihilated by the directional derivative,
over an arbitrary commutative ring and with arbitrary module coefficients. -/

noncomputable section
namespace ChoppedPlane.FiniteCech

open MvPolynomial SymmetricDerivative
open scoped TensorProduct

variable {R : Type*} [CommRing R]

theorem directional_linearChange_zero (f : Fin 3 → R)
    (A : Matrix (Fin 3) (Fin 3) R)
    (hA : ∀ i, ∑ j, f j * A i j = 0) (P : Aux R) :
    directional f (linearChange A P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
    simp [map_mul, Derivation.leibniz, hP, directional_linearForm, hA]

theorem directional_cross_zero (u v z : R) (P : Aux R) :
    directional ![u,v,z] (linearChange (crossMatrix u v z) P) = 0 := by
  apply directional_linearChange_zero
  intro i
  fin_cases i <;> simp [crossMatrix, Fin.sum_univ_three] <;> ring

theorem linearChange_cross_linearForm_zero (u v z : R) :
    linearChange (crossMatrix u v z) (linearForm ![u,v,z]) = 0 := by
  rw [linearChange_linearForm]
  have h : (fun k => ∑ j, ![u,v,z] j * crossMatrix u v z j k) = 0 := by
    funext k
    fin_cases k <;> simp [crossMatrix, Fin.sum_univ_three] <;> ring
  rw [h]
  simp [linearForm]

variable {M : Type*} [AddCommGroup M] [Module R M]

theorem tensorDirectional_cross_zero (u v z : R)
    (P : AuxTensor (R := R) (M := M)) :
    tensorDirectional ![u,v,z] (tensorChange (crossMatrix u v z) P) = 0 := by
  induction P using TensorProduct.inductionOn with
  | tmul Q m =>
    simp [tensorDirectional, tensorChange, LinearMap.rTensor_tmul, directional_cross_zero]
  | add P Q hP hQ => simp [hP, hQ]

theorem finiteDirectional_cross_zero (u v z : R) (n : ℕ)
    (c : Sym (Fin 3) (n + 1) → M) :
    finiteDirectional ![u,v,z] n (finiteCross (crossMatrix u v z) (n + 1) c) = 0 := by
  change homogeneousTensorCoefficientVector n
    (tensorDirectional ![u,v,z]
      (homogeneousTensorSynthesis (n + 1)
        (finiteCross (crossMatrix u v z) (n + 1) c))) = 0
  rw [synthesis_finiteCross, tensorDirectional_cross_zero]
  exact (homogeneousTensorCoefficientMap n).map_zero

theorem tensorChange_cross_multiply_zero (u v z : R)
    (P : AuxTensor (R := R) (M := M)) :
    tensorChange (crossMatrix u v z) (tensorMultiplyLinear ![u,v,z] P) = 0 := by
  induction P using TensorProduct.inductionOn with
  | tmul Q m =>
    simp [tensorChange, tensorMultiplyLinear, LinearMap.rTensor_tmul,
      linearChange_cross_linearForm_zero]
  | add P Q hP hQ => simp [hP, hQ]

theorem finiteCross_multiply_zero (u v z : R) (n : ℕ)
    (c : Sym (Fin 3) n → M) :
    finiteCross (crossMatrix u v z) (n + 1) (finiteMultiply ![u,v,z] n c) = 0 := by
  change homogeneousTensorCoefficientVector (n + 1)
    (tensorChange (crossMatrix u v z)
      (homogeneousTensorSynthesis (n + 1) (finiteMultiply ![u,v,z] n c))) = 0
  rw [synthesis_finiteMultiply, tensorChange_cross_multiply_zero]
  exact (homogeneousTensorCoefficientMap (n + 1)).map_zero

end ChoppedPlane.FiniteCech
