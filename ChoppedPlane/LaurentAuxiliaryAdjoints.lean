module

public import ChoppedPlane.LaurentResidueOperators
public import ChoppedPlane.PolynomialOperatorDuality
public import ChoppedPlane.FiniteAuxiliaryMaps

@[expose] public section

/-!
Actual finite coefficient flattening for auxiliary symmetric powers of Laurent
modules, and the factorial transpose identity for their three coefficient
operators. The equivalences preserve every coefficient and every grade.
-/
noncomputable section
namespace ChoppedPlane.LaurentPairing
open Module MvPolynomial SymmetricDerivative
open scoped Classical
variable {K : Type*} [Field K] {J S : Type*}

/-- Reorder one component, one auxiliary monomial, and two Laurent exponents. -/
def auxiliaryLaurentIndexEquiv : ((J × S) × (ℤ × ℤ)) ≃ (S × (J × (ℤ × ℤ))) where
  toFun e := (e.1.2, (e.1.1,e.2))
  invFun e := ((e.2.1,e.1),e.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual free Laurent coefficient flattening, with finite auxiliary index. -/
def splitFreeLaurentEquiv [Finite S] :
    FreeLaurent K (J × S) ≃ₗ[K] (S → FreeLaurent K J) :=
  (Finsupp.domLCongr auxiliaryLaurentIndexEquiv).trans
    ((Finsupp.curryLinearEquiv K).trans (Finsupp.linearEquivFunOnFinite K _ S))

@[simp] theorem splitFreeLaurentEquiv_apply [Finite S]
    (p : FreeLaurent K (J × S)) (s : S) (e : J × (ℤ × ℤ)) :
    splitFreeLaurentEquiv p s e = p ((e.1,s),e.2) := rfl

@[simp] theorem splitFreeLaurentEquiv_symm_apply [Finite S]
    (p : S → FreeLaurent K J) (e : (J × S) × (ℤ × ℤ)) :
    splitFreeLaurentEquiv.symm p e = p e.1.2 (e.1.1,e.2) := rfl

/-- Positive grade flattening is an actual linear equivalence. -/
def positiveGradeSplit [Finite S] (g : J → ℤ) (r : ℤ) :
    positiveGrade (K := K) (fun i : J × S => g i.1) r ≃ₗ[K]
      (S → positiveGrade (K := K) g r) where
  toFun p s := ⟨splitFreeLaurentEquiv p.val s, by
    apply (Finsupp.mem_supported' K _).mpr
    intro e he
    exact (Finsupp.mem_supported' K p.val).mp p.property ((e.1,s),e.2) he⟩
  invFun p := ⟨splitFreeLaurentEquiv.symm (fun s => (p s).val), by
    apply (Finsupp.mem_supported' K _).mpr
    intro e he
    exact (Finsupp.mem_supported' K (p e.1.2).val).mp (p e.1.2).property (e.1.1,e.2) he⟩
  left_inv p := Subtype.ext (splitFreeLaurentEquiv.symm_apply_apply p.val)
  right_inv p := by
    funext s
    apply Subtype.ext
    exact congrFun (splitFreeLaurentEquiv.apply_symm_apply (fun s => (p s).val)) s
  map_add' p q := by
    funext s
    apply Subtype.ext
    exact congrFun (map_add splitFreeLaurentEquiv p.val q.val) s
  map_smul' c p := by
    funext s
    apply Subtype.ext
    exact congrFun (map_smul splitFreeLaurentEquiv c p.val) s

@[simp] theorem positiveGradeSplit_apply [Finite S] (g : J → ℤ) (r : ℤ)
    (p : positiveGrade (K := K) (fun i : J × S => g i.1) r)
    (s : S) (e : J × (ℤ × ℤ)) :
    (positiveGradeSplit g r p s).val e = p.val ((e.1,s),e.2) := rfl

/-- The top Laurent grade has the same actual finite auxiliary flattening. -/
def negativeGradeSplit [Finite S] (g : J → ℤ) (r : ℤ) :
    negativeGrade (K := K) (fun i : J × S => g i.1) r ≃ₗ[K]
      (S → negativeGrade (K := K) g r) where
  toFun p s := ⟨splitFreeLaurentEquiv p.val s, by
    apply (Finsupp.mem_supported' K _).mpr
    intro e he
    exact (Finsupp.mem_supported' K p.val).mp p.property ((e.1,s),e.2) he⟩
  invFun p := ⟨splitFreeLaurentEquiv.symm (fun s => (p s).val), by
    apply (Finsupp.mem_supported' K _).mpr
    intro e he
    exact (Finsupp.mem_supported' K (p e.1.2).val).mp (p e.1.2).property (e.1.1,e.2) he⟩
  left_inv p := Subtype.ext (splitFreeLaurentEquiv.symm_apply_apply p.val)
  right_inv p := by
    funext s
    apply Subtype.ext
    exact congrFun (splitFreeLaurentEquiv.apply_symm_apply (fun s => (p s).val)) s
  map_add' p q := by
    funext s
    apply Subtype.ext
    exact congrFun (map_add splitFreeLaurentEquiv p.val q.val) s
  map_smul' c p := by
    funext s
    apply Subtype.ext
    exact congrFun (map_smul splitFreeLaurentEquiv c p.val) s

@[simp] theorem negativeGradeSplit_apply [Finite S] (g : J → ℤ) (r : ℤ)
    (p : negativeGrade (K := K) (fun i : J × S => g i.1) r)
    (s : S) (e : J × (ℤ × ℤ)) :
    (negativeGradeSplit g r p s).val e = p.val ((e.1,s),e.2) := rfl

/-- Flattening commutes with the actual componentwise Laurent polynomial map. -/
@[simp] theorem freeLaurentEquiv_split [Finite J] [Finite S]
    (p : FreeLaurent K (J × S)) (j : J) (s : S) :
    freeLaurentEquiv p (j,s) = freeLaurentEquiv (splitFreeLaurentEquiv p s) j := by
  ext e
  rfl

/-- A constant-one coefficient weight is the original perfect residue pairing. -/
theorem weightedResiduePair_one [Finite J] (g : J → ℤ) (r : ℤ)
    (q : negativeGrade (K := K) g r) (p : positiveGrade (K := K) g r) :
    weightedResiduePair g r (fun _ => 1) (fun _ => one_ne_zero) q p =
      residuePair g r q p := by
  have h : weightedResiduePair g r (fun _ => 1) (fun _ => one_ne_zero) q =
      residuePair g r q := by
    apply (positiveBasis g r).ext
    intro e
    simp only [weightedResiduePair_basis, residuePair_basis, one_mul]
  exact LinearMap.congr_fun h p

/-- The unweighted perfect pairing is the literal product residue. -/
theorem residuePair_eq_vectorResidue [Finite J] (g : J → ℤ) (r : ℤ)
    (q : negativeGrade (K := K) g r) (p : positiveGrade (K := K) g r) :
    residuePair g r q p = vectorResidueFunctional (fun _ => 1)
      (freeLaurentEquiv q.val) (freeLaurentEquiv p.val) := by
  rw [← weightedResiduePair_one]
  exact weightedResiduePair_eq_vectorResidue _ _ _ _ _ _

variable {V W V' W' : Type*}
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']

/-- The literal finite auxiliary variable multiplication with coefficient
operators `L i`, using actual monomial multiplication coefficients. -/
def auxiliaryOperatorMultiply (L : Fin 3 → W' →ₗ[K] V') (t : ℕ) :
    (Sym (Fin 3) t → W') →ₗ[K] (Sym (Fin 3) (t + 1) → V') :=
  LinearMap.pi fun b => ∑ s : Sym (Fin 3) t, ∑ i : Fin 3,
    (X i * monomial (homogeneousTensorExponent t s) 1 : Poly K 3).coeff
      (homogeneousTensorExponent (t + 1) b) • (L i).comp (LinearMap.proj s)

@[simp] theorem auxiliaryOperatorMultiply_apply (L : Fin 3 → W' →ₗ[K] V') (t : ℕ)
    (q : Sym (Fin 3) t → W') (b : Sym (Fin 3) (t + 1)) :
    auxiliaryOperatorMultiply L t q b = ∑ s : Sym (Fin 3) t, ∑ i : Fin 3,
      (X i * monomial (homogeneousTensorExponent t s) 1 : Poly K 3).coeff
        (homogeneousTensorExponent (t + 1) b) • L i (q s) := by
  simp only [auxiliaryOperatorMultiply, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- The actual factorial sum pairing on finite auxiliary coefficient vectors. -/
def auxiliaryCoefficientPair (β : W' →ₗ[K] W →ₗ[K] K) (t : ℕ)
    (q : Sym (Fin 3) t → W') (p : Sym (Fin 3) t → W) : K :=
  ∑ s : Sym (Fin 3) t, factorialWeight K (homogeneousTensorExponent t s) * β (q s) (p s)

/-- The perfect pairing on flattened coefficients equals the actual sum of
base residue pairings with their auxiliary factorial weights. -/
theorem auxiliaryResiduePair_eq_coefficientPair [Finite J] [CharZero K]
    (g : J → ℤ) (r : ℤ) (t : ℕ)
    (q : negativeGrade (K := K) (auxiliaryGeneratorWeights g t) r)
    (p : positiveGrade (K := K) (auxiliaryGeneratorWeights g t) r) :
    auxiliaryResiduePair g r t q p =
      auxiliaryCoefficientPair (residuePair g r) t
        (negativeGradeSplit g r q) (positiveGradeSplit g r p) := by
  classical
  letI := Fintype.ofFinite J
  change weightedResiduePair _ _ _ _ q p = _
  rw [weightedResiduePair_eq_vectorResidue, vectorResidueFunctional_apply]
  unfold auxiliaryCoefficientPair
  simp only [residuePair_eq_vectorResidue, vectorResidueFunctional_apply, one_mul,
    Finset.mul_sum]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro j hj
  change factorialWeight K (homogeneousTensorExponent t s) *
      (freeLaurentEquiv q.val (j,s) * freeLaurentEquiv p.val (j,s)).coeff (-1,-1) = _
  rw [freeLaurentEquiv_split, freeLaurentEquiv_split]
  rfl

/-- Auxiliary differentiation and multiplication are adjoint whenever their
actual three coefficient operators are adjoint. The proof uses literal
partial-derivative and variable-multiplication matrix coefficients. -/
theorem auxiliaryCoefficientPair_adjoint
    (α : V' →ₗ[K] V →ₗ[K] K) (β : W' →ₗ[K] W →ₗ[K] K)
    (T : Fin 3 → V →ₗ[K] W) (L : Fin 3 → W' →ₗ[K] V')
    (h : ∀ i q p, β q (T i p) = α (L i q) p) (t : ℕ)
    (q : Sym (Fin 3) t → W') (p : Sym (Fin 3) (t + 1) → V) :
    auxiliaryCoefficientPair β t q (operatorDifferential T t p) =
      auxiliaryCoefficientPair α (t + 1) (auxiliaryOperatorMultiply L t q) p := by
  unfold auxiliaryCoefficientPair
  simp only [operatorDifferential_coeff, auxiliaryOperatorMultiply_apply,
    map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro i hi
  rw [h]
  calc
    _ = (factorialWeight K (homogeneousTensorExponent t s) *
        (pderiv i (monomial (homogeneousTensorExponent (t + 1) b) 1 : Poly K 3)).coeff
          (homogeneousTensorExponent t s)) * α (L i (q s)) (p b) := by ring
    _ = (factorialWeight K (homogeneousTensorExponent (t + 1) b) *
        (X i * monomial (homogeneousTensorExponent t s) 1 : Poly K 3).coeff
          (homogeneousTensorExponent (t + 1) b)) * α (L i (q s)) (p b) := by
      rw [factorialWeight_pderiv_monomial_pair]
    _ = _ := by ring

end ChoppedPlane.LaurentPairing
