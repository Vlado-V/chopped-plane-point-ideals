module

public import ChoppedPlane.Points
public import ChoppedPlane.Multiplication

@[expose] public section

/-!
# Propagation beyond the interpolation degree

The lemmas use the actual homogeneous pieces and actual polynomial ideals.
Surjectivity of evaluation in degree `q - 1` supplies a recurrence for the
point ideal in every degree at least `q`. Equality with a subideal in degree
`q` then propagates to all later degrees.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K : Type*} [Field K]

/-- The ambient homogeneous degree piece of an actual polynomial ideal. -/
def idealDegreeSpace {n : ℕ} (I : Ideal (Poly K n)) (d : ℕ) :
    Submodule K (Poly K n) := Forms K n d ⊓ I.restrictScalars K

@[simp] theorem mem_idealDegreeSpace {n d : ℕ} (I : Ideal (Poly K n)) (f : Poly K n) :
    f ∈ idealDegreeSpace I d ↔ f.IsHomogeneous d ∧ f ∈ I := Iff.rfl

/-- Multiplication preserves ideal membership and adds homogeneous degrees. -/
theorem idealDegreeSpace_mul_forms_le {n d e : ℕ} (I : Ideal (Poly K n)) :
    idealDegreeSpace I d * Forms K n e ≤ idealDegreeSpace I (d + e) := by
  apply Submodule.mul_le.mpr
  intro f hf g hg
  exact ⟨hf.1.mul hg, Ideal.mul_mem_right _ _ hf.2⟩

/-- An actual ideal contains every product with its underlying submodule. -/
theorem forms_mul_ideal_le {n d : ℕ} (I : Ideal (Poly K n)) :
    Forms K n d * I.restrictScalars K ≤ I.restrictScalars K := by
  apply Submodule.mul_le.mpr
  intro f hf g hg
  exact Ideal.mul_mem_left _ _ hg

/-- A recurrence by degree-one multiplication propagates containment in an
actual subideal. The recurrence is an explicit helper hypothesis. -/
theorem idealDegreeSpace_le_of_recurrence {n q : ℕ}
    (I J : Ideal (Poly K n))
    (hbase : idealDegreeSpace I q ≤ J.restrictScalars K)
    (hrec : ∀ d, q ≤ d → idealDegreeSpace I (d + 1) ≤
      Forms K n 1 * idealDegreeSpace I d) :
    ∀ d, q ≤ d → idealDegreeSpace I d ≤ J.restrictScalars K := by
  intro d hd
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd
  induction e with
  | zero => simpa using hbase
  | succ e ih =>
    apply (hrec (q + e) (by omega)).trans
    have hprod : Forms K n 1 * idealDegreeSpace I (q + e) ≤
        Forms K n 1 * J.restrictScalars K := by
      apply Submodule.mul_le.mpr
      intro f hf g hg
      exact Submodule.mul_mem_mul hf (ih (by omega) hg)
    exact hprod.trans (forms_mul_ideal_le J)

/-- Equality of actual homogeneous ideal pieces propagates under the stated
recurrence. -/
theorem idealDegreeSpace_eq_of_recurrence {n q : ℕ}
    (I J : Ideal (Poly K n)) (hJI : J ≤ I)
    (hbase : idealDegreeSpace I q = idealDegreeSpace J q)
    (hrec : ∀ d, q ≤ d → idealDegreeSpace I (d + 1) ≤
      Forms K n 1 * idealDegreeSpace I d) :
    ∀ d, q ≤ d → idealDegreeSpace I d = idealDegreeSpace J d := by
  intro d hd
  apply le_antisymm
  · exact le_inf inf_le_left
      (idealDegreeSpace_le_of_recurrence I J
        (hbase ▸ inf_le_right) hrec d hd)
  · exact inf_le_inf_left _ hJI

/-- The kernel-defined point piece equals the homogeneous piece of the actual
vanishing ideal. -/
theorem pointDegreeSpace_eq_idealDegreeSpace {p d : ℕ} (a : PointCoordinates K p) :
    pointDegreeSpace K a d = idealDegreeSpace (pointIdeal K a) d := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, (homogeneous_mem_pointIdeal_iff a g).mpr hg⟩
  · intro hf
    exact ⟨⟨f, hf.1⟩, (homogeneous_mem_pointIdeal_iff a ⟨f, hf.1⟩).mp hf.2, rfl⟩

/-- Multiplication by powers of `z`, which evaluates to one on the chosen
chart, propagates surjectivity of point evaluation. -/
theorem pointEvaluation_surjective_add {p d : ℕ} (a : PointCoordinates K p)
    (hsurj : Function.Surjective (pointEvaluation K a d)) (e : ℕ) :
    Function.Surjective (pointEvaluation K a (d + e)) := by
  intro v
  obtain ⟨f, hf⟩ := hsurj v
  refine ⟨⟨f.val * X 2 ^ e, f.property.mul (isHomogeneous_X_pow 2 e)⟩, ?_⟩
  ext i
  simpa [pointEvaluation_apply, chartPoint, map_mul] using congrFun hf i

/-- Surjectivity of point evaluation persists at every later degree. -/
theorem pointEvaluation_surjective_of_le {p d t : ℕ} (a : PointCoordinates K p)
    (hsurj : Function.Surjective (pointEvaluation K a d)) (hdt : d ≤ t) :
    Function.Surjective (pointEvaluation K a t) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hdt
  exact pointEvaluation_surjective_add a hsurj e

/-- The three coordinate forms. -/
def coordinateForms : Fin 3 → Forms K 3 1 :=
  fun i => ⟨X i, isHomogeneous_X K i⟩

@[simp] theorem coordinateForms_val (i : Fin 3) :
    (coordinateForms (K := K) i).val = X i := rfl

/-- Every ternary form of positive degree is a sum of its coordinates times
forms of one lower degree. -/
theorem exists_coordinate_decomposition (d : ℕ) (f : Forms K 3 (d + 1)) :
    ∃ b : Fin 3 → Forms K 3 d, f.val = ∑ i, X i * (b i).val := by
  have hgen : generatorSpace (coordinateForms (K := K)) = Forms K 3 1 := by
    simpa [generatorSpace, coordinateForms] using
      (homogeneousSubmodule_one_eq_span_X (σ := Fin 3) (R := K)).symm
  have hmem : f.val ∈ LinearMap.range ((Forms K 3 (1 + d)).subtype.comp
      (multiplication (e := d) (coordinateForms (K := K)))) := by
    rw [range_ambient_multiplication, hgen, forms_mul_forms]
    simp [Nat.add_comm]
  obtain ⟨b, hb⟩ := hmem
  refine ⟨b, ?_⟩
  rw [LinearMap.comp_apply] at hb
  change (multiplication (e := d) (coordinateForms (K := K)) b).val = f.val at hb
  rw [multiplication_val] at hb
  simpa using hb.symm

@[simp] theorem mem_pointDegreeSpace {p d : ℕ} (a : PointCoordinates K p)
    (f : Poly K 3) :
    f ∈ pointDegreeSpace K a d ↔ f.IsHomogeneous d ∧
      ∀ i, eval (chartPoint K a i) f = 0 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.property, (mem_pointDegreePiece a g).mp hg⟩
  · rintro ⟨hf, heval⟩
    exact ⟨⟨f, hf⟩, (mem_pointDegreePiece a ⟨f, hf⟩).mpr heval, rfl⟩

/-- Interpolation one degree below the equations forces generation of the
next homogeneous piece by multiplication by the coordinates. -/
theorem pointDegreeSpace_succ_eq {p t : ℕ} (a : PointCoordinates K p)
    (hsurj : Function.Surjective (pointEvaluation K a t)) :
    pointDegreeSpace K a (t + 2) =
      Forms K 3 1 * pointDegreeSpace K a (t + 1) := by
  apply le_antisymm
  · intro f hf
    obtain ⟨hfhom, hfeval⟩ := (mem_pointDegreeSpace a f).mp hf
    obtain ⟨b, hb⟩ := exists_coordinate_decomposition (t + 1) ⟨f, hfhom⟩
    change f = ∑ i, X i * (b i).val at hb
    obtain ⟨g₀, hg₀⟩ := hsurj (pointEvaluation K a (t + 1) (b 0))
    obtain ⟨g₁, hg₁⟩ := hsurj (pointEvaluation K a (t + 1) (b 1))
    let c₀ : Poly K 3 := (b 0).val - X 2 * g₀.val
    let c₁ : Poly K 3 := (b 1).val - X 2 * g₁.val
    let c₂ : Poly K 3 := (b 2).val + X 0 * g₀.val + X 1 * g₁.val
    have he₀ (i : Fin p) : eval (chartPoint K a i) g₀.val =
        eval (chartPoint K a i) (b 0).val := congrFun hg₀ i
    have he₁ (i : Fin p) : eval (chartPoint K a i) g₁.val =
        eval (chartPoint K a i) (b 1).val := congrFun hg₁ i
    have hc₀ : c₀ ∈ pointDegreeSpace K a (t + 1) := by
      apply (mem_pointDegreeSpace a c₀).mpr
      constructor
      · exact (b 0).property.sub (by simpa [Nat.add_comm] using
          (isHomogeneous_X K (2 : Fin 3)).mul g₀.property)
      · intro i
        simp only [c₀, map_sub, map_mul, eval_X]
        rw [show chartPoint K a i 2 = 1 by simp [chartPoint], one_mul, he₀ i, sub_self]
    have hc₁ : c₁ ∈ pointDegreeSpace K a (t + 1) := by
      apply (mem_pointDegreeSpace a c₁).mpr
      constructor
      · exact (b 1).property.sub (by simpa [Nat.add_comm] using
          (isHomogeneous_X K (2 : Fin 3)).mul g₁.property)
      · intro i
        simp only [c₁, map_sub, map_mul, eval_X]
        rw [show chartPoint K a i 2 = 1 by simp [chartPoint], one_mul, he₁ i, sub_self]
    have hc₂ : c₂ ∈ pointDegreeSpace K a (t + 1) := by
      apply (mem_pointDegreeSpace a c₂).mpr
      constructor
      · exact ((b 2).property.add (by simpa [Nat.add_comm] using
          (isHomogeneous_X K (0 : Fin 3)).mul g₀.property)).add
          (by simpa [Nat.add_comm] using
          (isHomogeneous_X K (1 : Fin 3)).mul g₁.property)
      · intro i
        have h := hfeval i
        rw [hb, Fin.sum_univ_three] at h
        simp only [map_add, map_mul, eval_X] at h
        simp only [c₂, map_add, map_mul, eval_X, he₀ i, he₁ i]
        simp [chartPoint] at h ⊢
        linear_combination h
    have hid : f = X 0 * c₀ + X 1 * c₁ + X 2 * c₂ := by
      rw [hb, Fin.sum_univ_three]
      dsimp [c₀, c₁, c₂]
      ring
    rw [hid]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.mul_mem_mul (isHomogeneous_X K 0) hc₀
      · exact Submodule.mul_mem_mul (isHomogeneous_X K 1) hc₁
    · exact Submodule.mul_mem_mul (isHomogeneous_X K 2) hc₂
  · rw [pointDegreeSpace_eq_idealDegreeSpace, pointDegreeSpace_eq_idealDegreeSpace,
      mul_comm]
    simpa [Nat.add_assoc] using
      idealDegreeSpace_mul_forms_le (d := t + 1) (e := 1) (pointIdeal K a)

/-- The interpolation hypothesis gives the genuine ideal recurrence at every
subsequent degree. -/
theorem pointDegreeSpace_recurrence {p q : ℕ} (a : PointCoordinates K p)
    (hq : 1 ≤ q)
    (hsurj : Function.Surjective (pointEvaluation K a (q - 1)))
    (d : ℕ) (hqd : q ≤ d) :
    pointDegreeSpace K a (d + 1) = Forms K 3 1 * pointDegreeSpace K a d := by
  have hd : 1 ≤ d := hq.trans hqd
  have hs := pointEvaluation_surjective_of_le a hsurj
    (show q - 1 ≤ d - 1 by omega)
  have hh := pointDegreeSpace_succ_eq a hs
  simpa [show d - 1 + 1 = d by omega, show d - 1 + 2 = d + 1 by omega] using hh

/-- Interpolation and equality in degree `q` suffice to propagate equality
with any actual subideal in all higher degrees. -/
theorem pointDegreeSpace_eq_of_degree_eq {p q : ℕ} (a : PointCoordinates K p)
    (hq : 1 ≤ q)
    (hsurj : Function.Surjective (pointEvaluation K a (q - 1)))
    (J : Ideal (Poly K 3)) (hJI : J ≤ pointIdeal K a)
    (hbase : pointDegreeSpace K a q = idealDegreeSpace J q) :
    ∀ d, q ≤ d → pointDegreeSpace K a d = idealDegreeSpace J d := by
  have hrec : ∀ d, q ≤ d → idealDegreeSpace (pointIdeal K a) (d + 1) ≤
      Forms K 3 1 * idealDegreeSpace (pointIdeal K a) d := by
    intro d hd
    rw [← pointDegreeSpace_eq_idealDegreeSpace, ← pointDegreeSpace_eq_idealDegreeSpace]
    exact (pointDegreeSpace_recurrence a hq hsurj d hd).le
  intro d hd
  rw [pointDegreeSpace_eq_idealDegreeSpace]
  exact idealDegreeSpace_eq_of_recurrence (pointIdeal K a) J hJI
    (by rwa [← pointDegreeSpace_eq_idealDegreeSpace]) hrec d hd

end ChoppedPlane
