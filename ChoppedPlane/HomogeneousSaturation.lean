module

public import ChoppedPlane.Dehomogeneous
public import Mathlib

@[expose] public section

/-!
# Dehomogenization of homogeneous saturated ideals

A homogeneous polynomial belongs to a homogeneous ideal saturated by the last
coordinate exactly when its dehomogenization belongs to the corresponding
affine ideal. The key argument compares homogeneous components, using the
coordinate's regularity to descend from the finite highest component.
-/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module
variable {K σ : Type*} [Field K]

/-- Multiplication by a degree-one form shifts homogeneous components. -/
theorem homogeneousComponent_mul_degree_one_succ
    {z : MvPolynomial σ K} (hz : z.IsHomogeneous 1)
    (n : ℕ) (g : MvPolynomial σ K) :
    homogeneousComponent (n + 1) (z * g) = z * homogeneousComponent n g := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial d c =>
    have hg : (monomial d c : MvPolynomial σ K).IsHomogeneous d.degree :=
      isHomogeneous_monomial c rfl
    have hzg := hz.mul hg
    simp only [homogeneousComponent_of_mem hzg, homogeneousComponent_of_mem hg]
    have heq : (n + 1 = 1 + d.degree) ↔ (n = d.degree) := by omega
    simp only [heq, mul_ite, mul_zero]
  | add g h hg hh =>
    simp only [mul_add, map_add, hg, hh]

/-- A degree-one form contributes no degree-zero component to a product. -/
theorem homogeneousComponent_mul_degree_one_zero
    {z : MvPolynomial σ K} (hz : z.IsHomogeneous 1)
    (g : MvPolynomial σ K) : homogeneousComponent 0 (z * g) = 0 := by
  classical
  induction g using MvPolynomial.induction_on' with
  | monomial d c =>
    have hg : (monomial d c : MvPolynomial σ K).IsHomogeneous d.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (m := 0) (hz.mul hg)]
    simp [show 0 ≠ 1 + d.degree by omega]
  | add g h hg hh =>
    simp only [mul_add, map_add, hg, hh, add_zero]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous element cannot become zero after setting a regular
degree-one element equal to one in a homogeneous quotient. -/
theorem homogeneous_mem_of_sub_coordinate_one_mul
    (I : Ideal (MvPolynomial σ K))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ K))
    {z : MvPolynomial σ K} (hz : z.IsHomogeneous 1)
    (hsat : ∀ p, z * p ∈ I → p ∈ I)
    {t : ℕ} {f : MvPolynomial σ K} (hf : f.IsHomogeneous t)
    (g : MvPolynomial σ K) (hh : f - (z - 1) * g ∈ I) : f ∈ I := by
  have hbase : homogeneousComponent 0 g + homogeneousComponent 0 f ∈ I := by
    have h := homogeneousComponent_mem_of_mem hI hh 0
    rw [sub_mul, one_mul, map_sub, map_sub,
      homogeneousComponent_mul_degree_one_zero hz] at h
    convert h using 1
    ring
  have hrec (n : ℕ) : homogeneousComponent (n + 1) g -
      z * homogeneousComponent n g + homogeneousComponent (n + 1) f ∈ I := by
    have h := homogeneousComponent_mem_of_mem hI hh (n + 1)
    rw [sub_mul, one_mul, map_sub, map_sub,
      homogeneousComponent_mul_degree_one_succ hz] at h
    convert h using 1
    ring
  have hupper : ∀ n, t ≤ n → homogeneousComponent n g ∈ I := by
    apply Nat.strong_decreasing_induction
    · refine ⟨g.totalDegree, fun m hm _ => ?_⟩
      rw [homogeneousComponent_eq_zero m g hm]
      exact I.zero_mem
    · intro n ih hn
      have hnext := ih (n + 1) (by omega) (by omega)
      have hfn : homogeneousComponent (n + 1) f = 0 := by
        rw [homogeneousComponent_of_mem hf]
        simp [show n + 1 ≠ t by omega]
      have hr := hrec n
      rw [hfn, add_zero] at hr
      apply hsat
      have h := I.sub_mem hnext hr
      convert h using 1
      ring
  have hlow : ∀ n, n < t → homogeneousComponent n g ∈ I := by
    intro n
    induction n with
    | zero =>
      intro hn
      have hfn : homogeneousComponent 0 f = 0 := by
        rw [homogeneousComponent_of_mem hf]
        simp [show 0 ≠ t by omega]
      simpa only [hfn, add_zero] using hbase
    | succ n ih =>
      intro hn
      have hprev := I.mul_mem_left z (ih (by omega))
      have hfn : homogeneousComponent (n + 1) f = 0 := by
        rw [homogeneousComponent_of_mem hf]
        simp [show n + 1 ≠ t by omega]
      have hr := hrec n
      rw [hfn, add_zero] at hr
      simpa only [sub_add_cancel] using I.add_mem hr hprev
  cases t with
  | zero =>
    have h := I.sub_mem hbase (hupper 0 le_rfl)
    rw [homogeneousComponent_eq_self hf] at h
    convert h using 1
    ring
  | succ n =>
    have h := I.add_mem (I.sub_mem (hrec n) (hupper (n + 1) le_rfl))
      (I.mul_mem_left z (hlow n (Nat.lt_succ_self n)))
    rw [homogeneousComponent_eq_self hf] at h
    convert h using 1
    ring

/-- Homogeneous membership in a saturated homogeneous ideal is preserved and
reflected by the affine chart in the last coordinate. -/
theorem affineDehom_mem_map_iff
    (I : Ideal (Poly K 3))
    (hI : I.IsHomogeneous (homogeneousSubmodule (Fin 3) K))
    (hsat : ∀ p, (X 2 : Poly K 3) * p ∈ I → p ∈ I)
    {t : ℕ} {f : Poly K 3} (hf : f.IsHomogeneous t) :
    affineDehom f ∈ I.map (affineDehom (K := K)).toRingHom ↔ f ∈ I := by
  constructor
  · intro h
    obtain ⟨h, hh, heq⟩ :=
      (Ideal.mem_map_iff_of_surjective (affineDehom (K := K)).toRingHom
        affineDehom_surjective).mp h
    have hdiff : (X 2 - 1 : Poly K 3) ∣ f - h :=
      (affineDehom_eq_iff f h).mp heq.symm
    obtain ⟨g, hg⟩ := hdiff
    apply homogeneous_mem_of_sub_coordinate_one_mul I hI (isHomogeneous_X K (2 : Fin 3)) hsat hf g
    have hfg : f - (X 2 - 1) * g = h := by
      rw [← hg]
      ring
    rwa [hfg]
  · intro h
    exact Ideal.mem_map_of_mem (affineDehom (K := K)).toRingHom h

end ChoppedPlane
