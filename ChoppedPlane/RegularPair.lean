module

public import ChoppedPlane.Multiplication
public import ChoppedPlane.RankOpen
public import ChoppedPlane.Numerics
public import ChoppedPlane.RegularSequence
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Nilpotent

@[expose] public section

/-! The Koszul description of all homogeneous relations of a relatively prime
pair, and the resulting Hilbert function in every degree. -/
noncomputable section
namespace ChoppedPlane
open MvPolynomial Module

variable {K : Type*} [Field K] {n d e : ℕ}

/-- Multiplication varies linearly with its actual homogeneous generators. -/
def multiplicationLinear {r : ℕ} (e : ℕ) :
    (Fin r → Forms K n d) →ₗ[K]
      ((Fin r → Forms K n e) →ₗ[K] Forms K n (d + e)) where
  toFun := multiplication
  map_add' q q' := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    simp [multiplication_val, add_mul, Finset.sum_add_distrib]
  map_smul' c q := by
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    simp [multiplication_val, ← Finset.smul_sum]

/-- Every polynomial relation of a relatively prime pair is a Koszul relation. -/
theorem pair_syzygy_relPrime (f g u v : Poly K n) (hf : f ≠ 0)
    (hcop : IsRelPrime f g) (h : f * u + g * v = 0) :
    ∃ w, u = -g * w ∧ v = f * w := by
  have hdvd : f ∣ g * v := ⟨-u, by linear_combination h⟩
  obtain ⟨w, hw⟩ := hcop.dvd_of_dvd_mul_left hdvd
  refine ⟨w, ?_, hw⟩
  apply mul_left_cancel₀ hf
  rw [hw] at h
  linear_combination h

/-- In a low multiplier degree, a relatively prime pair has no nonzero relation. -/
theorem pair_multiplication_injective_below (q : Fin 2 → Forms K n d)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val)
    (hed : e < d) : Function.Injective (multiplication (e := e) q) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  have hs : (q 0).val * (a 0).val + (q 1).val * (a 1).val = 0 := by
    simpa only [multiplication_val, Fin.sum_univ_two, Submodule.coe_zero] using congrArg Subtype.val ha
  obtain ⟨w, hw₀, hw₁⟩ := pair_syzygy_relPrime _ _ _ _ hq hcop hs
  have hv : (a 1).val = 0 := by
    have hc := congrArg (homogeneousComponent e) hw₁
    rw [homogeneousComponent_eq_self (a 1).property,
      homogeneousComponent_mul_eq_zero_of_lt e hed _ _ (q 0).property] at hc
    exact hc
  have hu : (a 0).val = 0 := by
    apply mul_left_cancel₀ hq
    simpa [hv] using hs
  funext i
  fin_cases i
  · exact Subtype.ext hu
  · exact Subtype.ext hv

/-- Homogeneous Koszul map in a multiplier degree at least `d`. -/
def pairKoszul (q : Fin 2 → Forms K n d) (hed : d ≤ e) :
    Forms K n (e - d) →ₗ[K] (Fin 2 → Forms K n e) where
  toFun w := ![
    ⟨-(q 1).val * w.val, by
      simpa only [Forms, mem_homogeneousSubmodule, Nat.add_sub_of_le hed, neg_mul]
        using ((q 1).property.mul w.property).neg⟩,
    ⟨(q 0).val * w.val, by simpa [Nat.add_sub_of_le hed] using (q 0).property.mul w.property⟩]
  map_add' u v := by ext i; fin_cases i <;> simp [mul_add]
  map_smul' c u := by ext i; fin_cases i <;> simp

theorem pairKoszul_injective (q : Fin 2 → Forms K n d) (hed : d ≤ e)
    (hq : (q 0).val ≠ 0) : Function.Injective (pairKoszul q hed) := by
  intro u v huv
  apply Subtype.ext
  have h := congrArg (fun a : Fin 2 → Forms K n e => (a 1).val) huv
  exact mul_left_cancel₀ hq h

/-- In every degree, the Koszul map presents the entire homogeneous relation space. -/
theorem range_pairKoszul (q : Fin 2 → Forms K n d) (hed : d ≤ e)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val) :
    (pairKoszul q hed).range = (multiplication (e := e) q).ker := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    simp [multiplication_val, Fin.sum_univ_two, pairKoszul]
    ring
  · intro a ha
    have hs : (q 0).val * (a 0).val + (q 1).val * (a 1).val = 0 := by
      simpa only [multiplication_val, Fin.sum_univ_two, Submodule.coe_zero] using
        congrArg Subtype.val (LinearMap.mem_ker.mp ha)
    obtain ⟨w, hw₀, hw₁⟩ := pair_syzygy_relPrime _ _ _ _ hq hcop hs
    let w' : Forms K n (e - d) := ⟨homogeneousComponent (e - d) w, homogeneousComponent_mem _ _⟩
    have hv : (a 1).val = (q 0).val * w'.val := by
      have hh := congrArg (homogeneousComponent e) hw₁
      rw [homogeneousComponent_eq_self (a 1).property] at hh
      have heq : e = d + (e - d) := (Nat.add_sub_of_le hed).symm
      conv_rhs at hh => rw [heq]
      rw [homogeneousComponent_mul_form (e - d) _ _ (q 0).property] at hh
      exact hh
    have hu : (a 0).val = -(q 1).val * w'.val := by
      apply mul_left_cancel₀ hq
      rw [hv] at hs
      linear_combination hs
    refine ⟨w', ?_⟩
    funext i
    fin_cases i
    · exact Subtype.ext hu.symm
    · exact Subtype.ext hv.symm

/-- The exact quotient dimension above the generators in a low multiplier degree. -/
theorem pair_hilbert_below_double (q : Fin 2 → Forms K n d)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val)
    (hed : e < d) :
    generatedHilbertFunction (generatorSpace q) (d + e) +
      2 * finrank K (Forms K n e) = finrank K (Forms K n (d + e)) := by
  have h := generatedHilbertFunction_add_rank (e := e) q
  rw [LinearMap.finrank_range_of_inj (pair_multiplication_injective_below q hq hcop hed),
    Module.finrank_pi_fintype] at h
  simpa using h

/-- The exact quotient dimension in all later degrees, including the second Koszul term. -/
theorem pair_hilbert_above_double (q : Fin 2 → Forms K n d) (hed : d ≤ e)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val) :
    generatedHilbertFunction (generatorSpace q) (d + e) +
      2 * finrank K (Forms K n e) =
      finrank K (Forms K n (d + e)) + finrank K (Forms K n (e - d)) := by
  have h := generatedHilbertFunction_add_rank (e := e) q
  have hk := (multiplication (e := e) q).finrank_range_add_finrank_ker
  rw [← range_pairKoszul q hed hq hcop,
    LinearMap.finrank_range_of_inj (pairKoszul_injective q hed hq),
    Module.finrank_pi_fintype] at hk
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hk
  omega

/-- Testing multiplication at coefficient degree `d-1` detects every common
nonunit divisor; no assertion about homogeneous greatest common divisors is used. -/
theorem pair_relPrime_of_multiplication_injective (q : Fin 2 → Forms K 3 d)
    (hq : (q 0).val ≠ 0)
    (hinj : Function.Injective (multiplication (e := d - 1) q)) :
    IsRelPrime (q 0).val (q 1).val := by
  classical
  intro h h₀ h₁
  by_contra hnu
  obtain ⟨u, hu⟩ := h₀
  obtain ⟨v, hv⟩ := h₁
  have hhn : h ≠ 0 := by
    intro hz
    exact hq (by simpa only [hz, zero_mul] using hu)
  have hun : u ≠ 0 := by
    intro hz
    exact hq (by simpa only [hz, mul_zero] using hu)
  have hhdeg : 0 < h.totalDegree := by
    by_contra! hz
    have hc : h = C (h.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (by omega)
    have hcn : h.coeff 0 ≠ 0 := by intro hr; simp [hr] at hc; exact hhn hc
    exact hnu (isUnit_iff_totalDegree_of_isReduced.mpr ⟨isUnit_iff_ne_zero.mpr hcn, by omega⟩)
  have hudeg : u.totalDegree < d := by
    have ht := congrArg MvPolynomial.totalDegree hu
    rw [(q 0).property.totalDegree hq, totalDegree_mul_of_isDomain hhn hun] at ht
    omega
  have hex : ∃ j ≤ u.totalDegree, homogeneousComponent j u ≠ 0 := by
    by_contra! hz
    apply hun
    rw [← sum_homogeneousComponent u]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hj)
  obtain ⟨j, hj, hjn⟩ := hex
  have hjd : j ≤ d - 1 := by omega
  have hr : (q 0).val * v - (q 1).val * u = 0 := by rw [hu, hv]; ring
  have hc : (q 0).val * homogeneousComponent j v -
      (q 1).val * homogeneousComponent j u = 0 := by
    have hc := congrArg (homogeneousComponent (d + j)) hr
    simpa only [map_sub, map_zero,
      homogeneousComponent_mul_form j _ _ (q 0).property,
      homogeneousComponent_mul_form j _ _ (q 1).property] using hc
  let z : Poly K 3 := X 2 ^ (d - 1 - j)
  have hz : z ≠ 0 := pow_ne_zero _ (MvPolynomial.X_ne_zero 2)
  have hzdeg : z.IsHomogeneous (d - 1 - j) := by
    simpa only [one_mul] using (isHomogeneous_X K 2).pow (d - 1 - j)
  let a : Fin 2 → Forms K 3 (d - 1) := ![
    ⟨homogeneousComponent j v * z, by
      simpa only [Forms, mem_homogeneousSubmodule, Nat.add_sub_of_le hjd]
        using (homogeneousComponent_mem j v).mul hzdeg⟩,
    ⟨-homogeneousComponent j u * z, by
      simpa only [Forms, mem_homogeneousSubmodule, Nat.add_sub_of_le hjd, neg_mul]
        using ((homogeneousComponent_mem j u).mul hzdeg).neg⟩]
  have ham : multiplication q a = 0 := by
    apply Subtype.ext
    simp only [multiplication_val, Fin.sum_univ_two]
    change (q 0).val * (homogeneousComponent j v * z) +
      (q 1).val * (-homogeneousComponent j u * z) = 0
    linear_combination hc * z
  have ha : a = 0 := (injective_iff_map_eq_zero _).mp hinj a ham
  have hcun : -homogeneousComponent j u * z = 0 :=
    congrArg (fun b : Fin 2 → Forms K 3 (d - 1) => (b 1).val) ha
  exact (mul_ne_zero (neg_ne_zero.mpr hjn) hz) hcun

/-- For positive degree, the concrete finite multiplication test characterizes
relative primeness of a nonzero pair. -/
theorem pair_relPrime_iff_multiplication_injective (q : Fin 2 → Forms K 3 d)
    (hd : 0 < d) (hq : (q 0).val ≠ 0) :
    IsRelPrime (q 0).val (q 1).val ↔
      Function.Injective (multiplication (e := d - 1) q) :=
  ⟨fun h => pair_multiplication_injective_below q hq h (by omega),
    pair_relPrime_of_multiplication_injective q hq⟩

/-- Injective multiplication by a pair forces its first generator to be nonzero. -/
theorem pair_first_ne_zero_of_multiplication_injective (q : Fin 2 → Forms K 3 d)
    (hinj : Function.Injective (multiplication (e := e) q)) : (q 0).val ≠ 0 := by
  intro hq
  let z : Forms K 3 e := ⟨X 2 ^ e, by simpa using (isHomogeneous_X K 2).pow e⟩
  let a : Fin 2 → Forms K 3 e := ![z, 0]
  have ham : multiplication q a = 0 := by
    apply Subtype.ext
    simp [multiplication_val, Fin.sum_univ_two, a, hq]
  have ha : a = 0 := (injective_iff_map_eq_zero _).mp hinj a ham
  have hz : (X 2 : Poly K 3) ^ e = 0 :=
    congrArg (fun b : Fin 2 → Forms K 3 e => (b 0).val) ha
  exact pow_ne_zero e (MvPolynomial.X_ne_zero 2) hz

/-- The coefficients of `(1-u^d)^2/(1-u)^3` are the genuine quotient dimensions
of a relatively prime degree-`d` pair, in every degree simultaneously. -/
theorem pair_generatedHilbertFunction (q : Fin 2 → Forms K 3 d)
    (hq : (q 0).val ≠ 0) (hcop : IsRelPrime (q 0).val (q 1).val) (t : ℕ) :
    (generatedHilbertFunction (generatorSpace q) t : ℤ) =
      N₂ (t : ℤ) - 2 * N₂ ((t : ℤ) - d) + N₂ ((t : ℤ) - 2 * d) := by
  by_cases htd : t < d
  · rw [generatedHilbertFunction_below_degree t htd _ (generatorSpace_le q)]
    rw [N₂_nat, N₂_neg (by omega : (t : ℤ) - d < 0),
      N₂_neg (by omega : (t : ℤ) - 2 * d < 0)]
    simp only [mul_zero, sub_zero, add_zero, N]
    congr 1
    have hsym := Nat.choose_symm (by omega : t ≤ t + 2)
    simpa only [show 3 + t - 1 = t + 2 by omega, show t + 2 - t = 2 by omega] using hsym.symm
  · let e := t - d
    have hte : t = d + e := by dsimp [e]; omega
    have h₁ : N₂ ((t : ℤ) - d) = (N e : ℤ) := by
      have heq : (t : ℤ) - d = (e : ℤ) := by dsimp [e]; omega
      rw [heq, N₂_nat]
    by_cases hed : e < d
    · have h₂ : N₂ ((t : ℤ) - 2 * d) = 0 := N₂_neg (by omega)
      have hh := pair_hilbert_below_double q hq hcop hed
      rw [finrank_plane_forms, finrank_plane_forms] at hh
      rw [← hte] at hh
      rw [N₂_nat, h₁, h₂]
      dsimp [N]
      omega
    · have h₂ : N₂ ((t : ℤ) - 2 * d) = (N (e - d) : ℤ) := by
        have heq : (t : ℤ) - 2 * d = ((e - d : ℕ) : ℤ) := by omega
        rw [heq, N₂_nat]
      have hh := pair_hilbert_above_double q (by omega : d ≤ e) hq hcop
      rw [finrank_plane_forms, finrank_plane_forms, finrank_plane_forms] at hh
      rw [← hte] at hh
      rw [N₂_nat, h₁, h₂]
      dsimp [N]
      omega

set_option backward.isDefEq.respectTransparency.types false in
/-- A relatively prime witness in a polynomial family gives an actual nonempty
principal open of regular pairs and their complete all-degree Hilbert formula. -/
theorem pair_regular_principal_open {ι : Type*} (hd : 0 < d)
    (q : (ι → K) → (Fin 2 → Forms K 3 d)) (hpoly : IsPolynomialFamily q)
    (a₀ : ι → K) (hq₀ : (q a₀ 0).val ≠ 0)
    (hcop₀ : IsRelPrime (q a₀ 0).val (q a₀ 1).val) :
    ∃ D : MvPolynomial ι K, eval a₀ D ≠ 0 ∧ ∀ a, eval a D ≠ 0 →
      IsRelPrime (q a 0).val (q a 1).val ∧
      RingTheory.Sequence.IsRegular (Poly K 3) [(q a 0).val, (q a 1).val] ∧
      ∀ t, (generatedHilbertFunction (generatorSpace (q a)) t : ℤ) =
        N₂ (t : ℤ) - 2 * N₂ ((t : ℤ) - d) + N₂ ((t : ℤ) - 2 * d) := by
  let A := fun a : ι → K => multiplication (e := d - 1) (q a)
  have hA : IsPolynomialFamily A := by
    intro ell
    exact hpoly
      { toFun := fun qs => ell (multiplication (e := d - 1) qs)
        map_add' := by
          intro qs qs'
          rw [show multiplication (e := d - 1) (qs + qs') =
            multiplication qs + multiplication qs' from
            (multiplicationLinear (K := K) (n := 3) (d := d) (r := 2) (d - 1)).map_add qs qs',
            map_add]
        map_smul' := by
          intro c qs
          rw [show multiplication (e := d - 1) (c • qs) =
            c • multiplication qs from
            (multiplicationLinear (K := K) (n := 3) (d := d) (r := 2) (d - 1)).map_smul c qs,
            map_smul]
          rfl }
  obtain ⟨D, hD, hgood⟩ := injective_polynomial_principal_open A hA a₀
    (pair_multiplication_injective_below (q a₀) hq₀ hcop₀ (by omega : d - 1 < d))
  refine ⟨D, hD, ?_⟩
  intro a ha
  have hinj := hgood a ha
  have hq := pair_first_ne_zero_of_multiplication_injective (q a) hinj
  have hcop := pair_relPrime_of_multiplication_injective (q a) hq hinj
  exact ⟨hcop, homogeneous_regular_pair hd _ _ hq hcop,
    pair_generatedHilbertFunction (q a) hq hcop⟩

end ChoppedPlane
