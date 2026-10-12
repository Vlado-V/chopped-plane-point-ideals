module

public import ChoppedPlane.FerrersGrid
public import ChoppedPlane.ColumnGradedPresentation

@[expose] public section

/-! The column-graded split Ferrers seed. Its selected blocks satisfy `i ≤ j`. -/
noncomputable section
namespace ChoppedPlane.ColumnFerrers
open MvPolynomial
open scoped BigOperators
variable {K : Type*} [Field K] {c : ℕ}

abbrev RootIndex (ε : Fin c → ℕ) := Ferrers.RootIndex ε
abbrev SelectedIndex (ε : Fin c → ℕ) :=
  Σ ij : {ij : Fin c × Fin c // ij.1 ≤ ij.2}, Fin (ε ij.val.1) × Fin (ε ij.val.2)

def selectedX (ε : Fin c → ℕ) (α : RootIndex ε → K) (s : SelectedIndex ε) : K :=
  α ⟨s.1.val.1,s.2.1⟩
def selectedY (ε : Fin c → ℕ) (β : RootIndex ε → K) (s : SelectedIndex ε) : K :=
  β ⟨s.1.val.2,s.2.2⟩
def pointCoordinates (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    PointCoordinates K (Fintype.card (SelectedIndex ε)) := fun ik =>
  let s := (Fintype.equivFin (SelectedIndex ε)).symm ik.1
  if ik.2 = 0 then selectedX ε α s else selectedY ε β s
omit [Field K] in
@[simp] theorem pointCoordinates_first (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (i : Fin (Fintype.card (SelectedIndex ε))) :
    pointCoordinates ε α β (i,0) = selectedX ε α ((Fintype.equivFin _).symm i) := by
  simp [pointCoordinates]
omit [Field K] in
@[simp] theorem pointCoordinates_second (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (i : Fin (Fintype.card (SelectedIndex ε))) :
    pointCoordinates ε α β (i,1) = selectedY ε β ((Fintype.equivFin _).symm i) := by
  simp [pointCoordinates]

theorem selected_card (ε : Fin c → ℕ) :
    Fintype.card (SelectedIndex ε) =
      ∑ ij : {ij : Fin c × Fin c // ij.1 ≤ ij.2}, ε ij.val.1 * ε ij.val.2 := by
  simp [SelectedIndex, Fintype.card_sigma, Fintype.card_prod]

omit [Field K] in
theorem selected_injective (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    Function.Injective (fun s : SelectedIndex ε => (selectedX ε α s,selectedY ε β s)) := by
  intro s t h
  have hx := hα (congrArg Prod.fst h)
  have hy := hβ (congrArg Prod.snd h)
  obtain ⟨⟨⟨i,j⟩,hij⟩,a,b⟩ := s
  obtain ⟨⟨⟨i',j'⟩,hij'⟩,a',b'⟩ := t
  change (⟨i,a⟩ : RootIndex ε) = ⟨i',a'⟩ at hx
  change (⟨j,b⟩ : RootIndex ε) = ⟨j',b'⟩ at hy
  cases hx
  cases hy
  rfl

omit [Field K] in
theorem distinct_pointCoordinates (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    DistinctPoints K (pointCoordinates ε α β) := by
  intro i j h
  apply (Fintype.equivFin (SelectedIndex ε)).symm.injective
  apply selected_injective ε α β hα hβ
  simpa only [pointCoordinates_first,pointCoordinates_second] using h

/-- The diagonal and the next row of column `j` both have degree `ε j`. -/
def bidiagonal {R : Type*} [CommRing R] (f g : Fin c → R) :
    Matrix (Fin (c+1)) (Fin c) R := fun i j =>
  if i.val = j.val then f j else if i.val = j.val+1 then g j else 0

private theorem deleted_before {R : Type*} [CommRing R] (f g : Fin c → R)
    (k : Fin (c+1)) (i j : Fin c) (hi : i.val < k.val) :
    (bidiagonal f g).submatrix k.succAbove id i j =
      if i.val = j.val then f j else if i.val = j.val+1 then g j else 0 := by
  rw [Matrix.submatrix_apply,Fin.succAbove_of_castSucc_lt]
  · rfl
  · exact hi
private theorem deleted_after {R : Type*} [CommRing R] (f g : Fin c → R)
    (k : Fin (c+1)) (i j : Fin c) (hi : ¬i.val < k.val) :
    (bidiagonal f g).submatrix k.succAbove id i j =
      if i.val+1 = j.val then f j else if i.val = j.val then g j else 0 := by
  rw [Matrix.submatrix_apply,Fin.succAbove_of_le_castSucc]
  · simp [bidiagonal]
  · exact Nat.le_of_not_gt hi

/-- The ordered deleted-row determinant has the prefix/suffix product formula. -/
theorem bidiagonal_deletedRow_det {R : Type*} [CommRing R] (f g : Fin c → R)
    (k : Fin (c+1)) :
    ((bidiagonal f g).submatrix k.succAbove id).det =
      (∏ j ∈ Finset.univ.filter (fun j => j.val < k.val), f j) *
      (∏ j ∈ Finset.univ.filter (fun j => k.val ≤ j.val), g j) := by
  classical
  let A := (bidiagonal f g).submatrix k.succAbove id
  let p : Fin c → Prop := fun i => i.val < k.val
  have hsplit : ∀ i, ¬p i → ∀ j, p j → A i j = 0 := by
    intro i hi j hj
    change (bidiagonal f g).submatrix k.succAbove id i j = 0
    rw [deleted_after f g k i j hi]
    have hij : i.val ≠ j.val := by dsimp [p] at *; omega
    have hij' : i.val+1 ≠ j.val := by dsimp [p] at *; omega
    simp [hij,hij']
  rw [Matrix.twoBlockTriangular_det A p hsplit]
  have hl : (A.toSquareBlockProp p).IsLowerTriangular := by
    intro i j hij
    change (bidiagonal f g).submatrix k.succAbove id i.val j.val = 0
    rw [deleted_before f g k i.val j.val i.property]
    have hv : i.val.val < j.val.val := hij
    have hne : i.val.val ≠ j.val.val := by omega
    have hne' : i.val.val ≠ j.val.val+1 := by omega
    simp [hne,hne']
  have hr : (A.toSquareBlockProp (fun i => ¬p i)).IsUpperTriangular := by
    intro i j hij
    change (bidiagonal f g).submatrix k.succAbove id i.val j.val = 0
    rw [deleted_after f g k i.val j.val i.property]
    have hv : j.val.val < i.val.val := hij
    have hne : i.val.val ≠ j.val.val := by omega
    have hne' : i.val.val+1 ≠ j.val.val := by omega
    simp [hne,hne']
  rw [Matrix.det_of_isLowerTriangular _ hl,Matrix.det_of_isUpperTriangular hr]
  have hleft : (∏ i : {i : Fin c // p i}, A i.val i.val) =
      ∏ i ∈ Finset.univ.filter (fun i => i.val < k.val), f i := by
    calc
      _ = ∏ i : {i : Fin c // p i}, f i.val := by
        apply Finset.prod_congr rfl
        intro i _
        change (bidiagonal f g).submatrix k.succAbove id i.val i.val = f i.val
        rw [deleted_before f g k i.val i.val i.property]
        simp
      _ = _ := (Finset.prod_subtype _ (by simp [p]) f).symm
  have hright : (∏ i : {i : Fin c // ¬p i}, A i.val i.val) =
      ∏ i ∈ Finset.univ.filter (fun i => k.val ≤ i.val), g i := by
    calc
      _ = ∏ i : {i : Fin c // ¬p i}, g i.val := by
        apply Finset.prod_congr rfl
        intro i _
        change (bidiagonal f g).submatrix k.succAbove id i.val i.val = g i.val
        rw [deleted_after f g k i.val i.val i.property]
        simp
      _ = _ := (Finset.prod_subtype _ (by simp [p]) g).symm
  exact congrArg₂ (· * ·) hleft hright

def seedMatrix (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    Matrix (Fin (c+1)) (Fin c) (Poly K 3) :=
  bidiagonal (Ferrers.rowFirst ε α) (Ferrers.rowSecond ε β)
def cofactorProduct (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (k : Fin (c+1)) : Poly K 3 :=
  (∏ j ∈ Finset.univ.filter (fun j => j.val < k.val), Ferrers.rowFirst ε α j) *
  (∏ j ∈ Finset.univ.filter (fun j => k.val ≤ j.val), Ferrers.rowSecond ε β j)
def cofactorIdeal (ε : Fin c → ℕ) (α β : RootIndex ε → K) : Ideal (Poly K 3) :=
  Ideal.span (Set.range (cofactorProduct ε α β))

theorem seedMatrix_deletedRow_det (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (k : Fin (c+1)) :
    ((seedMatrix ε α β).submatrix k.succAbove id).det = cofactorProduct ε α β k :=
  bidiagonal_deletedRow_det _ _ _

theorem seedMatrix_homogeneous (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (i : Fin (c+1)) (j : Fin c) : (seedMatrix ε α β i j).IsHomogeneous (ε j) := by
  classical
  unfold seedMatrix bidiagonal
  split_ifs
  · exact Ferrers.rowFirst_homogeneous ε α j
  · exact Ferrers.rowSecond_homogeneous ε β j
  · exact isHomogeneous_zero (Fin 3) K (ε j)

theorem cofactorProduct_homogeneous (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (k : Fin (c+1)) : (cofactorProduct ε α β k).IsHomogeneous (∑ j, ε j) := by
  rw [← seedMatrix_deletedRow_det]
  exact maximalMinor_homogeneous_columns (seedMatrix ε α β) ε
    (seedMatrix_homogeneous ε α β) k

theorem cofactorProduct_eval_selected (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (s : SelectedIndex ε) (k : Fin (c+1)) :
    eval ![selectedX ε α s,selectedY ε β s,1] (cofactorProduct ε α β k) = 0 := by
  classical
  simp only [cofactorProduct,map_mul,map_prod]
  by_cases h : s.1.val.1.val < k.val
  · apply mul_eq_zero_of_left
    apply Finset.prod_eq_zero (i := s.1.val.1)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
    · exact Ferrers.rowFirst_eval_root ε α ⟨s.1.val.1,s.2.1⟩ _
  · apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (i := s.1.val.2)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by
        have := s.1.property
        simp only [Fin.le_def] at this
        omega⟩
    · exact Ferrers.rowSecond_eval_root ε β ⟨s.1.val.2,s.2.2⟩ _

theorem cofactorIdeal_le_pointIdeal (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    cofactorIdeal ε α β ≤ pointIdeal K (pointCoordinates ε α β) := by
  apply Ideal.span_le.mpr
  rintro f ⟨j,rfl⟩
  apply Ideal.mem_iInf.mpr
  intro i
  apply (homogeneous_mem_singlePointIdeal_iff _ _
    ⟨cofactorProduct ε α β j,cofactorProduct_homogeneous ε α β j⟩).mpr
  simp only [pointCoordinates_first,pointCoordinates_second]
  exact cofactorProduct_eval_selected ε α β ((Fintype.equivFin _).symm i) j

theorem cofactorProducts_vanish_iff_selected (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) (hα : Function.Injective α) (hβ : Function.Injective β)
    (u v : RootIndex ε) :
    (∀ k, eval ![α u,β v,1] (cofactorProduct ε α β k) = 0) ↔ u.1 ≤ v.1 := by
  constructor
  · intro hall
    by_contra hn
    let k : Fin (c+1) := u.1.castSucc
    have hh : eval ![α u,β v,1] (cofactorProduct ε α β k) ≠ 0 := by
      classical
      simp only [cofactorProduct,map_mul,map_prod]
      apply mul_ne_zero
      · apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hil := (Finset.mem_filter.mp hi).2
        exact Ferrers.rowFirst_eval_ne_zero ε α hα u i (by
          intro heq
          subst i
          change u.1.val < u.1.val at hil
          omega) _
      · apply Finset.prod_ne_zero_iff.mpr
        intro i hi
        have hil := (Finset.mem_filter.mp hi).2
        exact Ferrers.rowSecond_eval_ne_zero ε β hβ v i (by
          intro heq
          subst i
          change u.1.val ≤ v.1.val at hil
          exact hn hil) _
    exact hh (hall k)
  · intro huv k
    exact cofactorProduct_eval_selected ε α β ⟨⟨(u.1,v.1),huv⟩,(u.2,v.2)⟩ k

@[simp] theorem cofactorProduct_zero (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    cofactorProduct ε α β 0 = ∏ j, Ferrers.rowSecond ε β j := by
  classical
  simp [cofactorProduct]
@[simp] theorem cofactorProduct_last (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    cofactorProduct ε α β (Fin.last c) = ∏ j, Ferrers.rowFirst ε α j := by
  classical
  have hl : Finset.univ.filter (fun j : Fin c => j.val < (Fin.last c).val) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j _
    exact j.isLt
  have hr : Finset.univ.filter (fun j : Fin c => (Fin.last c).val ≤ j.val) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _ hj
    exact Nat.not_le_of_lt j.isLt hj
  rw [cofactorProduct,hl,hr,Finset.prod_empty,mul_one]

theorem seedMatrix_primitive (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    PrimitiveMaximalMinors (seedMatrix ε α β) := by
  apply primitiveMaximalMinors_of_relPrime_pair _ (Fin.last c) 0
  change IsRelPrime
    (((seedMatrix ε α β).submatrix (Fin.last c).succAbove id).det)
    (((seedMatrix ε α β).submatrix (0 : Fin (c+1)).succAbove id).det)
  rw [seedMatrix_deletedRow_det,seedMatrix_deletedRow_det,
    cofactorProduct_last,cofactorProduct_zero]
  exact Ferrers.firstProducts_relPrime_secondProducts ε α β _ _

theorem seedMatrix_cofactorIdeal (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    ChoppedPlane.cofactorIdeal (seedMatrix ε α β) = cofactorIdeal ε α β := by
  rw [ChoppedPlane.cofactorIdeal_eq_span_maximalMinor]
  have h : maximalMinor (seedMatrix ε α β) = cofactorProduct ε α β := by
    funext i
    exact seedMatrix_deletedRow_det ε α β i
  rw [h]
  rfl

theorem pureSeed_primitive {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (ε : Fin c → ℕ) (x y : R) (hxy : IsRelPrime x y) :
    PrimitiveMaximalMinors (bidiagonal (fun j => x ^ ε j) (fun j => y ^ ε j)) := by
  apply primitiveMaximalMinors_of_relPrime_pair _ (Fin.last c) 0
  change IsRelPrime
    (((bidiagonal (fun j => x ^ ε j) (fun j => y ^ ε j)).submatrix
      (Fin.last c).succAbove id).det)
    (((bidiagonal (fun j => x ^ ε j) (fun j => y ^ ε j)).submatrix
      (0 : Fin (c+1)).succAbove id).det)
  rw [bidiagonal_deletedRow_det,bidiagonal_deletedRow_det]
  have hl : Finset.univ.filter (fun j : Fin c => j.val < (Fin.last c).val) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro j _
    exact j.isLt
  have hr : Finset.univ.filter (fun j : Fin c => (Fin.last c).val ≤ j.val) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j _ hj
    exact Nat.not_le_of_lt j.isLt hj
  classical
  simp only [hl,hr,Finset.prod_empty,mul_one]
  simp only [Fin.val_zero,Nat.not_lt_zero,Finset.filter_false,Finset.prod_empty,
    Nat.zero_le,Finset.filter_true,one_mul]
  apply IsRelPrime.prod_left
  intro i _
  apply IsRelPrime.prod_right
  intro j _
  exact hxy.pow_left.pow_right

theorem seedMatrix_map_infinity (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    (seedMatrix ε α β).map Ferrers.infinityMap =
      bidiagonal (fun j => (X 0 : Poly K 2)^ε j) (fun j => (X 1 : Poly K 2)^ε j) := by
  classical
  funext i j
  change Ferrers.infinityMap (if i.val = j.val then Ferrers.rowFirst ε α j
    else if i.val = j.val+1 then Ferrers.rowSecond ε β j else 0) = _
  split_ifs <;> simp [bidiagonal,Ferrers.infinityMap,Ferrers.rowFirst,Ferrers.rowSecond, *]

theorem seedMatrix_primitive_atInfinity (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    PrimitiveMaximalMinors ((seedMatrix ε α β).map Ferrers.infinityMap) := by
  rw [seedMatrix_map_infinity]
  exact pureSeed_primitive ε _ _ Ferrers.binary_X_relPrime

theorem cofactorIdeal_z_saturated (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (n : ℕ) (p : Poly K 3) :
    X 2 ^ n * p ∈ cofactorIdeal ε α β ↔ p ∈ cofactorIdeal ε α β := by
  rw [← seedMatrix_cofactorIdeal]
  exact pow_mul_mem_cofactorIdeal_iff (seedMatrix ε α β) (X 2) (X_ne_zero _)
    Ferrers.infinityMap Ferrers.infinityMap_surjective Ferrers.infinityMap_ker
    (seedMatrix_primitive_atInfinity ε α β) n p

attribute [local instance] MvPolynomial.gradedAlgebra

theorem cofactorIdeal_homogeneous (ε : Fin c → ℕ) (α β : RootIndex ε → K) :
    (cofactorIdeal ε α β).IsHomogeneous (homogeneousSubmodule (Fin 3) K) := by
  apply Ideal.homogeneous_span
  rintro f ⟨j,rfl⟩
  exact ⟨_,cofactorProduct_homogeneous ε α β j⟩

def affineCofactorIdeal (ε : Fin c → ℕ) (α β : RootIndex ε → K) : Ideal (Poly K 2) :=
  (cofactorIdeal ε α β).map (affineDehom (K := K)).toRingHom

theorem mvAffineGridIdeal_le_affineCofactorIdeal (ε : Fin c → ℕ)
    (α β : RootIndex ε → K) :
    Grid.mvAffineGridIdeal (Ferrers.flatRoots ε α) (Ferrers.flatRoots ε β) ≤
      affineCofactorIdeal ε α β := by
  apply Ideal.span_le.mpr
  rintro f (rfl | rfl)
  · have hmem : cofactorProduct ε α β (Fin.last c) ∈ cofactorIdeal ε α β :=
      Ideal.subset_span ⟨Fin.last c,rfl⟩
    have hh := Ideal.mem_map_of_mem (affineDehom (K := K)).toRingHom hmem
    rw [cofactorProduct_last,Ferrers.totalFirst_eq_planeFirst] at hh
    simpa [Grid.planeFirst,Grid.affineFirstProduct,affineDehom,affineCofactorIdeal] using hh
  · have hmem : cofactorProduct ε α β 0 ∈ cofactorIdeal ε α β :=
      Ideal.subset_span ⟨0,rfl⟩
    have hh := Ideal.mem_map_of_mem (affineDehom (K := K)).toRingHom hmem
    rw [cofactorProduct_zero,Ferrers.totalSecond_eq_planeSecond] at hh
    simpa [Grid.planeSecond,Grid.affineSecondProduct,affineDehom,affineCofactorIdeal] using hh

def selectedGridSet (ε : Fin c → ℕ) :
    Set (Fin (Fintype.card (RootIndex ε)) × Fin (Fintype.card (RootIndex ε))) :=
  {ij | ((Fintype.equivFin (RootIndex ε)).symm ij.1).1 ≤
    ((Fintype.equivFin (RootIndex ε)).symm ij.2).1}

theorem affineCofactor_separator (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (ij : Fin (Fintype.card (RootIndex ε)) × Fin (Fintype.card (RootIndex ε)))
    (hij : ij ∉ selectedGridSet ε) :
    ∃ f ∈ affineCofactorIdeal ε α β,
      Grid.mvAffineGridEvaluation (Ferrers.flatRoots ε α) (Ferrers.flatRoots ε β) f ij ≠ 0 := by
  let u := (Fintype.equivFin (RootIndex ε)).symm ij.1
  let v := (Fintype.equivFin (RootIndex ε)).symm ij.2
  have hn : ¬u.1 ≤ v.1 := hij
  have hnot : ¬∀ j, eval ![α u,β v,1] (cofactorProduct ε α β j) = 0 := by
    intro hall
    exact hn ((cofactorProducts_vanish_iff_selected ε α β hα hβ u v).mp hall)
  push Not at hnot
  obtain ⟨j,hj⟩ := hnot
  refine ⟨affineDehom (cofactorProduct ε α β j),
    Ideal.mem_map_of_mem (affineDehom (K := K)).toRingHom
      (Ideal.subset_span ⟨j,rfl⟩),?_⟩
  simpa only [Grid.mvAffineGridEvaluation_apply,Ferrers.flatRoots,
    Ferrers.eval_affineDehom] using hj

theorem homogeneous_mem_cofactorIdeal_of_pointIdeal {t : ℕ}
    (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β)
    (f : Forms K 3 t) (hf : f.val ∈ pointIdeal K (pointCoordinates ε α β)) :
    f.val ∈ cofactorIdeal ε α β := by
  have hsat : ∀ p : Poly K 3, X 2 * p ∈ cofactorIdeal ε α β →
      p ∈ cofactorIdeal ε α β := by
    intro p hp
    exact (cofactorIdeal_z_saturated ε α β 1 p).mp (by simpa using hp)
  apply (affineDehom_mem_map_iff (cofactorIdeal ε α β)
    (cofactorIdeal_homogeneous ε α β) hsat f.property).mp
  have hker : RingHom.ker
      (Grid.mvAffineGridEvaluation (Ferrers.flatRoots ε α) (Ferrers.flatRoots ε β)) ≤
      affineCofactorIdeal ε α β := by
    rw [Grid.mvAffineGridEvaluation_ker _ _ (Ferrers.flatRoots_injective ε α hα)
      (Ferrers.flatRoots_injective ε β hβ)]
    exact mvAffineGridIdeal_le_affineCofactorIdeal ε α β
  apply mem_ideal_of_vanish_on_selected
    (Grid.mvAffineGridEvaluation (Ferrers.flatRoots ε α) (Ferrers.flatRoots ε β))
    (Grid.mvAffineGridEvaluation_surjective _ _ (Ferrers.flatRoots_injective ε α hα)
      (Ferrers.flatRoots_injective ε β hβ))
    (affineCofactorIdeal ε α β) hker (selectedGridSet ε)
    (affineCofactor_separator ε α β hα hβ)
  intro ij hij
  let u := (Fintype.equivFin (RootIndex ε)).symm ij.1
  let v := (Fintype.equivFin (RootIndex ε)).symm ij.2
  have huv : u.1 ≤ v.1 := hij
  let s : SelectedIndex ε := ⟨⟨(u.1,v.1),huv⟩,(u.2,v.2)⟩
  have hh := (mem_pointDegreePiece (pointCoordinates ε α β) f).mp
    ((homogeneous_mem_pointIdeal_iff (pointCoordinates ε α β) f).mp hf)
    (Fintype.equivFin (SelectedIndex ε) s)
  change eval ![pointCoordinates ε α β (Fintype.equivFin (SelectedIndex ε) s,0),
    pointCoordinates ε α β (Fintype.equivFin (SelectedIndex ε) s,1),1] f.val = 0 at hh
  simp only [pointCoordinates_first,pointCoordinates_second,Equiv.symm_apply_apply] at hh
  simpa [Grid.mvAffineGridEvaluation_apply,Ferrers.flatRoots,Ferrers.eval_affineDehom,
    selectedX,selectedY,s,u,v] using hh

/-- The column-graded seed ideal is exactly the ideal of its selected distinct points. -/
theorem cofactorIdeal_eq_pointIdeal (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    cofactorIdeal ε α β = pointIdeal K (pointCoordinates ε α β) := by
  apply le_antisymm (cofactorIdeal_le_pointIdeal ε α β)
  intro f hf
  apply (mem_iff_homogeneousComponent_mem (cofactorIdeal_homogeneous ε α β) f).mpr
  intro t
  exact homogeneous_mem_cofactorIdeal_of_pointIdeal ε α β hα hβ
    ⟨homogeneousComponent t f,homogeneousComponent_mem t f⟩
    (homogeneousComponent_mem_of_mem (Ferrers.pointIdeal_homogeneous
      (pointCoordinates ε α β)) hf t)

theorem affineCofactorIdeal_quotient_reduced (ε : Fin c → ℕ) (α β : RootIndex ε → K)
    (hα : Function.Injective α) (hβ : Function.Injective β) :
    IsReduced (Poly K 2 ⧸ affineCofactorIdeal ε α β) :=
  Grid.quotient_reduced_of_mvAffineGridIdeal_le (Ferrers.flatRoots ε α)
    (Ferrers.flatRoots ε β) (Ferrers.flatRoots_injective ε α hα)
    (Ferrers.flatRoots_injective ε β hβ) (affineCofactorIdeal ε α β)
    (mvAffineGridIdeal_le_affineCofactorIdeal ε α β)

end ChoppedPlane.ColumnFerrers
