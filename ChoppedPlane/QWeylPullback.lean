module

public import Mathlib.Tactic

@[expose] public section

/-!
# Polynomial identities for the cubic rank-three witness

This file contains the explicit algebraic identities behind the quartic
pullback of the cyclic three-dimensional binary-polynomial module.  Every
statement is an identity in a commutative ring; the cubic relation is stated
as an equation rather than imported from geometry.
-/

namespace ChoppedPlane.QWeyl

variable {A : Type*} [CommRing A]

/-- First binary quartic in the cubic pullback. -/
def quarticU (u v : A) : A := u * (u ^ 3 + 2 * v ^ 3)

/-- Second binary quartic in the cubic pullback. -/
def quarticV (u v : A) : A := -v * (2 * u ^ 3 + v ^ 3)

/-- The third quartic, after adjoining a cubic root. -/
def quarticZ (u v z : A) : A := z * (u ^ 3 - v ^ 3)

theorem quartic_binary_cubic (u v : A) :
    quarticU u v ^ 3 + quarticV u v ^ 3 =
      (u ^ 3 + v ^ 3) * (u ^ 3 - v ^ 3) ^ 3 := by
  unfold quarticU quarticV
  ring

theorem quartic_preserves_cubic (u v z : A) (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    quarticU u v ^ 3 + quarticV u v ^ 3 = quarticZ u v z ^ 3 := by
  rw [quartic_binary_cubic]
  unfold quarticZ
  rw [mul_pow, hz]

/-- These identities supply a right inverse for the quartic row on the
`u` chart, without using a projective no-common-zero argument. -/
theorem quartic_bezout_u (u v : A) :
    (3 * u ^ 3 + 2 * v ^ 3) * quarticU u v +
      4 * u * v ^ 2 * quarticV u v = 3 * u ^ 7 := by
  unfold quarticU quarticV
  ring

/-- The corresponding identity on the `v` chart. -/
theorem quartic_bezout_v (u v : A) :
    -4 * u ^ 2 * v * quarticU u v -
      (3 * v ^ 3 + 2 * u ^ 3) * quarticV u v = 3 * v ^ 7 := by
  unfold quarticU quarticV
  ring

/-- The first quadratic syzygy of the quartic row. -/
theorem quartic_quadratic_syzygy_one (u v z : A) :
    quarticU u v * (v * z) + quarticV u v * (z * u) +
      quarticZ u v z * (u * v) = 0 := by
  unfold quarticU quarticV quarticZ
  ring

/-- The second quadratic syzygy, modulo the cubic equation. -/
theorem quartic_quadratic_syzygy_two (u v z : A)
    (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    quarticU u v * u ^ 2 + quarticV u v * v ^ 2 -
      quarticZ u v z * z ^ 2 = 0 := by
  unfold quarticU quarticV quarticZ
  calc
    _ = (u ^ 3 - v ^ 3) * (u ^ 3 + v ^ 3 - z ^ 3) := by ring
    _ = 0 := by rw [hz]; ring

/-- The first maximal minor of the two quadratic syzygies. -/
theorem quadratic_minor_u (u v z : A) (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    (z * u) * (-z ^ 2) - (u * v) * v ^ 2 = -quarticU u v := by
  unfold quarticU
  calc
    _ = -u * z ^ 3 - u * v ^ 3 := by ring
    _ = _ := by rw [hz]; ring

/-- The second maximal minor. -/
theorem quadratic_minor_v (u v z : A) (hz : z ^ 3 = u ^ 3 + v ^ 3) :
    (u * v) * u ^ 2 - (v * z) * (-z ^ 2) = -quarticV u v := by
  unfold quarticV
  calc
    _ = u ^ 3 * v + v * z ^ 3 := by ring
    _ = _ := by rw [hz]; ring

/-- The third maximal minor. -/
theorem quadratic_minor_z (u v z : A) :
    (v * z) * v ^ 2 - (z * u) * u ^ 2 = -quarticZ u v z := by
  unfold quarticZ
  ring

/-- A root of `T²+T+1` is a cube root of unity. -/
theorem cube_eq_one (q : A) (hq : q ^ 2 + q + 1 = 0) : q ^ 3 = 1 := by
  linear_combination (q - 1) * hq

/-- The quartic coefficient along one cyclic basis vector. -/
theorem quartic_factor_zero (u v : A) :
    quarticU u v + quarticV u v = (u + v) * (u - v) ^ 3 := by
  unfold quarticU quarticV
  ring

/-- The quartic factorization for any cube root of unity. -/
theorem quartic_factor_of_cube (u v q : A) (hq3 : q ^ 3 = 1) :
    quarticU u v + q * quarticV u v =
      (u + q * v) * (u - q * v) ^ 3 := by
  have hq4 : q ^ 4 = q := by
    calc
      q ^ 4 = q ^ 3 * q := by ring
      _ = q := by rw [hq3]; ring
  unfold quarticU quarticV
  ring_nf
  rw [hq3, hq4]
  ring

/-- The factorization along the second cyclic basis vector. -/
theorem quartic_factor_one (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    quarticU u v + q * quarticV u v =
      (u + q * v) * (u - q * v) ^ 3 :=
  quartic_factor_of_cube u v q (cube_eq_one q hq)

/-- The factorization along the third cyclic basis vector. -/
theorem quartic_factor_two (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    quarticU u v + q ^ 2 * quarticV u v =
      (u + q ^ 2 * v) * (u - q ^ 2 * v) ^ 3 := by
  apply quartic_factor_of_cube
  rw [← pow_mul, show 2 * 3 = 3 * 2 from by omega, pow_mul,
    cube_eq_one q hq, one_pow]

/-- The factorization of the product of the three binary chart factors. -/
theorem binary_cubic_factor (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u - v) * (u - q * v) * (u - q ^ 2 * v) = u ^ 3 - v ^ 3 := by
  have hq3 : q ^ 3 = 1 := cube_eq_one q hq
  calc
    _ = u ^ 3 - u ^ 2 * v * (q ^ 2 + q + 1) +
        u * v ^ 2 * (q ^ 3 + q ^ 2 + q) - q ^ 3 * v ^ 3 := by ring
    _ = _ := by
      rw [hq3]
      linear_combination (-u ^ 2 * v + u * v ^ 2) * hq

/-- First weight of the semilinear coefficient-module pullback. -/
def weightZero (u v q : A) : A := (u - v) ^ 2 * (u - q * v)

/-- Second weight of the semilinear coefficient-module pullback. -/
def weightOne (u v q : A) : A := (u - q * v) ^ 2 * (u - q ^ 2 * v)

/-- Third weight of the semilinear coefficient-module pullback. -/
def weightTwo (u v q : A) : A := (u - q ^ 2 * v) ^ 2 * (u - v)

/-- The first cyclic intertwining identity. -/
theorem intertwiner_zero (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u + v) * (u ^ 3 - v ^ 3) * weightZero u v q =
      (quarticU u v + quarticV u v) * weightOne u v q := by
  rw [quartic_factor_zero, ← binary_cubic_factor u v q hq]
  unfold weightZero weightOne
  ring

/-- The second cyclic intertwining identity. -/
theorem intertwiner_one (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u + q * v) * (u ^ 3 - v ^ 3) * weightOne u v q =
      (quarticU u v + q * quarticV u v) * weightTwo u v q := by
  rw [quartic_factor_one u v q hq, ← binary_cubic_factor u v q hq]
  unfold weightOne weightTwo
  ring

/-- The third cyclic intertwining identity. -/
theorem intertwiner_two (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) * weightTwo u v q =
      (quarticU u v + q ^ 2 * quarticV u v) * weightZero u v q := by
  rw [quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  unfold weightTwo weightZero
  ring

/-- Reverse cyclic identities for the binary-module dual, whose three
generators have degree two. -/
theorem dual_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + q ^ 2 * v) * (u ^ 3 - v ^ 3) * (d1 * d2 ^ 2) =
        f2 * (d0 * d1 ^ 2)) ∧
    ((u + v) * (u ^ 3 - v ^ 3) * (d2 * d0 ^ 2) =
        f0 * (d1 * d2 ^ 2)) ∧
    ((u + q * v) * (u ^ 3 - v ^ 3) * (d0 * d1 ^ 2) =
        f1 * (d2 * d0 ^ 2)) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- The shifted module with generator degrees `(0,0,1)` has cyclic
coefficients `(u+v,1,(u+q*v)*(u+q²*v))`. -/
theorem shifted_two_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + v) * (u ^ 3 - v ^ 3) * d0 ^ 2 = f0 * (d1 * d2)) ∧
    ((u ^ 3 - v ^ 3) * (d1 * d2) = d2 ^ 2 * d0 * d1 ^ 2) ∧
    ((u + q * v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d2 ^ 2 * d0 * d1 ^ 2) = f1 * f2 * d0 ^ 2) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- The dual of the preceding shifted module has generator degrees
`(2,2,1)` and the reverse cyclic action. -/
theorem shifted_two_dual_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + q * v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d1 ^ 2 * d2 ^ 2) = f1 * f2 * d0) ∧
    ((u + v) * (u ^ 3 - v ^ 3) * (d1 * d2 * d0 ^ 2) =
        f0 * (d1 ^ 2 * d2 ^ 2)) ∧
    ((u ^ 3 - v ^ 3) * d0 = d1 * d2 * d0 ^ 2) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- The shifted module with generator degrees `(0,1,1)` has cyclic
coefficients `(1,u+q*v,(u+v)*(u+q²*v))`. -/
theorem shifted_one_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u ^ 3 - v ^ 3) * d1 = d0 * d1 ^ 2 * d2) ∧
    ((u + q * v) * (u ^ 3 - v ^ 3) * (d0 * d1 ^ 2 * d2) =
        f1 * (d0 ^ 2 * d2 ^ 2)) ∧
    ((u + v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d0 ^ 2 * d2 ^ 2) = f0 * f2 * d1) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

/-- Its dual has generator degrees `(2,1,1)` and reverse cyclic action. -/
theorem shifted_one_dual_intertwiners (u v q : A) (hq : q ^ 2 + q + 1 = 0) :
    let d0 := u - v
    let d1 := u - q * v
    let d2 := u - q ^ 2 * v
    let f0 := quarticU u v + quarticV u v
    let f1 := quarticU u v + q * quarticV u v
    let f2 := quarticU u v + q ^ 2 * quarticV u v
    ((u + v) * (u + q ^ 2 * v) * (u ^ 3 - v ^ 3) *
        (d0 ^ 2 * d1 * d2 ^ 2) = f0 * f2 * d1 ^ 2) ∧
    ((u ^ 3 - v ^ 3) * (d0 * d2) = d0 ^ 2 * d1 * d2 ^ 2) ∧
    ((u + q * v) * (u ^ 3 - v ^ 3) * d1 ^ 2 = f1 * (d0 * d2)) := by
  dsimp
  rw [quartic_factor_zero, quartic_factor_one u v q hq,
    quartic_factor_two u v q hq, ← binary_cubic_factor u v q hq]
  constructor
  · ring
  constructor <;> ring

end ChoppedPlane.QWeyl
