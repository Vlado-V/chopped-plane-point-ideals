module

public import ChoppedPlane.RankOpen

@[expose] public section

noncomputable section
namespace ChoppedPlane
variable {K ι J V : Type*} [Field K] [Fintype J]
  [AddCommGroup V] [Module K V]

/-- A finite tuple of polynomial vector families is a polynomial family. -/
theorem IsPolynomialFamily.finite_pi {f : (ι → K) → J → V}
    (hf : ∀ j, IsPolynomialFamily (fun a => f a j)) : IsPolynomialFamily f := by
  classical
  have h := IsPolynomialFamily.sum (fun j =>
    (hf j).linear_comp (LinearMap.single K (fun _ : J => V) j))
  convert h using 1
  funext a j
  simp [LinearMap.single_apply]

end ChoppedPlane
