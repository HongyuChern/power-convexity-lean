import PowerConvexity.Algebra.DeterminantOrderTwo

/-! # An inverse order consequence of the two-point Hessian contact inequality -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_sub_posSemidef_of_contact
    {H S : Matrix ι ι ℂ} (hH : H.PosDef) (hS : S.IsHermitian)
    (hc : (S-S*H*S).PosSemidef) : (H⁻¹-S).PosSemidef := by
  let D := H⁻¹-S
  have hD : D.IsHermitian := hH.inv.isHermitian.sub hS
  have hPSD := hH.posSemidef.mul_mul_conjTranspose_same D
  have hunit : IsUnit H.det := (Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit
  have hleft : H⁻¹*H = 1 := Matrix.nonsing_inv_mul _ hunit
  have hright : H*H⁻¹ = 1 := Matrix.mul_nonsing_inv _ hunit
  have he : D*H*D.conjTranspose+(S-S*H*S) = H⁻¹-S := by
    rw [hD.eq]
    dsimp only [D]
    simp only [Matrix.sub_mul,Matrix.mul_sub,hleft,Matrix.one_mul]
    rw [Matrix.mul_assoc S H H⁻¹,hright,Matrix.mul_one]
    abel
  simpa only [he] using hPSD.add hc

end PowerConvexity
