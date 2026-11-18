import PowerConvexity.Calculus.DoubleZeroContactTwo
import PowerConvexity.Calculus.FrameReindex

/-! # Both skew third-derivative matrices vanish at a normalized double zero -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem skewThirdHessian_all_zero_at_double_zero_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ)))
    (k : Fin 2) : skewThirdHessian a b u k x = 0 := by
  let e := Equiv.swap (0 : Fin 2) k
  have hdet' (y : E) (hy : y ∈ U) : (complexHessian (a ∘ e) (b ∘ e) u y).det = ρ := by
    rw [complexHessian_frame_reindex,Matrix.det_submatrix_equiv_self]
    exact hdet y hy
  have hpos' (y : E) (hy : y ∈ U) : (complexHessian (a ∘ e) (b ∘ e) u y).PosDef := by
    rw [complexHessian_frame_reindex]
    exact (hpos y hy).submatrix e.injective
  have hM' : ∀ᶠ y in 𝓝 x, (modifiedSchur (a ∘ e) (b ∘ e) u y).PosSemidef := by
    filter_upwards [hM] with y hy
    rw [modifiedSchur_frame_reindex]
    exact hy.submatrix e
  have hI' : modifiedA (a ∘ e) (b ∘ e) u x = 1 := by
    rw [modifiedA_frame_reindex,hI,Matrix.submatrix_one_equiv]
  have hD' : modifiedB (a ∘ e) (b ∘ e) u x = Matrix.diagonal (fun _ => (1:ℂ)) := by
    rw [modifiedB_frame_reindex,hD,Matrix.submatrix_diagonal_equiv]
    rfl
  have hz := skewThirdHessian_zero_at_double_zero_two hU hu (a ∘ e) (b ∘ e)
    hρ hdet' hneg hpos' hx hM' hI' hD'
  rw [skewThirdHessian_frame_reindex] at hz
  ext i j
  have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M (e.symm i) (e.symm j)) hz
  simpa only [Matrix.submatrix_apply,Equiv.apply_symm_apply,Matrix.zero_apply,
    e,Equiv.swap_apply_left] using hh

end PowerConvexity
