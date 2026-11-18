import PowerConvexity.Calculus.NormalizedSchurTraceBoundTwo
import PowerConvexity.Calculus.FrameReindexSecond

/-! # Both actual Schur diagonal contractions, with derivative norm control -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_dz_le_fderiv (f : E → ℂ) (x a b : E) :
    ‖dz a b f x‖ ≤ ((‖a‖+‖b‖)/2)*‖fderiv ℝ f x‖ := by
  unfold dz rd
  rw [norm_mul,norm_inv]
  have hh := norm_sub_le (fderiv ℝ f x a) (Complex.I*fderiv ℝ f x b)
  simp only [norm_mul,Complex.norm_I,one_mul] at hh
  have ha := (fderiv ℝ f x).le_opNorm a
  have hb := (fderiv ℝ f x).le_opNorm b
  norm_num
  nlinarith

theorem modifiedSchur_LM_normalized_all_rows_trace_bound_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    {B g : ℝ} (hB : 1 ≤ B) (hg : 0 ≤ g) (k : Fin 2)
    (hjets : normalizedSpectralJetBoundTwo
      (a ∘ Equiv.swap (0:Fin 2) k) (b ∘ Equiv.swap (0:Fin 2) k) u x B)
    (hgrad : ∀ p s, ‖dz (a p) (b p) (fun y => modifiedSchur a b u y k s) x‖ ≤ g) :
    (matrixL a b u (modifiedSchur a b u) x k k).re ≤
      (768*B^5+96*B^3)*(2-(d 0)^2-(d 1)^2)+48*B^2*g := by
  let e := Equiv.swap (0:Fin 2) k
  have hdet' (y : E) (hy : y ∈ U) : (complexHessian (a ∘ e) (b ∘ e) u y).det = ρ := by
    rw [complexHessian_frame_reindex,Matrix.det_submatrix_equiv_self]
    exact hdet y hy
  have hpos' (y : E) (hy : y ∈ U) : (complexHessian (a ∘ e) (b ∘ e) u y).PosDef := by
    rw [complexHessian_frame_reindex]
    exact (hpos y hy).submatrix e.injective
  have hI' : modifiedA (a ∘ e) (b ∘ e) u x = 1 := by
    rw [modifiedA_frame_reindex,hI,Matrix.submatrix_one_equiv]
  have hD' : modifiedB (a ∘ e) (b ∘ e) u x = Matrix.diagonal (fun i => (d (e i):ℂ)) := by
    rw [modifiedB_frame_reindex,hD,Matrix.submatrix_diagonal_equiv]
    rfl
  have heM : modifiedSchur (a ∘ e) (b ∘ e) u =
      fun y => (modifiedSchur a b u y).submatrix e e :=
    funext fun y => modifiedSchur_frame_reindex a b e u y
  have hh := modifiedSchur_LM_normalized_trace_row_bound_two hU hu (a ∘ e) (b ∘ e)
    hρ hdet' hneg hpos' hx (d ∘ e) hI' hD' (fun i => hd (e i)) hB hg hjets (by
      intro p s
      simpa only [heM,Matrix.submatrix_apply,Function.comp_apply,e,Equiv.swap_apply_left]
        using hgrad (e p) (e s))
  have hsum : (d (e 0))^2+(d (e 1))^2 = (d 0)^2+(d 1)^2 := by
    fin_cases k <;> simp [e,Equiv.swap_apply_def] <;> ring
  have hs : 2-(d (e 0))^2-(d (e 1))^2 = 2-(d 0)^2-(d 1)^2 := by linarith
  rw [heM,matrixL_frame_reindex] at hh
  simp only [Function.comp_apply] at hh
  rw [hs] at hh
  simpa only [Matrix.submatrix_apply,e,Equiv.swap_apply_left] using hh

theorem modifiedSchur_LM_normalized_all_rows_fderiv_bound_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ)))
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1)
    {B S : ℝ} (hB : 1 ≤ B) (hS : 0 ≤ S)
    (hdir : ∀ p, (‖a p‖+‖b p‖)/2 ≤ B) (k : Fin 2)
    (hjets : normalizedSpectralJetBoundTwo
      (a ∘ Equiv.swap (0:Fin 2) k) (b ∘ Equiv.swap (0:Fin 2) k) u x B)
    (hgrad : ∀ s, ‖fderiv ℝ (fun y => modifiedSchur a b u y k s) x‖ ≤ S) :
    (matrixL a b u (modifiedSchur a b u) x k k).re ≤
      (768*B^5+96*B^3)*(2-(d 0)^2-(d 1)^2)+48*B^3*S := by
  have hh := modifiedSchur_LM_normalized_all_rows_trace_bound_two hU hu a b hρ hdet hneg hpos
    hx d hI hD hd hB (show 0 ≤ B*S from mul_nonneg (by linarith) hS) k hjets (by
      intro p s
      refine (norm_dz_le_fderiv _ x (a p) (b p)).trans ?_
      exact mul_le_mul (hdir p) (hgrad s) (norm_nonneg _) (by linarith))
  convert hh using 1 <;> ring

end PowerConvexity
