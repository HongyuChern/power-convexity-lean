import PowerConvexity.Calculus.DoubleZeroAllDirectionsTwo
import PowerConvexity.Calculus.FrameReindexSecond
import PowerConvexity.Calculus.MatrixHessianZeroTwo

/-! # The entire second jet vanishes at a normalized semidefinite double zero

These are pointwise conclusions. They do not establish neighbourhood propagation.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem modifiedSchur_LM_diagonal_zero_at_double_zero_two
    {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ)))
    (k : Fin 2) : matrixL a b u (modifiedSchur a b u) x k k = 0 := by
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
  have hW := skewThirdHessian_zero_at_double_zero_two hU hu (a ∘ e) (b ∘ e)
    hρ hdet' hneg hpos' hx hM' hI' hD'
  have hl := modifiedSchur_double_zero_contraction_two hU hu (a ∘ e) (b ∘ e)
    hρ hdet' hneg hpos' hx hM' hI' hD'
  simp only [hW,Matrix.trace_zero,Complex.normSq_zero,Complex.ofReal_zero,
    Matrix.zero_apply,Finset.sum_const_zero,sub_zero] at hl
  have heM : modifiedSchur (a ∘ e) (b ∘ e) u =
      fun y => (modifiedSchur a b u y).submatrix e e :=
    funext fun y => modifiedSchur_frame_reindex a b e u y
  rw [heM,matrixL_frame_reindex] at hl
  simpa only [Matrix.submatrix_apply,e,Equiv.swap_apply_left] using hl

theorem modifiedSchur_diagonal_realHessian_zero_at_double_zero_two
    {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ)))
    (i : Fin 2) : realHessian (fun y => (modifiedSchur a b u y i i).re) x = 0 := by
  let M := modifiedSchur a b u
  have hc := modifiedSchur_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hpos x hx)
  have hzero : M x = 0 := modifiedSchur_double_zero_matrix a b hI hD
  have hr : (fun y => M y i i) =ᶠ[𝓝 x] fun y => ((M y i i).re:ℂ) := by
    filter_upwards [hM] with y hy
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hy.diag_nonneg (i := i))).2.symm
  have hm : IsLocalMin (fun y => (M y i i).re) x := by
    filter_upwards [hM] with y hy
    have hh := (Complex.nonneg_iff.mp (hy.diag_nonneg (i := i))).1
    simpa only [hzero,Matrix.zero_apply,Complex.zero_re] using hh
  apply realHessian_eq_zero_of_localMin_linearized_zero a b e he
    (Complex.reCLM.contDiff.contDiffAt.comp x (hc i i)) hm (hpos x hx)
  have hl := modifiedSchur_LM_diagonal_zero_at_double_zero_two hU hu a b
    hρ hdet hneg hpos hx hM hI hD i
  have hh : complexLinearized a b u (fun y => (M y i i).re) x =
      (matrixL a b u M x i i).re := by
    rw [matrixL_entry]
    unfold complexLinearized
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [dz_dz_congr_eventually hr (a p) (b p) (a q) (-b q)]
  change complexLinearized a b u (fun y => (M y i i).re) x = 0
  rw [hh]
  simpa only [M,hl,Complex.zero_re]

theorem modifiedSchur_all_real_imag_Hessians_zero_at_double_zero_two
    {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U)
    (hM : ∀ᶠ y in 𝓝 x, (modifiedSchur a b u y).PosSemidef)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun _ => (1:ℂ))) :
    ∀ i j, realHessian (fun y => (modifiedSchur a b u y i j).re) x = 0 ∧
      realHessian (fun y => (modifiedSchur a b u y i j).im) x = 0 := by
  have hc := modifiedSchur_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx))
    (hneg x hx) a b (hpos x hx)
  have hd := modifiedSchur_diagonal_realHessian_zero_at_double_zero_two
    hU hu a b e he hρ hdet hneg hpos hx hM hI hD
  apply matrix_real_imag_Hessians_zero_of_trace_Hessian_zero_two hc hM
    (modifiedSchur_double_zero_matrix a b hI hD)
  have hfun : (fun y => (modifiedSchur a b u y).trace.re) =
      fun y => (modifiedSchur a b u y 0 0).re+(modifiedSchur a b u y 1 1).re := by
    funext y
    simp [Matrix.trace,Matrix.diag,Fin.sum_univ_two]
  have hc0 : ContDiffAt ℝ 2
      (fun y => (modifiedSchur a b u y 0 0).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hc 0 0)
  have hc1 : ContDiffAt ℝ 2
      (fun y => (modifiedSchur a b u y 1 1).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hc 1 1)
  rw [hfun,realHessian_add hc0 hc1,hd 0,hd 1]
  ext v w
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,zero_add]

end PowerConvexity
