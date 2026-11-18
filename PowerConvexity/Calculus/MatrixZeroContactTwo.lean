import PowerConvexity.Calculus.ModifiedContactSpectrumTwo
import PowerConvexity.Calculus.ComplexGradientMinimum
import CHS.Calculus.SchurScalar

/-! # Actual first derivatives and elliptic contraction at a zero matrix contact

The positive semidefinite hypothesis holds on a neighbourhood. Positivity at
the single point would not imply any of the derivative conclusions below.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology BigOperators ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem matrixTwo_eq_zero_of_quadratic_zero (A : Matrix (Fin 2) (Fin 2) ℂ)
    (h : ∀ z : Fin 2 → ℂ, star z ⬝ᵥ A.mulVec z = 0) : A = 0 := by
  have h0 := h ![1,0]
  have h1 := h ![0,1]
  have hp := h ![1,1]
  have hi := h ![1,Complex.I]
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Complex.star_def] at h0 h1 hp hi
  rw [h0,h1] at hp hi
  simp only [zero_add,mul_zero,add_zero] at hp hi
  have hid : Complex.I*(A 0 1-A 1 0) = 0 := by linear_combination hi
  have hd := (mul_eq_zero.mp hid).resolve_left Complex.I_ne_zero
  have h01 : A 0 1 = 0 := by linear_combination (hp+hd)/2
  have h10 : A 1 0 = 0 := by linear_combination (hp-hd)/2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h0,h1,h01,h10]

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem matrixDZ_eq_zero_of_posSemidef_zero_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 1 (fun y => M y i j) x)
    (hpos : ∀ᶠ y in 𝓝 x, (M y).PosSemidef) (hzero : M x = 0) (a b : E) :
    matrixDZ a b M x = 0 := by
  apply matrixTwo_eq_zero_of_quadratic_zero
  intro z
  have hC : ContDiffAt ℝ 1 (matrixPair M z) x := matrixPair_contDiffAt hM z
  have hR : ContDiffAt ℝ 1 (fun y => (matrixPair M z y).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x hC
  have hr : matrixPair M z =ᶠ[𝓝 x] fun y => ((matrixPair M z y).re:ℂ) := by
    filter_upwards [hpos] with y hy
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hy.dotProduct_mulVec_nonneg z)).2.symm
  have hm : IsLocalMin (fun y => (matrixPair M z y).re) x := by
    filter_upwards [hpos] with y hy
    have hh := (Complex.nonneg_iff.mp (hy.dotProduct_mulVec_nonneg z)).1
    simpa only [matrixPair,hzero,Matrix.zero_mulVec,dotProduct_zero,Complex.zero_re] using hh
  change matrixPair (matrixDZ a b M) z x = 0
  rw [← dz_matrixPair (fun i j => (hM i j).differentiableAt (by norm_num)) z a b,
    dz_congr_nhds hr a b]
  exact dz_ofReal_eq_zero_of_fderiv_eq_zero (hR.differentiableAt (by norm_num)) hm.fderiv_eq_zero a b

theorem dz_dz_congr_eventually {f g : E → ℂ} {x : E}
    (h : f =ᶠ[𝓝 x] g) (a b c d : E) :
    dz c d (dz a b f) x = dz c d (dz a b g) x := by
  apply dz_congr_nhds _ c d
  exact h.eventually_nhds.mono fun _ hy => dz_congr_nhds hy a b

end General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem matrixL_diagonal_re_nonneg_of_posSemidef_zero_two
    {M : E → Matrix (Fin 2) (Fin 2) ℂ} {u : E → ℝ} {x : E}
    (hM : ∀ i j, ContDiffAt ℝ 2 (fun y => M y i j) x)
    (hpos : ∀ᶠ y in 𝓝 x, (M y).PosSemidef) (hzero : M x = 0)
    (a b : Fin 2 → E) (hA : (complexHessian a b u x).PosDef) (i : Fin 2) :
    0 ≤ (matrixL a b u M x i i).re := by
  have hR : ContDiffAt ℝ 2 (fun y => (M y i i).re) x :=
    Complex.reCLM.contDiff.contDiffAt.comp x (hM i i)
  have hr : (fun y => M y i i) =ᶠ[𝓝 x] fun y => ((M y i i).re:ℂ) := by
    filter_upwards [hpos] with y hy
    apply Complex.ext
    · rfl
    · exact (Complex.nonneg_iff.mp (hy.diag_nonneg (i := i))).2.symm
  have hm : IsLocalMin (fun y => (M y i i).re) x := by
    filter_upwards [hpos] with y hy
    have hh := (Complex.nonneg_iff.mp (hy.diag_nonneg (i := i))).1
    simpa only [hzero,Matrix.zero_apply,Complex.zero_re] using hh
  have he : (matrixL a b u M x i i).re =
      complexLinearized a b u (fun y => (M y i i).re) x := by
    rw [matrixL_entry]
    unfold complexLinearized
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [dz_dz_congr_eventually hr (a p) (b p) (a q) (-b q)]
  rw [he,complexLinearized_eq_real a b u hR]
  apply complexHessianContraction_positive a b hA.inv
  exact realHessian_nonneg_of_isLocalMin hR hm

end PowerConvexity
