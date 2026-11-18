import PowerConvexity.Calculus.RealHessianQuotient
import PowerConvexity.Calculus.ViscosityHarmonicClassicalConsistencyTwo
import PowerConvexity.Calculus.SmallContactGaussianBarrierTwo
import PowerConvexity.Analysis.PositiveHessianAnchor

/-! # The actual four-dimensional Poisson kernel.
All derivatives below are Fréchet derivatives of the displayed rational
function. The dimension-dependent cancellation is proved explicitly.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

def poissonKernelFour (ξ x : E) : ℝ := (1-‖x‖^2)/(‖x-ξ‖^2)^2

theorem poissonKernelFour_contDiffAt {ξ x : E} (hne : x ≠ ξ) (n : ℕ∞ω) :
    ContDiffAt ℝ n (poissonKernelFour ξ) x := by
  apply (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt).fun_div
    (((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).pow 2).contDiffAt
  exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))

theorem poissonKernelFour_joint_contDiffAt {z : E × E} (hne : z.1 ≠ z.2) (n : ℕ∞ω) :
    ContDiffAt ℝ n (fun p : E × E => poissonKernelFour p.2 p.1) z := by
  apply (contDiffAt_const.sub (contDiff_fst.norm_sq (𝕜 := ℝ)).contDiffAt).fun_div
    (((contDiff_fst.sub contDiff_snd).norm_sq (𝕜 := ℝ)).pow 2).contDiffAt
  exact pow_ne_zero _ (pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))

private theorem sqdist_fderiv (ξ x v : E) :
    fderiv ℝ (fun y : E => ‖y-ξ‖^2) x v = 2*inner ℝ (x-ξ) v := by
  have h := (((hasFDerivAt_id x).sub_const ξ).norm_sq).fderiv
  simpa only [id_eq,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat,innerSL_apply_apply] using
      congrArg (fun L => L v) h

private theorem sqdist_hessian (ξ x v w : E) :
    realHessian (fun y : E => ‖y-ξ‖^2) x v w = 2*inner ℝ v w := by
  rw [realHessian_norm_sub_sq]
  rfl

private theorem poisson_numerator_fderiv (x v : E) :
    fderiv ℝ (fun y : E => 1-‖y‖^2) x v = -2*inner ℝ x v := by
  rw [fderiv_fun_sub (differentiableAt_const (1:ℝ))
    ((contDiff_norm_sq ℝ (n := 2)).contDiffAt.differentiableAt (by norm_num)),
    fderiv_fun_const,fderiv_norm_sq_apply]
  simp only [ContinuousLinearMap.sub_apply,Pi.zero_apply,ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.smul_apply,innerSL_apply_apply,smul_eq_mul,nsmul_eq_mul,Nat.cast_ofNat]
  ring

private theorem poisson_numerator_hessian (x v w : E) :
    realHessian (fun y : E => 1-‖y‖^2) x v w = -2*inner ℝ v w := by
  rw [realHessian_sub_at contDiffAt_const (contDiff_norm_sq ℝ).contDiffAt]
  simp only [ContinuousLinearMap.sub_apply,realHessian_norm_square]
  simp [realHessian]
  <;> ring

private theorem poisson_denominator_fderiv (ξ x v : E) :
    fderiv ℝ (fun y : E => (‖y-ξ‖^2)^2) x v =
      4*‖x-ξ‖^2*inner ℝ (x-ξ) v := by
  have hd : DifferentiableAt ℝ (fun y : E => ‖y-ξ‖^2) x :=
    (((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ) (n := 2)).contDiffAt).differentiableAt (by norm_num)
  have he : (fun y : E => (‖y-ξ‖^2)^2) = (fun y : E => ‖y-ξ‖^2*‖y-ξ‖^2) := by
    funext y; exact pow_two _
  rw [he,fderiv_fun_mul hd hd]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  rw [sqdist_fderiv]
  ring

theorem poissonKernelFour_realHessian {ξ x : E} (hne : x ≠ ξ) (v w : E) :
    realHessian (poissonKernelFour ξ) x v w =
      -2*inner ℝ v w/(‖x-ξ‖^2)^2+
      8*(inner ℝ x v*inner ℝ (x-ξ) w+inner ℝ (x-ξ) v*inner ℝ x w)/(‖x-ξ‖^2)^3-
      4*(1-‖x‖^2)*inner ℝ v w/(‖x-ξ‖^2)^3+
      24*(1-‖x‖^2)*inner ℝ (x-ξ) v*inner ℝ (x-ξ) w/(‖x-ξ‖^2)^4 := by
  have hd : ContDiffAt ℝ 2 (fun y : E => ‖y-ξ‖^2) x :=
    ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ)).contDiffAt
  have hD : ‖x-ξ‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  have hG (v w : E) : realHessian (fun y : E => (‖y-ξ‖^2)^2) x v w =
      8*inner ℝ (x-ξ) v*inner ℝ (x-ξ) w+4*‖x-ξ‖^2*inner ℝ v w := by
    have he : (fun y : E => (‖y-ξ‖^2)^2) = (fun y : E => ‖y-ξ‖^2*‖y-ξ‖^2) := by
      funext y; exact pow_two _
    rw [he,realHessian_mul_real_at hd hd]
    simp only [sqdist_hessian,sqdist_fderiv]
    ring
  unfold poissonKernelFour
  rw [realHessian_div_real_at (contDiffAt_const.sub (contDiff_norm_sq ℝ).contDiffAt)
    (hd.pow 2) (pow_ne_zero _ hD),poisson_numerator_hessian,
    poisson_numerator_fderiv,poisson_numerator_fderiv,
    poisson_denominator_fderiv,poisson_denominator_fderiv,hG]
  field_simp [hD]
  <;> ring

theorem block_inner_mul_sum_two (v w : E) :
    (∑ i : J, inner ℝ v (Sum.elim realDirections imagDirections i)*
      inner ℝ w (Sum.elim realDirections imagDirections i)) = inner ℝ v w := by
  simp only [blockDirection_eq_single,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul]
  calc
    _ = ∑ i : Fin (2+2), v i*w i :=
      Equiv.sum_comp finSumFinEquiv (fun i : Fin (2+2) => v i*w i)
    _ = inner ℝ v w := by simp [PiLp.inner_apply,mul_comm]

theorem poissonKernelFour_trace {ξ x : E} (hne : x ≠ ξ) :
    (realBlockHessian realDirections imagDirections (poissonKernelFour ξ) x).trace =
      8*(1-‖ξ‖^2)/(‖x-ξ‖^2)^3 := by
  have hD : ‖x-ξ‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  have hunit (i : J) : inner ℝ (Sum.elim realDirections imagDirections i)
      (Sum.elim realDirections imagDirections i) = 1 := by
    rw [real_inner_self_eq_norm_sq,blockDirection_eq_single]
    simp
  simp only [Matrix.trace,Matrix.diag_apply,realBlockHessian,
    poissonKernelFour_realHessian hne,hunit]
  simp_rw [show ∀ i : J,
    24*(1-‖x‖^2)*inner ℝ (x-ξ) (Sum.elim realDirections imagDirections i)*
      inner ℝ (x-ξ) (Sum.elim realDirections imagDirections i) =
        24*(1-‖x‖^2)*(inner ℝ (x-ξ) (Sum.elim realDirections imagDirections i))^2 by
      intro i; ring]
  simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_div,
    ← Finset.mul_sum,Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,
    nsmul_eq_mul,block_inner_square_sum_two,block_inner_mul_sum_two]
  simp only [inner_sub_left,inner_sub_right,real_inner_self_eq_norm_sq,real_inner_comm]
  field_simp [hD]
  <;> rw [norm_sub_sq_real]
  <;> simp only [real_inner_comm ξ x]
  <;> ring

theorem poissonKernelFour_harmonic_on_unit_ball {ξ : E} (hξ : ‖ξ‖ = 1) :
    InnerProductSpace.HarmonicOnNhd (poissonKernelFour ξ) (ball 0 1) := by
  intro x hx
  have hne : x ≠ ξ := by
    intro he; subst x
    simpa [mem_ball,dist_zero_right,hξ] using hx
  refine ⟨poissonKernelFour_contDiffAt hne 2,?_⟩
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  have hney : y ≠ ξ := by
    intro he; subst y
    simpa [mem_ball,dist_zero_right,hξ] using hy
  change Laplacian.laplacian (poissonKernelFour ξ) y = 0
  rw [← actual_block_trace_eq_laplacian_two,poissonKernelFour_trace hney,hξ]
  norm_num

theorem poissonKernelFour_nonneg_on_unit_ball {ξ x : E} (hx : x ∈ closedBall 0 1) :
    0 ≤ poissonKernelFour ξ x := by
  apply div_nonneg _ (sq_nonneg _)
  have hx' : ‖x‖ ≤ 1 := by simpa only [mem_closedBall,dist_zero_right] using hx
  nlinarith [norm_nonneg x]

theorem poissonKernelFour_at_zero {ξ : E} (hξ : ‖ξ‖ = 1) :
    poissonKernelFour ξ 0 = 1 := by
  simp [poissonKernelFour,hξ]

end PowerConvexity
