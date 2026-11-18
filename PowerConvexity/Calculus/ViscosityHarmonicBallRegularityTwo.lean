import PowerConvexity.Calculus.PoissonExtensionFour
import CHS.Calculus.AffinePullback

/-! # Actual harmonic replacement on arbitrary positive-radius balls.
The dilation, boundary trace, continuity and actual Hessian scaling are
all checked before comparison is applied to the original viscosity function.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "S" => sphere (0 : E) 1

theorem actual_C2_block_trace_affine_scalar_two {u : E → ℝ} {c x : E} {r : ℝ}
    (hu : ContDiffAt ℝ 2 u (c+r • x)) :
    (realBlockHessian realDirections imagDirections (fun y => u (c+r • y)) x).trace =
      r^2*(realBlockHessian realDirections imagDirections u (c+r • x)).trace := by
  have hH (v w : E) : realHessian (fun y => u (c+r • y)) x v w =
      r^2*realHessian u (c+r • x) v w := by
    change realHessian (fun y => u (c+(r • ContinuousLinearMap.id ℝ E) y)) x v w = _
    rw [realHessian_comp_affine (r • ContinuousLinearMap.id ℝ E) c hu]
    simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply,map_smul,_root_.smul_apply,smul_eq_mul]
    ring
  simp only [Matrix.trace,Matrix.diag_apply,realBlockHessian,hH,← Finset.mul_sum]

theorem classical_harmonic_affine_scalar_pullback_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : InnerProductSpace.HarmonicOnNhd u U) (c : E) (r : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun y => u (c+r • y))
      ((fun y : E => c+r • y) ⁻¹' U) := by
  have hmap : ContDiff ℝ 2 (fun y : E => c+r • y) := by fun_prop
  have hopen := hU.preimage hmap.continuous
  intro x hx
  refine ⟨(hu (c+r • x) hx).1.comp x hmap.contDiffAt,?_⟩
  filter_upwards [hopen.mem_nhds hx] with y hy
  change Laplacian.laplacian (fun z => u (c+r • z)) y = 0
  rw [← actual_block_trace_eq_laplacian_two,
    actual_C2_block_trace_affine_scalar_two (hu (c+r • y) hy).1,
    actual_classical_harmonic_trace_zero_two hu hy,mul_zero]

def ballNormalizationFour (c : E) (R : ℝ) (x : E) : E := R⁻¹ • (x-c)

theorem ballNormalizationFour_contDiff (c : E) (R : ℝ) (n : ℕ∞ω) :
    ContDiff ℝ n (ballNormalizationFour c R) := by
  unfold ballNormalizationFour
  fun_prop

theorem ballNormalizationFour_norm {R : ℝ} (hR : 0 < R) (c x : E) :
    ‖ballNormalizationFour c R x‖ = dist x c/R := by
  simp only [ballNormalizationFour,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),
    dist_eq_norm,div_eq_mul_inv,mul_comm]

theorem ballNormalizationFour_mem_ball_iff {R : ℝ} (hR : 0 < R) (c x : E) :
    ballNormalizationFour c R x ∈ ball (0 : E) 1 ↔ x ∈ ball c R := by
  rw [mem_ball,dist_zero_right,ballNormalizationFour_norm hR,mem_ball]
  exact div_lt_one hR

theorem ballNormalizationFour_mem_closedBall_iff {R : ℝ} (hR : 0 < R) (c x : E) :
    ballNormalizationFour c R x ∈ closedBall (0 : E) 1 ↔ x ∈ closedBall c R := by
  rw [mem_closedBall,dist_zero_right,ballNormalizationFour_norm hR,mem_closedBall]
  exact div_le_one hR

theorem ballNormalizationFour_mem_sphere_iff {R : ℝ} (hR : 0 < R) (c x : E) :
    ballNormalizationFour c R x ∈ sphere (0 : E) 1 ↔ x ∈ sphere c R := by
  rw [mem_sphere,dist_zero_right,ballNormalizationFour_norm hR,mem_sphere]
  exact div_eq_one_iff_eq hR.ne'

theorem ballNormalizationFour_inverse {R : ℝ} (hR : R ≠ 0) (c x : E) :
    c+R • ballNormalizationFour c R x = x := by
  simp [ballNormalizationFour,smul_smul,hR]

theorem ballNormalizationFour_after_dilation {R : ℝ} (hR : R ≠ 0) (c z : E) :
    ballNormalizationFour c R (c+R • z) = z := by
  simp [ballNormalizationFour,smul_smul,hR]

theorem classical_harmonic_ball_normalization_two {u : E → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u (ball (0 : E) 1))
    {R : ℝ} (hR : 0 < R) (c : E) :
    InnerProductSpace.HarmonicOnNhd (fun x => u (ballNormalizationFour c R x)) (ball c R) := by
  have he : (fun x : E => -(R⁻¹ • c)+R⁻¹ • x) = ballNormalizationFour c R := by
    funext x
    simp [ballNormalizationFour,smul_sub,sub_eq_add_neg,add_comm]
  have h := classical_harmonic_affine_scalar_pullback_two isOpen_ball hu (-(R⁻¹ • c)) R⁻¹
  change InnerProductSpace.HarmonicOnNhd (u ∘ (fun x : E => -(R⁻¹ • c)+R⁻¹ • x))
    ((fun x : E => -(R⁻¹ • c)+R⁻¹ • x) ⁻¹' ball (0 : E) 1) at h
  rw [he] at h
  have hpre : ballNormalizationFour c R ⁻¹' ball (0 : E) 1 = ball c R := by
    ext x
    exact ballNormalizationFour_mem_ball_iff hR c x
  simpa only [hpre,Function.comp_def] using h

theorem viscosity_harmonic_C2_on_ball_two {g : E → ℝ} {c : E} {R : ℝ}
    (hR : 0 < R) (hgc : ContinuousOn g (closedBall c R))
    (hg : IsViscosityHarmonicTwo g (ball c R)) :
    ContDiffOn ℝ 2 g (ball c R) := by
  let f : S → ℝ := fun ξ => g (c+R • (ξ : E))
  have hmap (ξ : S) : c+R • (ξ : E) ∈ closedBall c R := by
    have hn : ‖(ξ : E)‖ = 1 := by simpa only [mem_sphere,dist_zero_right] using ξ.property
    simp [mem_closedBall,dist_eq_norm,norm_smul,abs_of_pos hR,hn]
  have hf : Continuous f := by
    apply continuousOn_univ.mp
    have hcmap : Continuous (fun ξ : S => c+R • (ξ : E)) := by fun_prop
    exact hgc.comp hcmap.continuousOn (fun ξ _ => hmap ξ)
  let p : E → ℝ := fun x => unitPoissonExtensionFour f (ballNormalizationFour c R x)
  have hpH : InnerProductSpace.HarmonicOnNhd p (ball c R) :=
    classical_harmonic_ball_normalization_two (unitPoissonExtensionFour_harmonic hf) hR c
  have hpC : ContinuousOn p (closedBall c R) :=
    (unitPoissonExtensionFour_continuousOn_closedBall hf).comp
      (ballNormalizationFour_contDiff c R 0).continuous.continuousOn
      (fun x hx => (ballNormalizationFour_mem_closedBall_iff hR c x).mpr hx)
  have hb (x : E) (hx : x ∈ sphere c R) : g x = p x := by
    let ξ : S := ⟨ballNormalizationFour c R x,(ballNormalizationFour_mem_sphere_iff hR c x).mpr hx⟩
    have he := unitPoissonExtensionFour_on_sphere f ξ
    change p x = g (c+R • ballNormalizationFour c R x) at he
    rw [ballNormalizationFour_inverse hR.ne'] at he
    exact he.symm
  have heq := viscosity_harmonic_eq_classical_on_ball_two hR hgc hg hpC hpH hb
  apply hpH.contDiffOn.congr
  intro x hx
  exact heq (ball_subset_closedBall hx)

theorem IsViscosityHarmonicTwo.contDiffOn_two {g : E → ℝ} {U : Set E}
    (hg : IsViscosityHarmonicTwo g U) (hU : IsOpen U) : ContDiffOn ℝ 2 g U := by
  intro x hx
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hK : closedBall x (r/2) ⊆ U := by
    intro y hy
    exact hrU (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by linarith)))
  have hB : ball x (r/2) ⊆ U := fun y hy => hK (ball_subset_closedBall hy)
  have hgv : IsViscosityHarmonicTwo g (ball x (r/2)) :=
    ⟨hg.1.mono hB,fun y hy => hg.2 y (hB hy)⟩
  exact ((viscosity_harmonic_C2_on_ball_two (half_pos hr) (hg.1.mono hK) hgv).contDiffAt
    (isOpen_ball.mem_nhds (mem_ball_self (half_pos hr)))).contDiffWithinAt

theorem IsViscosityHarmonicTwo.classical_harmonic_two {g : E → ℝ} {U : Set E}
    (hg : IsViscosityHarmonicTwo g U) (hU : IsOpen U) :
    InnerProductSpace.HarmonicOnNhd g U :=
  hg.classical_harmonic_of_C2 hU (hg.contDiffOn_two hU)

end PowerConvexity
