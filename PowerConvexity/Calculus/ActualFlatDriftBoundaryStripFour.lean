import PowerConvexity.Calculus.ActualFlatDriftQuadraticBarrierFour
import PowerConvexity.Calculus.ActualFlatBoundaryStripBoundFour
import PowerConvexity.Analysis.ActualFlatTestH01Four
import CHS.Calculus.AffinePullback

/-! # Uniform linear vanishing throughout the actual flat boundary strip
The normal barrier is translated to the actual orthogonal projection of each
point and applied on a physical half ball of radius one half.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_flat_drift_boundary_strip_bound_four
    {N : E} (hN : ‖N‖=1) {lam T F : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) (hF : 0 ≤ F)
    (L : E → Bilin →ₗ[ℝ] ℝ)
    (hL : ∀ x ∈ actualFlatUpperBallFour N 1, HessianPositive (L x))
    (htrace : ∀ x ∈ actualFlatUpperBallFour N 1, L x (realInnerForm : Bilin) ≤ T)
    (hnormal : ∀ x ∈ actualFlatUpperBallFour N 1, lam ≤ L x (realRankOneForm N))
    (b : E → E)
    (hb : ∀ x ∈ actualFlatUpperBallFour N 1,
      (3*((T+F/4+1)/lam)+3)*‖b x‖ ≤ 2)
    {u : E → ℝ} (huC : ContinuousOn u (actualFlatClosedUpperBallFour N 1))
    (hu2 : ContDiffOn ℝ 2 u (actualFlatUpperBallFour N 1))
    (hLu : ∀ x ∈ actualFlatUpperBallFour N 1, |L x (realHessian u x)+fderiv ℝ u x (b x)| ≤ F)
    (hu0 : ∀ x ∈ closedBall (0 : E) 1, inner ℝ N x=0 → u x=0)
    (hub : ∀ x ∈ actualFlatClosedUpperBallFour N 1, |u x| ≤ 1) :
    ∀ x ∈ actualFlatClosedUpperBallFour N (1/2),
      |u x| ≤ (2*((T+F/4+1)/lam+2))*inner ℝ N x := by
  intro x hx
  let x₀ := x-(inner ℝ N x) • N
  have hproj := actual_flat_projection_geometry_four hN x
  have hxnorm : ‖x‖ ≤ 1/2 := by simpa only [mem_closedBall,dist_zero_right] using hx.1
  have hx₀ : ‖x₀‖ ≤ 1/2 := hproj.2.trans hxnorm
  have hNx₀ : inner ℝ N x₀=0 := hproj.1
  let P : E → E := fun y => x₀+(1/2 : ℝ) • y
  have hmap := actual_flat_half_patch_maps_four hx₀ hproj.1
  have hPC : ContDiff ℝ 2 P := contDiff_const.add (contDiff_id.const_smul (1/2 : ℝ))
  let v : E → ℝ := fun y => u (P y)
  have hv2 : ContDiffOn ℝ 2 v (actualFlatUpperBallFour N 1) :=
    hu2.comp hPC.contDiffOn hmap.2
  have hvC : ContinuousOn v (actualFlatClosedUpperBallFour N 1) :=
    huC.comp hPC.continuous.continuousOn hmap.1
  have hH (y : E) (hy : y ∈ actualFlatUpperBallFour N 1) :
      realHessian v y = (1/4 : ℝ) • realHessian u (P y) := by
    ext a b
    have hh := realHessian_comp_affine ((1/2 : ℝ) • ContinuousLinearMap.id ℝ E) x₀
      (hu2.contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds (hmap.2 hy))) a b
    change realHessian (fun z => u (x₀+(1/2 : ℝ) • z)) y a b = _
    simp only [_root_.smul_apply,ContinuousLinearMap.id_apply] at hh
    rw [hh]
    simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    ring
  have hD (y : E) (hy : y ∈ actualFlatUpperBallFour N 1) :
      fderiv ℝ v y=(1/2 : ℝ) • fderiv ℝ u (P y) := by
    have hpD := (((1/2 : ℝ) • ContinuousLinearMap.id ℝ E).hasFDerivAt (x := y)).const_add x₀
    have huD := ((hu2.contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds (hmap.2 hy))).differentiableAt (by norm_num)).hasFDerivAt.comp y hpD
    apply ContinuousLinearMap.ext
    intro w
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L w) huD.fderiv
    simpa only [v,P,Function.comp_def,ContinuousLinearMap.comp_apply,_root_.smul_apply,
      ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] using hh
  have hvLu (y : E) (hy : y ∈ actualFlatUpperBallFour N 1) :
      |L (P y) (realHessian v y)+fderiv ℝ v y ((1/2 : ℝ) • b (P y))| ≤ F/4 := by
    rw [hH y hy,hD y hy,map_smul,smul_eq_mul,_root_.smul_apply,map_smul,smul_eq_mul]
    simp only [smul_eq_mul,mul_assoc]
    have he : (1/4 : ℝ)*L (P y) (realHessian u (P y))+
        (1/2 : ℝ)*((1/2 : ℝ)*fderiv ℝ u (P y) (b (P y))) =
        (1/4 : ℝ)*(L (P y) (realHessian u (P y))+fderiv ℝ u (P y) (b (P y))) := by ring
    rw [he,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<1/4)]
    nlinarith [hLu (P y) (hmap.2 hy)]
  have hv0 (y : E) (hy : y ∈ closedBall (0 : E) 1) (hy0 : inner ℝ N y=0) : v y=0 := by
    have hPy := hmap.1 (show y ∈ actualFlatClosedUpperBallFour N 1 from ⟨hy,hy0.ge⟩)
    apply hu0 (P y) hPy.1
    dsimp only [P]
    simp only [inner_add_right,hNx₀,inner_smul_right,hy0,mul_zero,add_zero]
  have hb := actual_flat_drift_normal_boundary_bound_four hN hlam hT
    (div_nonneg hF (by norm_num)) (fun y => L (P y))
    (fun y hy => hL (P y) (hmap.2 hy))
    (fun y hy => htrace (P y) (hmap.2 hy))
    (fun y hy => hnormal (P y) (hmap.2 hy)) (fun y => (1/2 : ℝ) • b (P y))
    (by
      intro y hy
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
      nlinarith [hb (P y) (hmap.2 hy)]) hvC hv2 hvLu hv0
    (fun y hy => hub (P y) (hmap.1 hy))
  let d := 2*inner ℝ N x
  have hd : d ∈ Icc (0 : ℝ) 1 := by
    have hi : inner ℝ N x ≤ ‖x‖ := by simpa only [hN,one_mul] using real_inner_le_norm N x
    exact ⟨mul_nonneg (by norm_num) hx.2,by dsimp only [d]; linarith⟩
  have he : P (d • N)=x := by
    dsimp only [P,x₀,d]
    rw [smul_smul,show (1/2 : ℝ)*(2*inner ℝ N x)=inner ℝ N x by ring,sub_add_cancel]
  have hh := hb d hd
  change |u (P (d • N))| ≤ _ at hh
  rw [he] at hh
  simpa only [d,mul_assoc,mul_left_comm,mul_comm] using hh

end PowerConvexity
