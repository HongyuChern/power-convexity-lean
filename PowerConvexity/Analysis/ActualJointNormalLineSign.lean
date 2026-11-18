import PowerConvexity.Calculus.FiniteParameterFiberDerivative
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # One actual normal-line sign neighbourhood for nearby parameters

The strict derivative is used for the joint function. The two comparison
points have the same parameter, so their difference has zero parameter
component. The normal is allowed to vary with the parameter.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {P E : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem actual_joint_normal_line_sign
    {s : P} {N : P → E} {f : P × E → ℝ}
    (hN : ContinuousAt N s) (hf : ContDiffAt ℝ 1 f (s,0))
    (hDN : fderiv ℝ (fun y => f (s,y)) 0 (N s)=1) :
    ∃ V : Set (P × E), IsOpen V ∧ (s,(0 : E)) ∈ V ∧
      ∀ p : P, ‖N p‖=1 → ∀ y : E, (p,y) ∈ V → ∀ z : E, (p,z) ∈ V →
      ∀ t : ℝ, y-z=t • N p → f (p,z)=0 →
        (0 < f (p,y) ↔ 0 < t) ∧ (f (p,y)=0 ↔ t=0) ∧
        (f (p,y) < 0 ↔ t < 0) := by
  let D := fderiv ℝ f (s,0)
  let mu : P → ℝ := fun p => D (0,N p)
  have hmu : ContinuousAt mu s := D.continuous.continuousAt.comp
    (continuousAt_const.prodMk hN)
  have hmus : mu s=1 := by
    rw [finite_parameter_fiber_fderiv_eq (hf.differentiableAt (by norm_num))] at hDN
    exact hDN
  have hmnear : ∀ᶠ p in 𝓝 s, |mu p-1| < (1/4 : ℝ) := by
    have hh := hmu.eventually (Metric.ball_mem_nhds (mu s) (by norm_num : (0 : ℝ) < 1/4))
    simpa only [mem_ball,Real.dist_eq,hmus] using hh
  obtain ⟨W,hW,hWo,hsW⟩ := _root_.mem_nhds_iff.mp hmnear
  have hsmall := (hf.hasStrictFDerivAt (by norm_num)).isLittleO.bound
    (by norm_num : (0 : ℝ) < 1/4)
  obtain ⟨V0,hVo,h0V,hVV⟩ := exists_nhds_square hsmall
  let V := V0 ∩ Prod.fst ⁻¹' W
  refine ⟨V,hVo.inter (hWo.preimage continuous_fst),⟨h0V,hsW⟩,?_⟩
  intro p hp y hy z hz t hdiff hfz
  have hd : (p,y)-(p,z)=(0,t • N p) := by
    ext
    · simp
    · exact hdiff
  have hh := hVV (show ((p,y),(p,z)) ∈ V0 ×ˢ V0 from ⟨hy.1,hz.1⟩)
  change |f (p,y)-f (p,z)-D ((p,y)-(p,z))| ≤ (1/4 : ℝ)*‖(p,y)-(p,z)‖ at hh
  have hprod : (0,t • N p)=t • ((0 : P),N p) := by simp
  have hnorm : ‖((0 : P),N p)‖=1 := by simp only [Prod.norm_def,norm_zero,hp,max_eq_right zero_le_one]
  have herr : |f (p,y)-t*mu p| ≤ (1/4 : ℝ)*|t| := by
    simpa only [hd,hprod,hfz,sub_zero,map_smul,smul_eq_mul,norm_smul,
      Real.norm_eq_abs,hnorm,mul_one,mu] using hh
  have hmd : |mu p-1| ≤ (1/4 : ℝ) := (hW hy.2).le
  have hmt : |t*mu p-t| ≤ |t| *(1/4 : ℝ) := by
    calc
      |t*mu p-t|=|t*(mu p-1)| := by congr 1; ring
      _=|t| *|mu p-1| := abs_mul _ _
      _≤|t| *(1/4 : ℝ) := mul_le_mul_of_nonneg_left hmd (abs_nonneg t)
  have herror : |f (p,y)-t| ≤ (1/2 : ℝ)*|t| := by
    calc
      |f (p,y)-t|≤|f (p,y)-t*mu p|+|t*mu p-t| := abs_sub_le _ _ _
      _≤(1/4 : ℝ)*|t|+|t| *(1/4 : ℝ) := add_le_add herr hmt
      _=(1/2 : ℝ)*|t| := by ring
  have hlow := (abs_le.mp herror).1
  have hhigh := (abs_le.mp herror).2
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro hypos
      by_contra ht
      have htn : t ≤ 0 := le_of_not_gt ht
      rw [abs_of_nonpos htn] at hhigh
      linarith
    · intro ht
      rw [abs_of_pos ht] at hlow
      linarith
  · constructor
    · intro hyzero
      rw [hyzero,zero_sub,abs_neg] at herror
      have hzabs : |t|=0 := by linarith [abs_nonneg t]
      exact abs_eq_zero.mp hzabs
    · intro ht
      subst t
      have hh : |f (p,y)| ≤ 0 := by simpa only [sub_zero,abs_zero,mul_zero] using herror
      exact abs_eq_zero.mp (le_antisymm hh (abs_nonneg _))
  · constructor
    · intro hyneg
      by_contra ht
      have htn : 0 ≤ t := le_of_not_gt ht
      rw [abs_of_nonneg htn] at hlow
      linarith
    · intro ht
      rw [abs_of_neg ht] at hhigh
      linarith

end PowerConvexity
