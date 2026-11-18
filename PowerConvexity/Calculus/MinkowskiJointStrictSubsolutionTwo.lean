import PowerConvexity.Calculus.MinkowskiJointStrictPshTwo
import PowerConvexity.Calculus.ParameterStrictSubsolutionScalingTwo
import PowerConvexity.Calculus.AffineBoundaryJetQuadraticBoundTwo

/-! # Actual joint local zero-boundary strict subsolutions on Minkowski domains

One fixed positive scaling gives determinant greater than one on one actual
parameter-space neighborhood. Actual vanishing on each moving boundary is
proved from the common defining equivalence. No det=1 solution is selected.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem classicalDirichlet_minkowski_exists_joint_local_strict_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {x : E} (hx : x ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ w : ℝ × E → ℝ, ContDiffAt ℝ ∞ w (s,x) ∧ w (s,x) = 0 ∧
      (∀ᶠ p in 𝓝 (s,x),
        ContDiffAt ℝ 4 (fun y => w (p.1,y)) p.2 ∧
        fderiv ℝ (fun y => w (p.1,y)) p.2 ≠ 0 ∧
        (complexHessian e (fun j => Complex.I • e j) (fun y => w (p.1,y)) p.2).PosDef ∧
        (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (p.1,y)) p.2).det ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ w p < 0) ∧
          (p.2 ∈ frontier (minkowskiDomain p.1 U (ball (0 : E) R)) → w p = 0))) := by
  obtain ⟨rho,hrho,hrho0,hn⟩ :=
    classicalDirichlet_minkowski_exists_joint_strictPsh_defining_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR hx
  obtain ⟨c,hc,hscaled⟩ := exists_parameter_positive_scaling_det_gt_one_two
    e (fun j => Complex.I • e j) ((contDiffAt_infty.mp hrho) 2)
    (hn.mono (fun _ hp => hp.2.2.1))
  let w : ℝ × E → ℝ := fun p => c*rho p
  have hw : ContDiffAt ℝ ∞ w (s,x) := contDiffAt_const.mul hrho
  have hwdef : ∀ᶠ p in 𝓝 (s,x), p.1 ∈ Icc (0 : ℝ) 1 →
      (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ w p < 0) := by
    filter_upwards [hn] with p hp
    intro hpI
    rw [hp.2.2.2 hpI]
    change rho p < 0 ↔ c*rho p < 0
    constructor
    · exact mul_neg_of_pos_of_neg hc
    · intro hh
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg hc.le hnn)) hh
  have hpositive : ∀ᶠ p : ℝ × E in 𝓝 (s,x), 0 < p.1 :=
    continuousAt_fst.tendsto.eventually (lt_mem_nhds hs)
  refine ⟨w,hw,by simp only [w,hrho0,mul_zero],?_⟩
  filter_upwards [hn,hscaled,hwdef,hwdef.eventually_nhds,hpositive]
    with p hp hscl hdefp hdefnp hpt
  have hreg : ContDiffAt ℝ 4 (fun y => w (p.1,y)) p.2 := contDiffAt_const.mul hp.1
  have hDw : fderiv ℝ (fun y => w (p.1,y)) p.2 ≠ 0 := by
    change fderiv ℝ (fun y => c*rho (p.1,y)) p.2 ≠ 0
    rw [fderiv_const_mul (hp.1.differentiableAt (by norm_num))]
    exact smul_ne_zero hc.ne' hp.2.1
  refine ⟨hreg,hDw,hscl.1,hscl.2,?_⟩
  intro hpI
  refine ⟨hdefp hpI,?_⟩
  intro hfront
  have hVo : IsOpen (minkowskiDomain p.1 U (ball (0 : E) R)) := by
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ hpt.ne').add_right
  have hlocal : ∀ᶠ y in 𝓝 p.2,
      y ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ w (p.1,y) < 0 := by
    have hin : Tendsto (fun y : E => (p.1,y)) (𝓝 p.2) (𝓝 p) :=
      (continuousAt_const.prodMk continuousAt_id).tendsto
    filter_upwards [hin.eventually hdefnp] with y hy
    exact hy hpI
  exact local_defining_function_zero_at_frontier hVo hfront hreg.continuousAt hlocal

theorem classicalDirichlet_minkowski_exists_joint_regular_ball_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R)
    {x : E} (hx : x ∈ frontier (minkowskiDomain s U (ball (0 : E) R))) :
    ∃ w : ℝ × E → ℝ, w (s,x) = 0 ∧ ∃ r > 0,
      ContDiffOn ℝ 4 w (ball (s,x) r) ∧
      ∀ p ∈ ball (s,x) r,
        ContDiffAt ℝ 4 (fun y => w (p.1,y)) p.2 ∧
        fderiv ℝ (fun y => w (p.1,y)) p.2 ≠ 0 ∧
        (complexHessian e (fun j => Complex.I • e j) (fun y => w (p.1,y)) p.2).PosDef ∧
        (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (p.1,y)) p.2).det ∧
        (p.1 ∈ Icc (0 : ℝ) 1 →
          (p.2 ∈ minkowskiDomain p.1 U (ball (0 : E) R) ↔ w p < 0) ∧
          (p.2 ∈ frontier (minkowskiDomain p.1 U (ball (0 : E) R)) → w p = 0)) := by
  obtain ⟨w,hw,hw0,hn⟩ := classicalDirichlet_minkowski_exists_joint_local_strict_subsolution_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR hx
  have hw4 : ContDiffAt ℝ 4 w (s,x) := (contDiffAt_infty.mp hw) 4
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp ((hw4.eventually (by norm_num)).and hn)
  refine ⟨w,hw0,r,hr,?_,?_⟩
  · intro p hp
    exact (hball hp).1.contDiffWithinAt
  · intro p hp
    exact (hball hp).2

end PowerConvexity
