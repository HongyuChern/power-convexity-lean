import PowerConvexity.Calculus.MinkowskiJointBoundaryStrictSubsolutionTwo
import PowerConvexity.Calculus.JointStrictPshExtensionTwo
import PowerConvexity.Calculus.JointClosureSubsolutionScalingTwo
import CHS.Calculus.ClosureRegularity

/-! # One actual jointly C4 global strict-subsolution family

The original endpoint data produce a boundary family. A full-germ-preserving
base extension and the actual correction g(x)+rho(t,x)-rho(s,x) yield strict
psh on every nearby closure. One final scaling is selected on the compact
actual parameter-closure graph, before the nearby parameter.
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

theorem classicalDirichlet_minkowski_exists_joint_global_strict_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ w : ℝ × E → ℝ,
      ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)) ∧
      ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
        ContDiff ℝ 4 (fun x => w (t,x)) ∧ Nonempty (ClosureC2Jet (fun x => w (t,x)) (V t)) ∧
        (∀ x ∈ frontier (V t), w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0)) ∧
        ∀ x ∈ closure (V t),
          (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef ∧
          (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d0,hd0,rho,hrho,hrhodata⟩ :=
    classicalDirichlet_minkowski_exists_joint_boundary_strict_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  have hVo : IsOpen (V s) :=
    (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
      (continuous_const.prodMk continuous_id)
  have hbase := hrhodata s (mem_closedBall_self hd0.le) ⟨hs.le,hs1⟩
  obtain ⟨g,hg,hgerm,hgp⟩ := global_C4_strictPsh_extension_preserving_boundary_germs_two
    e hab hVo hVK hbase.1 (fun x hx => (hbase.2 x hx).1)
    (fun x hx => (hbase.2 x hx).2.2.1) (fun x hx => (hbase.2 x hx).2.2.2.1)
  have hclosure : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} :=
    minkowskiDomain_real_closure_parameterGraph_isCompact hK hBK
  have hfrontier : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} :=
    minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK
  obtain ⟨d1,hd1,F,hF,hFdata⟩ := joint_strictPsh_extension_from_base_germs_two e
    (by positivity : 0 < 2*d0) hclosure hfrontier hrho hg hgerm hgp
  let d := min (d0/2) (d1/2)
  have hd : 0 < d := lt_min (half_pos hd0) (half_pos hd1)
  have hdd0 : d ≤ d0 := (min_le_left (d0/2) (d1/2)).trans (by linarith)
  have hdd1 : d ≤ d1 := (min_le_right (d0/2) (d1/2)).trans (by linarith)
  have hFjoint : ContDiffOn ℝ 4 F (ball s (2*d) ×ˢ (univ : Set E)) :=
    hF.mono (Set.prod_mono (ball_subset_ball (by linarith : 2*d ≤ 2*d1)) Subset.rfl)
  have hFpos (t : ℝ) (ht : t ∈ closedBall s d) (hI : t ∈ Icc (0 : ℝ) 1) :=
    (hFdata t (closedBall_subset_closedBall hdd1 ht) hI).2.2
  obtain ⟨c,hc1,hcpos⟩ := exists_joint_uniform_positive_scaling_on_closures_two
    e (fun j => Complex.I • e j) hd hclosure hFjoint hFpos
  have hc : 0 < c := lt_trans (by norm_num) hc1
  let w : ℝ × E → ℝ := fun q => c*F q
  refine ⟨d,hd,w,contDiffOn_const.mul hFjoint,?_⟩
  intro t ht hI
  have hFt := (hFdata t (closedBall_subset_closedBall hdd1 ht) hI).1
  have hwt : ContDiff ℝ 4 (fun x => w (t,x)) := contDiff_const.mul hFt
  have hwt2 : ContDiff ℝ 2 (fun x => w (t,x)) := hwt.of_le (by norm_num)
  have hJ : Nonempty (ClosureC2Jet (fun x => w (t,x)) (V t)) :=
    (c2OnClosure_of_neighborhood isOpen_univ (subset_univ _) hwt2.contDiffOn).2
  refine ⟨hwt,hJ,?_,hcpos t ht hI⟩
  intro x hx
  have he := (hFdata t (closedBall_subset_closedBall hdd1 ht) hI).2.1 x hx
  have hrd := (hrhodata t (closedBall_subset_closedBall hdd0 ht) hI).2 x hx
  have hFx : F (t,x) = 0 := he.self_of_nhds.trans hrd.1
  have hDF : fderiv ℝ (fun y => F (t,y)) x ≠ 0 := by
    rw [he.fderiv_eq]
    exact hrd.2.1
  refine ⟨by simp only [w,hFx,mul_zero],?_,?_⟩
  · change fderiv ℝ (fun y => c*F (t,y)) x ≠ 0
    rw [fderiv_const_mul (hFt.contDiffAt.differentiableAt (by norm_num))]
    exact smul_ne_zero hc.ne' hDF
  · filter_upwards [he,hrd.2.2.1] with z hez hdefz
    rw [hdefz]
    change rho (t,z) < 0 ↔ c*F (t,z) < 0
    have hez' : F (t,z) = rho (t,z) := hez
    rw [hez']
    constructor
    · exact fun hn => mul_neg_of_pos_of_neg hc hn
    · intro hn
      by_contra! hnn
      exact (not_lt_of_ge (mul_nonneg hc.le hnn)) hn

end PowerConvexity
