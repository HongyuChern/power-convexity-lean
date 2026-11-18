import PowerConvexity.Calculus.MinkowskiJointGlobalStrictSubsolutionTwo
import PowerConvexity.Calculus.JointBoundaryQuadraticTwo

/-! # Original endpoint data give a locally parameter-uniform full boundary Hessian bound -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem classicalDirichlet_minkowski_parameter_uniform_boundary_quadratic_upper_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {s R : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ d > 0, ∃ C ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (v : E → ℝ) (Jv : ClosureC2Jet v (V t)), ContDiffOn ℝ 3 v (V t) →
        (∀ x ∈ frontier (V t), v x = 0) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) v x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) v x).det = 1) →
        ∀ x ∈ frontier (V t), ∀ z : E, Jv.hessian x z z ≤ C*‖z‖^2 := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨d,hd,w,hw,hwdata⟩ :=
    classicalDirichlet_minkowski_exists_joint_global_strict_subsolution_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)} :=
    minkowskiDomain_real_closure_parameterGraph_isCompact hK hBK
  have hfront : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)} :=
    minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK
  have hgeometry (t : ℝ) (ht : t ∈ closedBall s d) (hI : t ∈ Icc (0 : ℝ) 1) :
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)) ∧ HasC2LocalDefiningFunction (V t) := by
    have hVo : IsOpen (V t) :=
      (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
        (continuous_const.prodMk continuous_id)
    have hVK : IsCompact (closure (V t)) := by
      change IsCompact (closure (minkowskiDomain t U (ball (0 : E) R)))
      rw [minkowskiDomain_closure hK hBK]
      exact (hK.smul t).add (hBK.smul (1-t))
    refine ⟨hVo,minkowskiDomain_convex hconv (convex_ball (0 : E) R) t,hVK,?_⟩
    intro x hx
    have hwd := hwdata t ht hI
    have hbd := hwd.2.2.1 x hx
    exact ⟨(fun y => w (t,y)),hwd.1.contDiffAt.of_le (by norm_num),hbd.1,hbd.2.1,hbd.2.2⟩
  obtain ⟨C,hC,hbound⟩ := joint_strict_subsolution_uniform_boundary_quadratic_upper_two
    e hab hd hgraph hfront hgeometry hw
    (fun t ht hI => (hwdata t ht hI).2.2.1)
    (fun t ht hI x hx => ((hwdata t ht hI).2.2.2 x hx).1)
    (fun t ht hI x hx => ((hwdata t ht hI).2.2.2 x (subset_closure hx)).2)
  exact ⟨d,hd,C,hC,hbound⟩

end PowerConvexity
