import PowerConvexity.Calculus.JointBoundaryStrictSubsolutionTwo

/-! # Original endpoint data yield one strict subsolution on nearby boundaries -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]

theorem classicalDirichlet_minkowski_exists_joint_boundary_strict_subsolution_two
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
        ContDiff ℝ 4 (fun x => w (t,x)) ∧
        ∀ x ∈ frontier (V t), w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
          (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0) ∧
          (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef ∧
          (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨delta,hdelta,F,hF,hFdata⟩ :=
    classicalDirichlet_minkowski_exists_joint_global_regular_Levi_defining_two
      hU hconv hK hboundary hu J hb e hab hpsh hdet hs hs1 hR
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure (V s)) := by
    change IsCompact (closure (minkowskiDomain s U (ball (0 : E) R)))
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul s).add (hBK.smul (1-s))
  exact joint_C4_strict_subsolution_on_nearby_boundaries_two e ⟨hs.le,hs1⟩ hdelta
    (hVK.of_isClosed_subset isClosed_frontier frontier_subset_closure)
    (minkowskiDomain_real_frontier_parameterGraph_isCompact hU isOpen_ball hK hBK) hF
    (fun t ht hI => (hFdata t ht hI).2.2)

end PowerConvexity
