import PowerConvexity.Calculus.GlobalC6StrictPshBoundaryNeighborhoodTwo
import PowerConvexity.Calculus.GlobalC6StrictPshDefiningTwo
import PowerConvexity.Calculus.GlobalC6StrictSubsolutionScalingTwo

/-! # A genuine C6 global strict subsolution on each fixed Minkowski domain

The endpoint solution is still only C2 with an actual closure C2 jet.
All additional regularity is constructed from the same smooth domain charts.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_minkowski_exists_global_C6_strict_subsolution_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ w : E → ℝ, ContDiff ℝ 6 w ∧ Nonempty (ClosureC2Jet w V) ∧
      (∀ x ∈ frontier V, w x = 0 ∧ fderiv ℝ w x ≠ 0) ∧
      ∀ x ∈ closure V, (complexHessian e (fun j => Complex.I • e j) w x).PosDef ∧
        (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) w x).det := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure V) := by
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  obtain ⟨F,hF,_,hFb⟩ := classicalDirichlet_minkowski_exists_global_regular_C6_Levi_defining_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  obtain ⟨rho,hrho,hrb,W,hWo,hKW,hW⟩ := global_C6_strictPsh_boundary_neighborhood_of_Levi_two
    e (hVK.of_isClosed_subset isClosed_frontier frontier_subset_closure) hF hFb
  obtain ⟨w,hw,hwb,hwp⟩ := global_C6_strictPsh_defining_of_boundary_neighborhood_two
    e hab hVo hVK hrho hrb hWo hKW hW
  exact global_C6_strict_subsolution_of_strictPsh_closure_two
    e (fun j => Complex.I • e j) hVK hw hwb hwp

end PowerConvexity
