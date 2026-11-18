import PowerConvexity.Calculus.GlobalStrictPshBoundaryNeighborhoodTwo

/-! # One actual global defining function strictly psh near the whole Minkowski boundary -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_minkowski_exists_global_strictPsh_boundary_neighborhood_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R) :
    let V := minkowskiDomain t U (ball (0 : E) R)
    ∃ rho : E → ℝ, ContDiff ℝ 4 rho ∧
      (∀ x ∈ frontier V, rho x = 0 ∧ fderiv ℝ rho x ≠ 0) ∧
      ∃ W : Set E, IsOpen W ∧ frontier V ⊆ W ∧
        ∀ z ∈ W, (z ∈ V ↔ rho z < 0) ∧
          (complexHessian e (fun j => Complex.I • e j) rho z).PosDef := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  obtain ⟨F,hF,hFn,hFboundary⟩ := classicalDirichlet_minkowski_exists_global_regular_Levi_defining_two
    hU hconv hK hboundary hu J hb e hab hpsh hdet ht ht1 hR
  have hKV : IsCompact (closure V) := by
    obtain ⟨L,hL⟩ := hK.isBounded.exists_norm_le
    have hUb (x : E) (hx : x ∈ U) : ‖x‖ ≤ max L R :=
      (hL x (subset_closure hx)).trans (le_max_left _ _)
    have hBb (x : E) (hx : x ∈ ball (0 : E) R) : ‖x‖ ≤ max L R := by
      have hh : ‖x‖ < R := by simpa only [mem_ball,dist_zero_right] using hx
      exact hh.le.trans (le_max_right _ _)
    exact minkowskiDomain_isCompact_closure hUb hBb ht.le ht1.le
  exact global_C4_strictPsh_boundary_neighborhood_of_Levi_two e
    (hKV.of_isClosed_subset isClosed_frontier frontier_subset_closure) hF hFboundary

end PowerConvexity
