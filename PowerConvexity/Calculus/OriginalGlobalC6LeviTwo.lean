import PowerConvexity.Calculus.GlobalC6BoundaryLeviDefiningTwo

/-! # A global C6 boundary defining function on the original domain itself.
The original classical endpoint supplies Levi positivity; smooth charts and
the existing finite gluing construction supply the function. No positive
real principal-curvature premise is added.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem classicalDirichlet_exists_global_regular_C6_Levi_defining_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0) (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    (hpsh : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) :
    ∃ F : E → ℝ, ContDiff ℝ 6 F ∧ (∀ x ∈ U, F x ≤ 0) ∧
      ∀ x ∈ frontier U, F x = 0 ∧ fderiv ℝ F x ≠ 0 ∧
        (∀ᶠ z in 𝓝 x, z ∈ U ↔ F z < 0) ∧
        ∀ v : E, v ≠ 0 → fderiv ℝ F x v = 0 → fderiv ℝ F x (Complex.I • v) = 0 →
          0 < realHessian F x v v+realHessian F x (Complex.I • v) (Complex.I • v) := by
  apply exists_global_regular_C6_Levi_defining_of_local_subsolutions_two e hU hconv
    (hK.of_isClosed_subset isClosed_frontier frontier_subset_closure)
  intro x hx
  obtain ⟨f,hf,hfx,hDf,hdef⟩ := hboundary x hx
  have hLevi := classicalDirichlet_defining_Levi_positive_two hU hconv hK hu J hb e hab
    hpsh hdet hx ((contDiffAt_infty.mp hf) 2) hfx hDf hdef
  obtain ⟨rho,hrho,hrx,_,hDrho,hrdef,hrpos⟩ :=
    smooth_defining_exists_strictPsh_neighborhood_two e hf hfx hDf hdef hLevi
  obtain ⟨w,hw,hwx,hDw,hnear⟩ := exists_local_zero_boundary_subsolution_two
    e (fun j => Complex.I • e j) hU hrho hrx hDrho hrdef (hrpos.mono (fun _ hy => hy.2))
  have hw6 : ContDiffAt ℝ 6 w x := (contDiffAt_infty.mp hw) 6
  have hD : ContinuousAt (fun z => fderiv ℝ w z) x :=
    (hw6.fderiv_right (m := 5) (by norm_num)).continuousAt
  have hnb := hnear.and ((hw6.eventually (by norm_num)).and (hD.eventually_ne hDw))
  obtain ⟨r,hr,hrP⟩ := Metric.eventually_nhds_iff.mp hnb
  have hP (z : E) (hz : z ∈ ball x r) := hrP (show dist z x < r from hz)
  refine ⟨r,w,⟨hr,?_,?_,?_,?_⟩,?_⟩
  · intro z hz
    exact (hP z hz).2.1.contDiffWithinAt
  · intro z hz
    exact (hP z hz).1.1
  · intro z hz
    exact (hP z hz.1).1.2.2.1 hz.2
  · intro z hz
    exact (hP z hz).1.2.2.2
  · intro z hz
    exact (hP z hz).2.2

end PowerConvexity
