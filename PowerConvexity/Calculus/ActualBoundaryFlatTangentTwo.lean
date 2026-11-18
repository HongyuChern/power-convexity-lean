import PowerConvexity.Calculus.VariableDensityBoundaryNormalTwo
import PowerConvexity.Calculus.ParallelPrincipalCurvature
import PowerConvexity.Calculus.MinkowskiSmoothBoundary

/-! # Flat real boundary tangents remain flat in the actual solution jet.
This proves a failure of the direct positive-real-tangent collar interface.
It does not disprove a positive power Hessian at actual interior points.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder Pointwise
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

theorem classicalDirichlet_boundary_tangent_null_iff_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ y ∈ frontier U, u y = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hp : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    (hd : ∀ y ∈ U, 1 ≤ (complexHessian a b u y).det.re)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    (∀ v : E, J.derivative x v = 0 ↔ fderiv ℝ f x v = 0) ∧
    ∀ v : E, fderiv ℝ f x v = 0 →
      (J.hessian x v v = 0 ↔ realHessian f x v v = 0) := by
  obtain ⟨lam,hlam,hJ,hH⟩ := classicalDirichlet_defining_tangent_hessian_of_det_lower_two
    hU hconv hK hu J hb a b hab hp hd hx hf hfx hDf hdef
  constructor
  · intro v
    rw [hJ]
    simp only [smul_apply,smul_eq_mul,mul_eq_zero,hlam.ne',false_or]
  · intro v hv
    rw [hH v v hv hv]
    simp only [mul_eq_zero,hlam.ne',false_or]

theorem minkowski_actual_solution_inherits_flat_tangent_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {v : E} (htan : fderiv ℝ f x v = 0) (hflat : realHessian f x v v = 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u (minkowskiDomain t U (ball (0 : E) R)))
    (J : ClosureC2Jet u (minkowskiDomain t U (ball (0 : E) R)))
    (hb : ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), u y = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hp : ∀ y ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u y).PosDef)
    (hd : ∀ y ∈ minkowskiDomain t U (ball (0 : E) R), 1 ≤ (complexHessian a b u y).det.re) :
    let y := definingParallelMap f t ((1-t)*R) x
    J.derivative y v = 0 ∧ J.hessian y v v = 0 := by
  let V := minkowskiDomain t U (ball (0 : E) R)
  let y := definingParallelMap f t ((1-t)*R) x
  have hVo : IsOpen V := by
    dsimp only [V]
    rw [minkowskiDomain_eq_smul_add]
    exact (hU.smul₀ ht.ne').add_right
  have hVc := minkowskiDomain_convex hconv (convex_ball (0 : E) R) t
  have hBK : IsCompact (closure (ball (0 : E) R)) := by
    rw [closure_ball 0 hR.ne']
    exact isCompact_closedBall 0 R
  have hVK : IsCompact (closure V) := by
    dsimp only [V]
    rw [minkowskiDomain_closure hK hBK]
    exact (hK.smul t).add (hBK.smul (1-t))
  have hy : y ∈ frontier V := definingParallelMap_mem_minkowski_frontier
    hU hconv hx hf hfx hDf hdef ht ht1.le hR
  obtain ⟨g,hg,hgy,hDg,hgdef⟩ := smoothLocalDefiningFunction_implies_C2
    (minkowskiDomain_hasSmoothLocalDefiningFunction hU hconv hK hboundary ht ht1 hR) y hy
  have htv := (parallel_defining_tangent_kernel_iff hU hconv hx hf hfx hDf hdef
    ht.le ht1.le hg hgy hDg hgdef v).mpr htan
  have hnull := (parallel_defining_tangent_null_iff hU hconv hx hf hfx hDf hdef
    ht ht1.le hR hg hgy hDg hgdef htv).mpr hflat
  have hh := classicalDirichlet_boundary_tangent_null_iff_of_det_lower_two
    hVo hVc hVK hu J hb a b hab hp hd hy hg hgy hDg hgdef
  exact ⟨(hh.1 v).mpr htv,(hh.2 v htv).mpr hnull⟩

theorem minkowski_flat_tangent_excludes_actual_boundary_tangent_strict_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hboundary : HasSmoothLocalDefiningFunction U)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0)
    {v : E} (hv : v ≠ 0) (htan : fderiv ℝ f x v = 0) (hflat : realHessian f x v v = 0)
    {t R : ℝ} (ht : 0 < t) (ht1 : t < 1) (hR : 0 < R)
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u (minkowskiDomain t U (ball (0 : E) R)))
    (J : ClosureC2Jet u (minkowskiDomain t U (ball (0 : E) R)))
    (hb : ∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)), u y = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hp : ∀ y ∈ minkowskiDomain t U (ball (0 : E) R), (complexHessian a b u y).PosDef)
    (hd : ∀ y ∈ minkowskiDomain t U (ball (0 : E) R), 1 ≤ (complexHessian a b u y).det.re) :
    ¬ (∀ y ∈ frontier (minkowskiDomain t U (ball (0 : E) R)),
      ∀ z : E, z ≠ 0 → J.derivative y z = 0 → 0 < J.hessian y z z) := by
  intro hstrict
  have hy := definingParallelMap_mem_minkowski_frontier
    hU hconv hx hf hfx hDf hdef ht ht1.le hR
  have hh := minkowski_actual_solution_inherits_flat_tangent_two hU hconv hK hboundary
    hx hf hfx hDf hdef htan hflat ht ht1 hR hu J hb a b hab hp hd
  have hpos := hstrict _ hy v hv hh.1
  rw [hh.2] at hpos
  exact lt_irrefl 0 hpos

end PowerConvexity
