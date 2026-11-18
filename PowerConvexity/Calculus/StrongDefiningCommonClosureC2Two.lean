import PowerConvexity.Calculus.StrongDefiningJointAprioriTwo
import PowerConvexity.Calculus.DirectionalHessianBoundaryMaximum
import PowerConvexity.Calculus.ClosureHessianNormFromUpperTwo
import PowerConvexity.Analysis.CompactLocalMonotoneBounds

/-! # A genuine common C2 bound over the entire strong Minkowski family

Compactness is applied to actual local parameter estimates before selecting
the parameter, solution, or closure jet. The directional Hessian maximum
principle transfers the actual boundary bound to the full original closure.
Complex positivity then controls the complete real Hessian operator norm.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance scc2RealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance scc2RealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem strong_defining_minkowski_common_closure_C2_bound_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (hUn : U.Nonempty) {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hb : ∀ x ∈ frontier U, f x=0 ∧ fderiv ℝ f x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ f z<0)
    {delta : ℝ} (hdelta : 0 < delta)
    (hH : ∀ x ∈ frontier U, ∀ v : E, 2*delta*‖v‖^2 ≤ realHessian f x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {R : ℝ} (hR : 0 < R) :
    let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
    ∃ C ≥ 0, ∀ t ∈ Icc (0 : ℝ) 1,
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 4 u (V t) →
        (∀ x ∈ frontier (V t), u x=0) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).det=1) →
        ∀ x ∈ closure (V t), ‖J.derivative x‖ ≤ C ∧ ‖J.hessian x‖ ≤ C := by
  let V := fun t : ℝ => minkowskiDomain t U (ball (0 : E) R)
  let P : ℝ → ℝ → Prop := fun t C => t ∈ Icc (0 : ℝ) 1 →
    ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 4 u (V t) →
      (∀ x ∈ frontier (V t), u x=0) →
      (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
      (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).det=1) →
      ∀ x ∈ closure (V t), ‖J.derivative x‖ ≤ C ∧ ‖J.hessian x‖ ≤ C
  have hmono : ∀ t a b, a ≤ b → P t a → P t b := by
    intro t a b hab hpa ht u J hu hzero hpos hdet x hx
    obtain ⟨hg,hh⟩ := hpa ht u J hu hzero hpos hdet x hx
    exact ⟨hg.trans hab,hh.trans hab⟩
  have hlocal : ∀ s ∈ Icc (0 : ℝ) 1, ∃ C ≥ 0, ∀ᶠ t in 𝓝 s, P t C := by
    intro s hs
    obtain ⟨dg,hdg,G,hG,hfirst⟩ := strong_defining_minkowski_parameter_uniform_first_tangent_bounds_two
      hU hconv hK hUn hf hb hdelta hH e hab hs.1 hs.2 hR
    obtain ⟨dh,hdh,H,hHb,hboundary⟩ := strong_defining_minkowski_parameter_uniform_boundary_quadratic_upper_two
      hU hconv hK hUn hf hb hdelta hH e hab hs.1 hs.2 hR
    refine ⟨G+2*H,by positivity,?_⟩
    filter_upwards [ball_mem_nhds s (lt_min hdg hdh)] with t ht
    intro htI u J hu hzero hpos hdet x hx
    have htg : t ∈ closedBall s dg := ball_subset_closedBall
      (ball_subset_ball (min_le_left _ _) ht)
    have hth : t ∈ closedBall s dh := ball_subset_closedBall
      (ball_subset_ball (min_le_right _ _) ht)
    have hg := (hfirst t htg htI u J (hu.of_le (by norm_num)) hzero hpos hdet).1 x hx
    have hBK : IsCompact (closure (ball (0 : E) R)) := by
      rw [closure_ball 0 hR.ne']
      exact isCompact_closedBall 0 R
    have hVK : IsCompact (closure (V t)) := by
      change IsCompact (closure (minkowskiDomain t U (ball (0 : E) R)))
      rw [minkowskiDomain_closure hK hBK]
      exact (hK.smul t).add (hBK.smul (1-t))
    have hVo : IsOpen (V t) :=
      (minkowskiDomain_real_parameterGraph_isOpen hU isOpen_ball).preimage
        (continuous_const.prodMk continuous_id)
    have hupper (v : E) : J.hessian x v v ≤ H*‖v‖^2 :=
      directionalHessian_le_boundary_bound hVo hVK hu J hzero e
        (fun j => Complex.I • e j) hpos hdet v
        (fun y hy => hboundary t hth htI u J (hu.of_le (by norm_num)) hzero hpos hdet y hy v) x hx
    have hh := closureJet_hessian_norm_le_of_quadratic_upper_two hVo
      (hu.of_le (by norm_num)) J e hpos hx hHb hupper
    exact ⟨hg.trans (by linarith),hh.trans (by linarith)⟩
  obtain ⟨C,hC,hall⟩ := compact_uniform_monotone_bound_of_local isCompact_Icc P hmono hlocal
  exact ⟨C,hC,fun t ht => hall t ht ht⟩

end PowerConvexity
