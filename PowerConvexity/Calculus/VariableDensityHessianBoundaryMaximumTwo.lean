import PowerConvexity.Calculus.ContinuationDensityDerivativeBoundsTwo

/-! # Boundary-to-interior Hessian control for variable-density auxiliary solutions

This transfers an actual directional boundary upper bound to the interior,
with the source correction derived from f. It does not construct the boundary
bound itself or assert existence of an auxiliary solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem directionalHessian_variable_density_le_boundary_bound_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {u f : E → ℝ} (hu : ContDiffOn ℝ 4 u U) (hf : ContDiffOn ℝ 2 f U)
    (J : ClosureC2Jet u U) (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hp : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (complexHessian a b u x).det = (f x : ℂ))
    (hfp : ∀ x ∈ U, 0 < f x) (v : E) {C M : ℝ}
    (hsource : ∀ x ∈ U,
      -C ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2)
    (hM : ∀ x ∈ frontier U, J.hessian x v v ≤ M) :
    ∀ x ∈ closure U, J.hessian x v v ≤ M-(C/2)*u x := by
  let g : E → ℝ := fun y => J.hessian y v v + -M
  have heq (x : E) (hx : x ∈ U) :
      (fun y => J.hessian y v v) =ᶠ[𝓝 x] (fun y => realHessian u y v v) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [J.hessian_eq hy]
    rfl
  have hgc : ContinuousOn g (closure U) :=
    ((J.continuous_hessian.clm_apply continuousOn_const).clm_apply continuousOn_const).add
      continuousOn_const
  have hg : ContDiffOn ℝ 2 g U := by
    intro x hx
    exact ((realHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) v v).congr_of_eventuallyEq
      (heq x hx)).add contDiffAt_const |>.contDiffWithinAt
  have hgb : ∀ x ∈ frontier U, g x ≤ 0 := by
    intro x hx
    dsimp only [g]
    linarith [hM x hx]
  have hLg : ∀ x ∈ U, -C ≤ linearizedCMAOperatorTwo a b u g x := by
    intro x hx
    have heH : realHessian (fun y => J.hessian y v v) x =
        realHessian (fun y => realHessian u y v v) x := (heq x hx).fderiv.fderiv_eq
    dsimp only [linearizedCMAOperatorTwo,g]
    rw [realHessian_add_const,heH]
    exact (hsource x hx).trans
      (directionalHessian_variable_density_lower_two hU hu hf a b hdet hfp hx (hp x hx) v)
  have hh := linearizedCMAOperatorTwo_upper_barrier a b hU hK J.continuous_value
    (hu.of_le (by norm_num)) hb hp hgc hg hgb hLg
  intro x hx
  have h := hh x hx
  dsimp only [g] at h
  linarith

variable [FiniteDimensional ℝ E]

theorem continuation_density_uniform_directional_boundary_to_interior_two
    (a b : Fin 2 → E) {V : Set E} (hV : IsOpen V) (hK : IsCompact (closure V))
    {w : E → ℝ} (hw : ContDiff ℝ 4 w)
    (hd : ∀ x ∈ closure V, (1 : ℝ) ≤ (complexHessian a b w x).det.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ u : E → ℝ, ClassicalDirichletDensityDataTwo a b V
        (dirichletContinuationDensityTwo a b w s) u →
      ∀ J : ClosureC2Jet u V, ∀ v : E, ‖v‖ = 1 →
        ∀ M : ℝ, (∀ x ∈ frontier V, J.hessian x v v ≤ M) →
          ∀ x ∈ closure V, J.hessian x v v ≤ M-(C/2)*u x := by
  obtain ⟨C,hC,hsource⟩ := dirichletContinuationDensityTwo_uniform_second_source a b hK hw hd
  refine ⟨C,hC,?_⟩
  intro s hs u hu J v hv M hM
  exact directionalHessian_variable_density_le_boundary_bound_two hV hK hu.1
    (dirichletContinuationDensityTwo_contDiff a b hw s).contDiffOn J hu.2.2.2.2 a b hu.2.2.1
    hu.2.2.2.1
    (fun x hx => lt_of_lt_of_le zero_lt_one
      (dirichletContinuationDensityTwo_bounds a b hs (hd x (subset_closure hx))).1)
    v (fun x hx => hsource s hs x (subset_closure hx) v hv) hM

end PowerConvexity
