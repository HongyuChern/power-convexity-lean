import PowerConvexity.Calculus.ClassicalDefiningLeviTwo

/-! # Actual boundary normals and tangent jets for densities bounded below by one

The comparison uses only det(Hu).re >= 1, so it applies to each auxiliary
continuation equation. No determinant-one identity is inserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Metric Filter
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem solution_le_translated_ball_of_det_lower_two
    {U : Set E} {u : E → ℝ} {R : ℝ} {c : E}
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hR : 0 < R) (hball : ball c R ⊆ U)
    (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hnonpos : ∀ x ∈ closure U, u x ≤ 0)
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re) :
    ∀ x ∈ closure (ball c R), u x ≤ translatedBallPotential 1 R c x := by
  have hcl : closure (ball c R) ⊆ closure U := closure_mono hball
  have hcompact : IsCompact (closure (ball c R)) := by
    rw [closure_ball c hR.ne']
    exact isCompact_closedBall c R
  apply classical_comparison_two isOpen_ball hcompact a b hab (huc.mono hcl)
    (translatedBallPotential_contDiff 1 R c 0).continuous.continuousOn (hu.mono hball)
    (translatedBallPotential_contDiff 1 R c 2).contDiffOn (fun x hx => hpsh x (hball hx))
  · intro x hx
    rw [translatedBallPotential_complexHessian a b hab]
    simpa only [Complex.ofReal_one,one_smul,Matrix.det_one,Complex.one_re] using hdet x (hball hx)
  · intro x hx
    have hs : x ∈ sphere c R := by rwa [frontier_ball c hR.ne'] at hx
    have hn : ‖x-c‖ = R := by simpa only [mem_sphere,dist_eq_norm] using hs
    rw [translatedBallPotential_zero_on_sphere 1 R c x hn]
    exact hnonpos x (hcl (frontier_subset_closure hx))

theorem classicalDirichlet_inward_ball_derivative_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x c : E} {R : ℝ} (hx : x ∈ frontier U) (hR : 0 < R)
    (hball : ball c R ⊆ U) (hxr : ‖x-c‖ = R) :
    J.derivative x (c-x) ≤ -2*R^2 := by
  have hcomp := solution_le_translated_ball_of_det_lower_two a b hab hR hball J.continuous_value hu
    (strictPshDirichlet_nonpos_closure_two hU hK J.continuous_value hu hb a b hpsh) hpsh hdet
  have hxball : x ∈ closure (ball c R) := by
    rw [closure_ball c hR.ne',mem_closedBall,dist_eq_norm,hxr]
  have hcball : c ∈ closure (ball c R) := subset_closure (mem_ball_self hR)
  have hcone : c-x ∈ posTangentConeAt (closure (ball c R)) x :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_ball c R).closure.segment_subset hxball hcball)
  have hD : HasFDerivWithinAt u (J.derivative x) (closure (ball c R)) x :=
    (closureJet_hasFDerivWithinAt hU hconv (hu.differentiableOn (by norm_num)) J
      (frontier_subset_closure hx)).mono (closure_mono hball)
  have hmax : IsMaxOn (fun y => u y-translatedBallPotential 1 R c y) (closure (ball c R)) x := by
    intro y hy
    change u y-translatedBallPotential 1 R c y ≤ u x-translatedBallPotential 1 R c x
    rw [hb x hx,translatedBallPotential_zero_on_sphere 1 R c x hxr,sub_self]
    exact sub_nonpos.mpr (hcomp y hy)
  have hv := ((translatedBallPotential_contDiff 1 R c 1).differentiable (by norm_num) x).hasFDerivAt
  have hh := hmax.localize.hasFDerivWithinAt_nonpos (hD.sub hv.hasFDerivWithinAt) hcone
  change J.derivative x (c-x)-fderiv ℝ (translatedBallPotential 1 R c) x (c-x) ≤ 0 at hh
  rw [translatedBallPotential_fderiv_apply] at hh
  have hi : inner ℝ (x-c) (c-x) = -(R^2) := by
    rw [show c-x = -(x-c) by abel,inner_neg_right,real_inner_self_eq_norm_sq,hxr]
  rw [hi] at hh
  linarith

theorem classicalDirichlet_derivative_eq_positive_defining_multiple_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ lam : ℝ, 0 < lam ∧ J.derivative x = lam • fderiv ℝ f x := by
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun v => (hNf v).symm) hdef
  have hR : 0 < r*‖N‖ := mul_pos hr (norm_pos_iff.mpr hN)
  have hxr : ‖x-(x-r • N)‖ = r*‖N‖ := by
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have hJ : J.derivative x ≠ 0 := by
    have hh := classicalDirichlet_inward_ball_derivative_of_det_lower_two hU hconv hK hu J hb
      a b hab hpsh hdet hx hR hball hxr
    intro hz
    rw [hz,ContinuousLinearMap.zero_apply] at hh
    nlinarith [sq_pos_of_pos hR]
  have hs : ∀ y ∈ closedBall (x-r • N) (r*‖N‖), J.derivative x (y-x) ≤ 0 := by
    intro y hy
    apply classicalDirichlet_closure_derivative_support_two hU hconv hK hu J hb a b hpsh hx
    apply closure_mono hball
    rwa [closure_ball _ hR.ne']
  obtain ⟨lam,hlam,he⟩ := supportingFunctional_tangent_ball_positive_multiple (J.derivative x)
    hJ hN hr hs
  refine ⟨lam,hlam,?_⟩
  ext v
  simpa only [ContinuousLinearMap.smul_apply,smul_eq_mul,hNf] using he v

theorem classicalDirichlet_defining_tangent_hessian_of_det_lower_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {u : E → ℝ} (hu : ContDiffOn ℝ 2 u U) (J : ClosureC2Jet u U)
    (hb : ∀ x ∈ frontier U, u x = 0)
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (hpsh : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hdet : ∀ x ∈ U, (1 : ℝ) ≤ (complexHessian a b u x).det.re)
    {x : E} (hx : x ∈ frontier U) {f : E → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hfx : f x = 0) (hDf : fderiv ℝ f x ≠ 0)
    (hdef : ∀ᶠ z in 𝓝 x, z ∈ U ↔ f z < 0) :
    ∃ lam : ℝ, 0 < lam ∧ J.derivative x = lam • fderiv ℝ f x ∧
      ∀ v w : E, fderiv ℝ f x v = 0 → fderiv ℝ f x w = 0 →
        J.hessian x v w = lam * realHessian f x v w := by
  obtain ⟨lam,hlam,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_of_det_lower_two
    hU hconv hK hu J hb a b hab hpsh hdet hx hf hfx hDf hdef
  obtain ⟨γ,N,hN,h0N,hγ0,hγ,hγb,hγf,hγD⟩ :=
    exists_contDiff_defining_boundary_chart hU hf hfx hDf hdef
  refine ⟨lam,hlam,hJ,?_⟩
  intro v w hv hw
  have hA := closureJet_boundary_chart_hessian hU hconv hu J hb hN hγ hγb h0N v w
  have hzero : f ∘ γ =ᶠ[𝓝 (0 : E)] (0 : E → ℝ) := by
    filter_upwards [hN.mem_nhds h0N] with y hy
    exact hγf y hy
  have hB := realHessian_of_locally_zero_composition
    (show ContDiffAt ℝ 2 f (γ 0) by rwa [hγ0])
    (hγ.contDiffAt (hN.mem_nhds h0N)) hzero v w
  rw [hγ0,hγD v hv,hγD w hw,hJ] at hA
  rw [hγ0,hγD v hv,hγD w hw] at hB
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul] at hA
  have hm := congrArg (fun z : ℝ => lam*z) hB
  nlinarith


end PowerConvexity
