import PowerConvexity.Calculus.JointBoundaryAffineTangencyTwo
import PowerConvexity.Calculus.JointSubsolutionFirstTangentBoundsTwo
import PowerConvexity.Calculus.JointTraceBarrierTwo
import PowerConvexity.Calculus.StrictSubsolutionUniformMixedBoundaryTwo

/-! # One actual mixed boundary estimate before parameter and unknown solution -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
noncomputable section
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance jbmRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance jbmRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule
local instance jbmDualTopology : TopologicalSpace (E →L[ℝ] ℝ) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace

theorem joint_strict_subsolution_uniform_boundary_normal_tangent_bound_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hfront : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ frontier (V q.1)})
    (hgeometry : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)) ∧ HasC2LocalDefiningFunction (V t))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hbd : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t),
      w (t,x) = 0 ∧ fderiv ℝ (fun y => w (t,y)) x ≠ 0 ∧
      (∀ᶠ z in 𝓝 x, z ∈ V t ↔ w (t,z) < 0))
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef)
    (hwd : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ V t,
      (1 : ℂ) < (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).det) :
    ∃ M ≥ 0, ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 3 u (V t) →
        (∀ y ∈ frontier (V t), u y = 0) →
        (∀ y ∈ V t, (complexHessian e (fun j => Complex.I • e j) u y).PosDef) →
        (∀ y ∈ V t, (complexHessian e (fun j => Complex.I • e j) u y).det = 1) →
        ∀ x ∈ frontier (V t), ∀ tau : E, ‖tau‖ ≤ 1 →
          fderiv ℝ (fun y => w (t,y)) x tau = 0 →
          |J.hessian x ((InnerProductSpace.toDual ℝ E).symm
            (fderiv ℝ (fun y => w (t,y)) x)) tau| ≤ M := by
  obtain ⟨C,hC,hgrad⟩ := joint_strict_subsolution_uniform_first_tangent_bounds_two
    e (fun j => Complex.I • e j) hab hd hgraph hgeometry hw
    (fun t ht hI => ⟨fun x hx => (hbd t ht hI x hx).1,
      fun x hx => ⟨hwp t ht hI x (subset_closure hx),hwd t ht hI x hx⟩⟩)
  obtain ⟨alpha,halpha,hlinear⟩ := joint_strictPsh_scaled_uniform_trace_barrier_two
    e hab hd hgraph (fun t ht hI => (hgeometry t ht hI).1) hw hwp
  obtain ⟨eta,heta,D,hD,Cg,hCg,K0,hK0,hgeo⟩ := joint_regular_defining_uniform_affine_tangency_two
    e hd hfront hw (fun t ht hI x hx => ⟨(hbd t ht hI x hx).1,(hbd t ht hI x hx).2.1⟩)
  let B : ℝ := (C/eta)*Cg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let P : ℝ := alpha*D
  have hP : 0 ≤ P := by dsimp [P]; positivity
  let M : ℝ := 2*B*(C+P)*D+C*K0*D
  refine ⟨M,by dsimp [M]; positivity,?_⟩
  intro t ht hI u J hu hub hup hud x hx tau htau htangent
  obtain ⟨hU,hconv,hK,hboundary⟩ := hgeometry t ht hI
  let f : E → ℝ := fun y => w (t,y)
  have hgd := hgeo t ht hI
  have hf : ContDiff ℝ 3 f := hgd.1
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfb (y : E) (hy : y ∈ frontier (V t)) : f y = 0 ∧ fderiv ℝ f y ≠ 0 :=
    ⟨(hbd t ht hI y hy).1,(hbd t ht hI y hy).2.1⟩
  have hdef (y : E) (hy : y ∈ frontier (V t)) : ∀ᶠ z in 𝓝 y, z ∈ V t ↔ f z < 0 :=
    (hbd t ht hI y hy).2.2
  let W : E → ℝ := fun y => alpha*f y
  have hW : ContDiff ℝ 2 W := contDiff_const.mul hf2
  have hWb : ∀ y ∈ frontier (V t), W y = 0 := fun y hy => by
    simp only [W,(hfb y hy).1,mul_zero]
  have hgU := (hgrad t ht hI u J hu hub hup hud).1
  have hPb (y : E) (hy : y ∈ frontier (V t)) : ‖fderiv ℝ W y‖ ≤ P := by
    have he : fderiv ℝ W y = alpha • fderiv ℝ f y :=
      fderiv_const_mul (hf2.contDiffAt.differentiableAt (by norm_num)) alpha
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos halpha]
    exact mul_le_mul_of_nonneg_left ((hgd.2.1 y hy).2) halpha.le
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (v : E) : inner ℝ N v = fderiv ℝ f x v := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply (hfb x hx).2
    ext v
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function
    hf2.contDiffAt (hfb x hx).1 hN (fun v => (hNf v).symm) (hdef x hx)
  have hy : x-r • N ∈ closure (V t) := subset_closure (hball
    (mem_ball_self (mul_pos hr (norm_pos_iff.mpr hN))))
  obtain ⟨K,c,htrace,hcx,hKn,hq⟩ := hgd.2.2 x hx tau htau htangent
  have hqU (y : E) (hy : y ∈ frontier (V t)) : |J.derivative y (c+K y)| ≤ B*‖y-x‖^2 := by
    obtain ⟨mu,hmu,hJ⟩ := classicalDirichlet_derivative_eq_positive_defining_multiple_two
      hU hconv hK (hu.of_le (by norm_num)) J hub e (fun j => Complex.I • e j) hab hup hud hy
      hf2.contDiffAt (hfb y hy).1 (hfb y hy).2 (hdef y hy)
    have hm1 := positive_multiple_coefficient_le_norm_bound (fderiv ℝ f y) (J.derivative y)
      (hfb y hy).2 hmu hJ (hgU y (frontier_subset_closure hy))
    have hm : mu ≤ C/eta := hm1.trans (div_le_div₀ hC le_rfl heta (hgd.2.1 y hy).1)
    rw [hJ,ContinuousLinearMap.smul_apply,smul_eq_mul,abs_mul,abs_of_pos hmu]
    calc
      mu*|fderiv ℝ f y (c+K y)| ≤ mu*(Cg*‖y-x‖^2) :=
        mul_le_mul_of_nonneg_left (hq y hy) hmu.le
      _ ≤ (C/eta)*(Cg*‖y-x‖^2) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = B*‖y-x‖^2 := by dsimp [B]; ring
  have hcmp := affine_boundary_mixed_from_trace_barrier_two hU hconv hK e hab hu hW J hub hWb
    hup hud K c htrace (hlinear t ht hI u (hu.of_le (by norm_num)) hup hud) hx hB hqU (x-r • N) hy
  rw [show x-r • N-x = -r • N by module,hcx] at hcmp
  have hh := mixed_bound_of_affine_inward_comparison (J.hessian x) (J.derivative x)
    (fderiv ℝ W x) (K.restrictScalars ℝ) N tau hr hB hC
    (hgU x (frontier_subset_closure hx)) hcmp
  have hNnorm : ‖N‖ ≤ D := by
    rw [show ‖N‖ = ‖fderiv ℝ f x‖ from (InnerProductSpace.toDual ℝ E).symm.norm_map _]
    exact (hgd.2.1 x hx).2
  have hKN : ‖K N‖ ≤ K0*D :=
    (K.le_opNorm N).trans (mul_le_mul hKn hNnorm (norm_nonneg _) hK0)
  have hfirst : 2*B*(C+‖fderiv ℝ W x‖)*‖N‖ ≤ 2*B*(C+P)*D := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hPb x hx)) (by positivity)
    · exact hNnorm
    · exact norm_nonneg _
    · positivity
  have hsecond := mul_le_mul_of_nonneg_left hKN hC
  change |J.hessian x N tau| ≤ M
  dsimp only [M]
  change |J.hessian x N tau| ≤ 2*B*(C+‖fderiv ℝ W x‖)*‖N‖+C*‖K N‖ at hh
  nlinarith only [hh,hfirst,hsecond]

end
end PowerConvexity
