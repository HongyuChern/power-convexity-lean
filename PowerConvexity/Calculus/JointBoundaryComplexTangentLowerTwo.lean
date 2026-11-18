import PowerConvexity.Calculus.JointSmallScaledSupersolutionTwo
import PowerConvexity.Calculus.SupersolutionTangentialBoundaryLowerTwo
import PowerConvexity.Calculus.JointStrictPshMarginTwo

/-! # Common actual boundary lower bounds from a common supersolution scale -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem joint_strictPsh_uniform_scaled_boundary_tangent_lower_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hgeometry : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hwb : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t), w (t,x) = 0)
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 2 u (V t) →
        (∀ x ∈ frontier (V t), u x = 0) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) →
        ∀ x ∈ frontier (V t), ∀ f : E → ℝ, ContDiffAt ℝ 2 f x → f x = 0 →
          fderiv ℝ f x ≠ 0 → (∀ᶠ z in 𝓝 x, z ∈ V t ↔ f z < 0) →
          ∀ v : E, fderiv ℝ f x v = 0 →
            c*realHessian (fun y => w (t,y)) x v v ≤ J.hessian x v v := by
  obtain ⟨c,hc,hcomp⟩ := joint_strictPsh_uniform_scaled_supersolution_comparison_two
    e (fun j => Complex.I • e j) hd hgraph hgeometry hw hwb hwp
  refine ⟨c,hc,?_⟩
  intro t ht hI u J hu hub hup hud x hx f hf hfx hDf hdef v hv
  obtain ⟨hU,hconv,hK⟩ := hgeometry t ht hI
  let w0 : E → ℝ := fun y => w (t,y)
  have hw0 : ContDiff ℝ 2 w0 := by
    rw [contDiff_iff_contDiffAt]
    intro y
    have hwq : ContDiffAt ℝ 2 w (t,y) :=
      (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
        ⟨closedBall_subset_ball (by linarith : d < 2*d) ht,mem_univ y⟩)).of_le (by norm_num)
    exact hwq.comp y (contDiffAt_const.prodMk contDiffAt_id)
  have hwb0 : ∀ y ∈ frontier (V t), w0 y = 0 := hwb t ht hI
  let N := (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x)
  have hNf (z : E) : inner ℝ N z = fderiv ℝ f x z := InnerProductSpace.toDual_symm_apply
  have hN : N ≠ 0 := by
    intro hz
    apply hDf
    ext z
    rw [← hNf,hz,inner_zero_left,ContinuousLinearMap.zero_apply]
  have hn : 0 < ‖N‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hN)
  have hNN : fderiv ℝ f x N = ‖N‖^2 := by rw [← hNf,real_inner_self_eq_norm_sq]
  obtain ⟨mu,hmu,hJu,hHu⟩ := classicalDirichlet_defining_tangent_hessian_two
    hU hconv hK hu J hub e (fun j => Complex.I • e j) hab hup hud hx hf hfx hDf hdef
  obtain ⟨hDw,hHw⟩ := zero_boundary_function_defining_derivative_hessian
    hU hf hfx hDf hdef hw0.contDiffAt hwb0
  obtain ⟨r,hr,hball⟩ := exists_interior_ball_of_C2_defining_function hf hfx hN
    (fun z => (hNf z).symm) hdef
  have hy : x-r • N ∈ closure (V t) := subset_closure (hball
    (mem_ball_self (mul_pos hr (norm_pos_iff.mpr hN))))
  have hh := (hcomp t ht hI u J hu hub hup hud).2 x hx (x-r • N) hy
  rw [show x-r • N-x = -r • N by module,hJu] at hh
  simp only [map_smul,ContinuousLinearMap.smul_apply,smul_eq_mul,hNN] at hh
  have hnormal : c*fderiv ℝ w0 x N ≤ mu*‖N‖^2 := by nlinarith only [hh,hr]
  have hratio : c*(fderiv ℝ w0 x N/‖N‖^2) ≤ mu := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hn).mpr hnormal
  have hcurv := definingFunction_tangent_hessian_nonneg_of_convex hU hconv hx hf hfx hDf hdef v hv
  rw [hHu v v hv hv,hHw v v hv hv]
  change c*((fderiv ℝ w0 x N/‖N‖^2)*realHessian f x v v) ≤ mu*realHessian f x v v
  have ht := mul_le_mul_of_nonneg_right hratio hcurv
  nlinarith only [ht]


theorem joint_strictPsh_uniform_boundary_complex_tangent_lower_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hgeometry : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      IsOpen (V t) ∧ Convex ℝ (V t) ∧ IsCompact (closure (V t)))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hwb : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ frontier (V t), w (t,x) = 0)
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ (u : E → ℝ) (J : ClosureC2Jet u (V t)), ContDiffOn ℝ 2 u (V t) →
        (∀ x ∈ frontier (V t), u x = 0) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) →
        ∀ x ∈ frontier (V t), ∀ f : E → ℝ, ContDiffAt ℝ 2 f x → f x = 0 →
          fderiv ℝ f x ≠ 0 → (∀ᶠ z in 𝓝 x, z ∈ V t ↔ f z < 0) →
          ∀ v : E, fderiv ℝ f x v = 0 → fderiv ℝ f x (Complex.I • v) = 0 →
            delta*‖v‖^2 ≤ J.hessian x v v+J.hessian x (Complex.I • v) (Complex.I • v) := by
  obtain ⟨c,hc,hscaled⟩ := joint_strictPsh_uniform_scaled_boundary_tangent_lower_two
    e hab hd hgraph hgeometry hw hwb hwp
  obtain ⟨eps,heps,hpaired⟩ := joint_strictPsh_has_uniform_scalar_and_paired_margin_two
    e hab hd hgraph hw hwp
  refine ⟨c*(4*eps),by positivity,?_⟩
  intro t ht hI u J hu hub hup hud x hx f hf hfx hDf hdef v hv hIv
  have h1 := hscaled t ht hI u J hu hub hup hud x hx f hf hfx hDf hdef v hv
  have h2 := hscaled t ht hI u J hu hub hup hud x hx f hf hfx hDf hdef (Complex.I • v) hIv
  have h3 := mul_le_mul_of_nonneg_left
    ((hpaired t ht hI x (frontier_subset_closure hx)).2 v) hc.le
  nlinarith only [h1,h2,h3]

end PowerConvexity
