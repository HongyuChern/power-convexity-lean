import PowerConvexity.Calculus.TraceBarrierBoundaryComparisonTwo
import PowerConvexity.Calculus.LinearizedDirichletC0Two

/-! # The trace barrier absorbs an actual inhomogeneous source

No determinant-one hypothesis is needed for this maximum comparison.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem linearized_function_le_trace_barrier_with_source_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u g V : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ x ∈ frontier U, u x = 0)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hgc : ContinuousOn g (closure U)) (hg : ContDiffOn ℝ 2 g U)
    (hVc : ContinuousOn V (closure U)) (hV : ContDiffOn ℝ 2 V U)
    (hVb : ∀ x ∈ frontier U, V x = 0)
    {A : ℝ} (hA : 0 ≤ A) (hgL : ∀ x ∈ U, -A ≤ linearizedCMAOperatorTwo a b u g x)
    (hVL : ∀ x ∈ U, linearizedCMAOperatorTwo a b u V x ≤
      -(1/2 : ℝ)*(1+((complexHessian a b u x)⁻¹).trace.re))
    (p : E) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ x ∈ frontier U, g x ≤ B*‖x-p‖^2) :
    ∀ x ∈ closure U, g x ≤ 2*(A+B)*V x+B*‖x-p‖^2 := by
  let q : E → ℝ := fun y => ‖y-p‖^2
  have hq : ContDiff ℝ 2 q := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  let f : E → ℝ := fun y => g y-(2*(A+B))*V y-B*q y
  let L := fun x => complexHessianContraction a b (complexHessian a b u x)⁻¹
  have hfc : ContinuousOn f (closure U) :=
    (hgc.sub (continuousOn_const.mul hVc)).sub (continuousOn_const.mul hq.continuous.continuousOn)
  have hf : ContDiffOn ℝ 2 f U :=
    (hg.sub (contDiffOn_const.mul hV)).sub (contDiffOn_const.mul hq.contDiffOn)
  have hLf (x : E) (hx : x ∈ U) : 0 ≤ linearizedCMAOperatorTwo a b u f x := by
    have hgx := hg.contDiffAt (hU.mem_nhds hx)
    have hVx := hV.contDiffAt (hU.mem_nhds hx)
    change 0 ≤ L x (realHessian (fun y => g y-(2*(A+B))*V y-B*q y) x)
    rw [realHessian_sub_at (hgx.sub (contDiffAt_const.mul hVx))
      (contDiffAt_const.mul hq.contDiffAt),realHessian_sub_at hgx (contDiffAt_const.mul hVx),
      realHessian_const_mul,realHessian_const_mul,
      map_sub (L x) (realHessian g x-(2*(A+B)) • realHessian V x) (B • realHessian q x),
      map_sub (L x) (realHessian g x) ((2*(A+B)) • realHessian V x),
      (L x).map_smul (2*(A+B)) (realHessian V x),(L x).map_smul B (realHessian q x),
      smul_eq_mul,smul_eq_mul]
    have hquad : L x (realHessian q x) = ((complexHessian a b u x)⁻¹).trace.re :=
      translated_norm_square_complex_contraction_two a b hab _ p x
    rw [hquad]
    have hT : 0 ≤ ((complexHessian a b u x)⁻¹).trace.re := by
      have ht := two_sqrt_det_re_le_trace (hup x hx).inv.posSemidef
      have hs := Real.sqrt_nonneg (((complexHessian a b u x)⁻¹).det.re)
      linarith
    have hmul := mul_le_mul_of_nonneg_left (hVL x hx)
      (show 0 ≤ 2*(A+B) by positivity)
    have hsource := hgL x hx
    change -A ≤ L x (realHessian g x) at hsource
    change 2*(A+B)*L x (realHessian V x) ≤ _ at hmul
    nlinarith [mul_nonneg hA hT]
  have hfb (x : E) (hx : x ∈ frontier U) : f x ≤ 0 := by
    dsimp only [f,q]
    rw [hVb x hx,mul_zero,sub_zero]
    exact sub_nonpos.mpr (hgb x hx)
  have hh := linearizedCMAOperatorTwo_nonpositive a b hU hK huc hu hub hup hfc hf hfb hLf
  intro x hx
  have hhx := hh x hx
  dsimp only [f,q] at hhx
  linarith

theorem linearized_function_abs_le_trace_barrier_with_source_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u g V : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ x ∈ frontier U, u x = 0)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hgc : ContinuousOn g (closure U)) (hg : ContDiffOn ℝ 2 g U)
    (hVc : ContinuousOn V (closure U)) (hV : ContDiffOn ℝ 2 V U)
    (hVb : ∀ x ∈ frontier U, V x = 0)
    {A : ℝ} (hA : 0 ≤ A) (hgL : ∀ x ∈ U, |linearizedCMAOperatorTwo a b u g x| ≤ A)
    (hVL : ∀ x ∈ U, linearizedCMAOperatorTwo a b u V x ≤
      -(1/2 : ℝ)*(1+((complexHessian a b u x)⁻¹).trace.re))
    (p : E) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ x ∈ frontier U, |g x| ≤ B*‖x-p‖^2) :
    ∀ x ∈ closure U, |g x| ≤ 2*(A+B)*V x+B*‖x-p‖^2 := by
  have hp := linearized_function_le_trace_barrier_with_source_two hU hK a b hab huc hu hub hup
    hgc hg hVc hV hVb hA (fun x hx => (abs_le.mp (hgL x hx)).1) hVL p hB
    (fun x hx => (le_abs_self _).trans (hgb x hx))
  have hn := linearized_function_le_trace_barrier_with_source_two hU hK a b hab huc hu hub hup
    hgc.neg hg.neg hVc hV hVb hA
    (fun x hx => by
      change -A ≤ complexHessianContraction a b (complexHessian a b u x)⁻¹
        (realHessian (fun y => -g y) x)
      rw [realHessian_neg,map_neg (complexHessianContraction a b (complexHessian a b u x)⁻¹)
        (realHessian g x)]
      exact neg_le_neg (abs_le.mp (hgL x hx)).2) hVL p hB
    (fun x hx => (neg_le_abs _).trans (hgb x hx))
  intro x hx
  have hnx : -g x ≤ 2*(A+B)*V x+B*‖x-p‖^2 := hn x hx
  exact abs_le.mpr ⟨by linarith,hp x hx⟩

end PowerConvexity
