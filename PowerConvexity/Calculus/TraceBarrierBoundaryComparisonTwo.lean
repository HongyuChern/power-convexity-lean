import PowerConvexity.Calculus.StrongLinearizedSubsolutionBarrierTwo
import PowerConvexity.Calculus.AffineBoundaryQuadraticTangencyTwo
import PowerConvexity.Calculus.TranslatedBallBarrierTwo

/-! # Global comparison for a homogeneous linearized solution and a trace barrier

The squared-distance error is the actual Euclidean quadratic. The solution u
itself supplies the strict maximum-principle barrier. Uniform ellipticity and
real convexity of u are not assumptions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem translated_norm_square_complex_contraction_two
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    (A : Matrix (Fin 2) (Fin 2) ℂ) (p x : E) :
    complexHessianContraction a b A (realHessian (fun y => ‖y-p‖^2) x) = A.trace.re := by
  have he : (fun y : E => ‖y-p‖^2) = translatedBallPotential 1 0 p := by
    funext y
    simp only [translatedBallPotential,quadraticBallPotential,zero_pow (by norm_num : 2 ≠ 0),
      sub_zero,one_mul]
  rw [he,← complexHessianContraction_pairing a b _
    (translatedBallPotential_contDiff 1 0 p 2).contDiffAt,
    complex_contraction_eq_trace (translatedBallPotential_contDiff 1 0 p 2).contDiffAt,
    translatedBallPotential_complexHessian a b hab]
  simp

theorem linearized_function_le_trace_barrier_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u g V : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ x ∈ frontier U, u x = 0)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hgc : ContinuousOn g (closure U)) (hg : ContDiffOn ℝ 2 g U)
    (hVc : ContinuousOn V (closure U)) (hV : ContDiffOn ℝ 2 V U)
    (hVb : ∀ x ∈ frontier U, V x = 0)
    (hgL : ∀ x ∈ U, complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian g x) = 0)
    (hVL : ∀ x ∈ U, complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian V x) ≤ -(1/2 : ℝ)*(1+((complexHessian a b u x)⁻¹).trace.re))
    (p : E) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ x ∈ frontier U, g x ≤ B*‖x-p‖^2) :
    ∀ x ∈ closure U, g x ≤ 2*B*V x+B*‖x-p‖^2 := by
  let q : E → ℝ := fun y => ‖y-p‖^2
  have hq : ContDiff ℝ 2 q := (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  let f : E → ℝ := fun y => g y-(2*B)*V y-B*q y
  let L := fun x => complexHessianContraction a b (complexHessian a b u x)⁻¹
  have hfc : ContinuousOn f (closure U) :=
    (hgc.sub (continuousOn_const.mul hVc)).sub (continuousOn_const.mul hq.continuous.continuousOn)
  have hf : ContDiffOn ℝ 2 f U :=
    (hg.sub (contDiffOn_const.mul hV)).sub (contDiffOn_const.mul hq.contDiffOn)
  have hfL (x : E) (hx : x ∈ U) : 0 ≤ L x (realHessian f x) := by
    have hgx := hg.contDiffAt (hU.mem_nhds hx)
    have hVx := hV.contDiffAt (hU.mem_nhds hx)
    change 0 ≤ L x (realHessian (fun y => g y-(2*B)*V y-B*q y) x)
    rw [realHessian_sub_at (hgx.sub (contDiffAt_const.mul hVx))
      (contDiffAt_const.mul hq.contDiffAt),
      realHessian_sub_at hgx (contDiffAt_const.mul hVx),realHessian_const_mul,
      realHessian_const_mul,
      map_sub (L x) (realHessian g x-(2*B) • realHessian V x) (B • realHessian q x),
      map_sub (L x) (realHessian g x) ((2*B) • realHessian V x),
      (L x).map_smul (2*B) (realHessian V x),
      (L x).map_smul B (realHessian q x),smul_eq_mul,smul_eq_mul]
    have hquad : L x (realHessian q x) = ((complexHessian a b u x)⁻¹).trace.re :=
      translated_norm_square_complex_contraction_two a b hab _ p x
    rw [show L x (realHessian g x) = 0 from hgL x hx,hquad]
    have hh := mul_le_mul_of_nonneg_left (hVL x hx) (show 0 ≤ 2*B by positivity)
    dsimp only [L] at *
    nlinarith
  have huL (x : E) (hx : x ∈ U) : 0 < L x (realHessian u x) := by
    rw [show L x (realHessian u x) = 2 from by
      simpa using complexHessianContraction_self_eq_card (hu.contDiffAt (hU.mem_nhds hx))
        a b (by rw [hud x hx]; exact one_ne_zero)]
    norm_num
  have hh := nonpositive_of_nonnegative_contraction_with_zero_boundary_barrier hU hK
    hfc hf (fun x hx => by dsimp only [f,q]; rw [hVb x hx,mul_zero,sub_zero]; exact sub_nonpos.mpr (hgb x hx))
    huc hu hub L (fun x hx => complexHessianContraction_positive a b (hup x hx).inv) hfL huL
  intro x hx
  have hhx := hh x hx
  dsimp only [f,q] at hhx
  linarith

theorem linearized_function_abs_le_trace_barrier_two
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    (a b : Fin 2 → E) (hab : Orthonormal ℝ (Sum.elim a b))
    {u g V : E → ℝ} (huc : ContinuousOn u (closure U)) (hu : ContDiffOn ℝ 2 u U)
    (hub : ∀ x ∈ frontier U, u x = 0)
    (hup : ∀ x ∈ U, (complexHessian a b u x).PosDef)
    (hud : ∀ x ∈ U, (complexHessian a b u x).det = 1)
    (hgc : ContinuousOn g (closure U)) (hg : ContDiffOn ℝ 2 g U)
    (hVc : ContinuousOn V (closure U)) (hV : ContDiffOn ℝ 2 V U)
    (hVb : ∀ x ∈ frontier U, V x = 0)
    (hgL : ∀ x ∈ U, complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian g x) = 0)
    (hVL : ∀ x ∈ U, complexHessianContraction a b (complexHessian a b u x)⁻¹
      (realHessian V x) ≤ -(1/2 : ℝ)*(1+((complexHessian a b u x)⁻¹).trace.re))
    (p : E) {B : ℝ} (hB : 0 ≤ B)
    (hgb : ∀ x ∈ frontier U, |g x| ≤ B*‖x-p‖^2) :
    ∀ x ∈ closure U, |g x| ≤ 2*B*V x+B*‖x-p‖^2 := by
  have hp := linearized_function_le_trace_barrier_two hU hK a b hab huc hu hub hup hud
    hgc hg hVc hV hVb hgL hVL p hB (fun x hx => (le_abs_self _).trans (hgb x hx))
  have hn := linearized_function_le_trace_barrier_two hU hK a b hab huc hu hub hup hud
    hgc.neg hg.neg hVc hV hVb
    (fun x hx => by
      change complexHessianContraction a b (complexHessian a b u x)⁻¹
        (realHessian (fun y => -g y) x) = 0
      rw [realHessian_neg,map_neg (complexHessianContraction a b (complexHessian a b u x)⁻¹)
        (realHessian g x),hgL x hx,neg_zero]) hVL p hB
    (fun x hx => (neg_le_abs _).trans (hgb x hx))
  intro x hx
  have hhx : -g x ≤ 2*B*V x+B*‖x-p‖^2 := hn x hx
  exact abs_le.mpr ⟨by linarith, hp x hx⟩

end PowerConvexity
