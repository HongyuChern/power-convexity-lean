import PowerConvexity.Calculus.ActualSmallCMAIsometricBallBoundTwo
import PowerConvexity.Calculus.QuadraticBallPotential

/-! # Actual real Hessian estimate for a classical CMA solution near the ball potential.
The deviation is the actual function u-(norm squared-R squared). Its complex
background is exactly the identity and its physical Hessian is recovered.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
open Set Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "F" => DeGiorgi.AmbientSpace (2+2)
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_directional_complexHessian_sub {ι : Type*} (a b : ι → E)
    {u q : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) (hq : ContDiffAt ℝ 2 q x) :
    complexHessian a b (fun y => u y-q y) x = complexHessian a b u x-complexHessian a b q x := by
  have he : (fun y => u y-q y) = fun y => u y+(-1)*q y := by funext y; ring
  rw [he,complexHessian_add_at hu (contDiffAt_const.mul hq),complexHessian_const_mul_at hq]
  simp only [Complex.ofReal_neg,Complex.ofReal_one,neg_smul,one_smul,sub_eq_add_neg]

theorem actual_ball_deviation_recovers_Hessian_norm_two {u : E → ℝ} {c : E} (R : ℝ)
    (hu : ContDiffAt ℝ 2 u c) {K : ℝ} (hK : 0 ≤ K)
    (hw : ‖realHessian (fun y => u y-quadraticBallPotential 1 R y) c‖ ≤ K) :
    ‖realHessian u c‖ ≤ K+2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  have hh := congrArg (fun H : E →L[ℝ] E →L[ℝ] ℝ => H v z)
    (realHessian_sub_at hu (quadraticBallPotential_contDiff 1 R 2).contDiffAt)
  simp only [ContinuousLinearMap.sub_apply,quadraticBallPotential_realHessian,mul_one] at hh
  have he : realHessian u c v z =
      realHessian (fun y => u y-quadraticBallPotential 1 R y) c v z+2*inner ℝ v z := by
    linarith only [hh]
  rw [he]
  calc
    _ ≤ ‖realHessian (fun y => u y-quadraticBallPotential 1 R y) c v z‖+‖2*inner ℝ v z‖ := norm_add_le _ _
    _ ≤ K*‖v‖*‖z‖+2*(‖v‖*‖z‖) := by
      apply add_le_add
      · exact ((realHessian (fun y => u y-quadraticBallPotential 1 R y) c).le_opNorm₂ v z).trans (by gcongr)
      · rw [norm_mul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤2)]
        exact mul_le_mul_of_nonneg_left (norm_inner_le_norm v z) (by norm_num)
    _ = (K+2)*‖v‖*‖z‖ := by ring

theorem actual_CMA_ball_deviation_Hessian_bound_two :
    ∃ C > 0, ∃ ε₀ > 0, ∀ (L : F ≃ₗᵢ[ℝ] E),
      Orthonormal ℝ (Sum.elim (fun i => L (realDirections i)) (fun i => L (imagDirections i))) →
      ∀ (c : E) (r : ℝ), 0 < r → ∀ ε > 0, ε ≤ ε₀ → ∀ (R : ℝ) (u : E → ℝ),
      ContinuousOn u (closedBall c r) → ContDiffOn ℝ 2 u (ball c r) →
      (∀ x ∈ ball c r,
        (complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) u x).PosDef) →
      (∀ x ∈ ball c r,
        (complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) u x).det = 1) →
      (∀ x ∈ closedBall c r, |u x-quadraticBallPotential 1 R x| ≤ ε*r^2) →
      ‖realHessian u c‖ ≤ C*ε+2 := by
  obtain ⟨C,hC,ε₀,hε₀,hsmall⟩ := actual_small_CMA_isometric_ball_Hessian_bound_two (E := E)
  refine ⟨C,hC,ε₀,hε₀,?_⟩
  intro L hab c r hr ε hε he R u huc hu hp hd hb
  have hq := quadraticBallPotential_contDiff (E := E) 1 R 2
  have hreg (x : E) (hx : x ∈ ball c r) : ContDiffAt ℝ 2 u x :=
    (hu x hx).contDiffAt (isOpen_ball.mem_nhds hx)
  have hid (x : E) (hx : x ∈ ball c r) :
      1+complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i))
        (fun y => u y-quadraticBallPotential 1 R y) x =
      complexHessian (fun i => L (realDirections i)) (fun i => L (imagDirections i)) u x := by
    rw [actual_directional_complexHessian_sub _ _ (hreg x hx) hq.contDiffAt,
      quadraticBallPotential_complexHessian _ _ hab]
    simp only [Complex.ofReal_one,one_smul]
    abel
  have hbound := hsmall L c r hr ε hε he (fun y => u y-quadraticBallPotential 1 R y)
    (huc.sub hq.continuous.continuousOn) (hu.sub hq.contDiffOn)
    (fun x hx => by rw [hid x hx]; exact (hp x hx).posSemidef)
    (fun x hx => by rw [hid x hx]; exact hd x hx) hb
  exact actual_ball_deviation_recovers_Hessian_norm_two R (hreg c (mem_ball_self hr))
    (mul_nonneg hC.le hε.le) hbound

end PowerConvexity
