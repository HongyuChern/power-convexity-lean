import PowerConvexity.Analysis.ActualUniformScalarSchauderTwo
import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo

/-! # Uniform local first-derivative control for actual classical families
Only the original ellipticity and Holder bounds enter. Classical functions
are converted to the actual weak equation on a relatively compact ball.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_uniform_classical_local_Lipschitz_four
    {U : Set E} (hU : IsOpen U)
    {lam Lambda Ka Kf F alpha : ℝ} (hlam : 0 < lam) (hLambda : 0 < Lambda)
    (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf) (hF : 0 ≤ F) (halpha : 0 < alpha)
    (A : ℕ → EllipticCoeff (2+2) U)
    (hlo : ∀ n, lam ≤ (A n).lam) (hhi : ∀ n, (A n).Λ ≤ Lambda)
    (hpos : ∀ n x, x ∈ U → ((A n).a x).PosDef)
    (hreg : ∀ n i j, ContDiffOn ℝ 1 (fun x => (A n).a x i j) U)
    (hdiv : ∀ n x, x ∈ U → ∀ j,
      (∑ i, fderiv ℝ (fun y => (A n).a y i j) x (EuclideanSpace.single i 1)) = 0)
    (hhold : ∀ n x, x ∈ U → ∀ y, y ∈ U →
      ‖actualMatrixOperatorTwo ((A n).a x)-actualMatrixOperatorTwo ((A n).a y)‖ ≤ Ka*‖x-y‖^alpha)
    (f u : ℕ → E → ℝ) (hfC : ∀ n, ContDiffOn ℝ 1 (f n) U)
    (hfhold : ∀ n x, x ∈ U → ∀ y, y ∈ U → |f n x-f n y| ≤ Kf*‖x-y‖^alpha)
    (hfb : ∀ n x, x ∈ U → |f n x| ≤ F)
    (hu : ∀ n, ContDiffOn ℝ 2 (u n) U)
    (hub : ∀ n x, x ∈ U → |u n x| ≤ 1)
    (hpde : ∀ n x, x ∈ U →
      (∑ i, ∑ j, (A n).a x i j*euclideanHessian (u n) x i j) = -f n x) :
    ∀ x ∈ U, ∃ delta > 0, ∃ C ≥ 0,
      ∀ n y, y ∈ U → dist y x < delta → |u n y-u n x| ≤ C*dist y x := by
  intro x hx
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  let r := R/4
  have hr : 0 < r := div_pos hR (by norm_num)
  have hclosed : closedBall x (2*r) ⊆ U :=
    (closedBall_subset_ball (by dsimp only [r]; linarith : 2*r < R)).trans hball
  have hsub : ball x (2*r) ⊆ U := ball_subset_closedBall.trans hclosed
  have hsmall : closedBall x r ⊆ ball x (2*r) := closedBall_subset_ball (by linarith)
  let N₀ := Real.sqrt ((volume (ball (0 : E) (2*r))).toReal)
  have hN₀ : 0 ≤ N₀ := Real.sqrt_nonneg _
  obtain ⟨delta,hd,hdr,beta,hbeta,hbeta1,M,hM,hscalar⟩ :=
    actual_uniform_scalar_C2_holder_interior_two hr hlam hLambda hKa hKf hF hN₀ halpha
  have hdelta : ball x delta ⊆ U :=
    (ball_subset_ball (by linarith : delta ≤ 2*r)).trans hsub
  refine ⟨delta,hd,M,hM,?_⟩
  intro n y hy hxy
  let B := (A n).restrict hsub
  have hf : MemLp (f n) 2 (volume.restrict (ball x (2*r))) :=
    continuousOn_memLp_two_of_subset_compact measurableSet_ball
      (isCompact_closedBall x (2*r)) ball_subset_closedBall ((hfC n).continuousOn.mono hclosed)
  have hw := actual_local_classical_scalar_weak_two hU (hu n) hclosed B
    (fun i j => (hreg n i j).mono hsub) (fun z hz j => hdiv n z (hsub hz) j) hf
    (fun z hz => hpde n z (hsub hz))
  let uw := actualLocalClassicalBallWitnessTwo hU ((hu n).of_le (by norm_num)) hclosed
  have hun : ‖uw.memLp.toLp (u n)‖ ≤ N₀ := by
    simpa only [one_pow,one_mul] using actual_ball_L2_norm_bound_of_pointwise_two
      uw.memLp (by norm_num : (0 : ℝ) ≤ 1) (fun z hz => hub n z (hsub hz))
  have hC := hscalar x (ball x (2*r)) isOpen_ball isBounded_ball hsmall B
    (by simpa only [B,EllipticCoeff.restrict_lam] using hlo n)
    (by simpa only [B,EllipticCoeff.restrict_Λ] using hhi n)
    (fun z hz => hpos n z (hsub hz)) (fun i j => (hreg n i j).mono hsub)
    (fun z hz j => hdiv n z (hsub hz) j)
    (fun z hz w hw => hhold n z (hsub (hsmall hz)) w (hsub (hsmall hw)))
    (f n) (u n) hf ((hfC n).mono hsub)
    (fun z hz w hw => hfhold n z (hsub hz) w (hsub hw))
    (fun z hz => hfb n z (hsub hz)) ((hu n).continuousOn.mono hsub) hw uw hun
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (hz : z ∈ ball x delta) =>
      (hC.1.contDiffAt (isOpen_ball.mem_nhds hz)).differentiableAt (by norm_num))
    (fun z hz => (hC.2.1 z hz).2.1) (convex_ball x delta) (mem_ball_self hd) hxy
  simpa only [Real.norm_eq_abs,dist_eq_norm] using hh

end PowerConvexity
