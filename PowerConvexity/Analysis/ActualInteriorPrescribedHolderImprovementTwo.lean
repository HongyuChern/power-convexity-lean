import PowerConvexity.Analysis.ActualHarmonicL2CubicTaylorTwo
import PowerConvexity.Analysis.ActualHalfEllipticQuadraticImprovementTwo

/-! # Interior weak improvement with a prescribed Holder exponent

The cubic harmonic remainder fixes the radius before the weak equation is
chosen.  The actual harmonic replacement is then made close at that radius.
The resulting contraction is r^alpha, so there is no exponent loss caused by
an unrelated fixed amplitude 1/2.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_harmonic_halfBall_L2_prescribed_holder_taylor_two :
    ∃ M > 0, ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
      ∀ eta : ℝ, 0 < eta → ∀ Rmax : ℝ, 0 < Rmax →
      ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ Rmax ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∀ v : F → ℝ,
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo (ball (0 : F) (1/2 : ℝ))).1 v →
      ContinuousOn v (ball (0 : F) (1/2 : ℝ)) →
      ∀ vw : MemW1pWitness 2 v (ball (0 : F) (1/2 : ℝ)), ‖vw.memLp.toLp v‖ ≤ 2 →
      ∃ q : F → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        ∀ x ∈ closedBall (0 : F) r, |v x-q x| ≤ eta*r^alpha*r^2 := by
  obtain ⟨M,hM,L,hL,ha⟩ := actual_harmonic_halfBall_L2_cubic_taylor_two
  refine ⟨M,hM,?_⟩
  intro alpha halpha halpha1 eta heta Rmax hRmax
  have hexp : 0 < 1-alpha := sub_pos.mpr halpha1
  let R1 := (eta/L)^((1-alpha)⁻¹)
  let R2 := (1/2 : ℝ)^(alpha⁻¹)
  have hR1 : 0 < R1 := Real.rpow_pos_of_pos (div_pos heta hL) _
  have hR2 : 0 < R2 := Real.rpow_pos_of_pos (by norm_num) _
  let r := min (1/32) (min Rmax (min R1 R2))
  have hr : 0 < r := lt_min (by norm_num) (lt_min hRmax (lt_min hR1 hR2))
  have hr32 : r ≤ (1/32 : ℝ) := min_le_left _ _
  have hrmax : r ≤ Rmax := (min_le_right _ _).trans (min_le_left _ _)
  have hr1 : r ≤ R1 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr2 : r ≤ R2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hrpow : r^alpha ≤ (1/2 : ℝ) := by
    apply (Real.rpow_le_rpow hr.le hr2 halpha.le).trans_eq
    exact Real.rpow_inv_rpow (by norm_num : (0 : ℝ) ≤ 1/2) halpha.ne'
  have hrate : L*r^(1-alpha) ≤ eta := by
    have hh : r^(1-alpha) ≤ eta/L := by
      apply (Real.rpow_le_rpow hr.le hr1 hexp.le).trans_eq
      exact Real.rpow_inv_rpow (div_pos heta hL).le hexp.ne'
    have hh' := (le_div_iff₀ hL).mp hh
    simpa only [mul_comm] using hh'
  refine ⟨r,hr,hr32,hrmax,hrpow,?_⟩
  intro v hv hc vw hn
  obtain ⟨q,hq,hqt,hqH,hqa⟩ := ha v hv hc vw hn
  refine ⟨q,hq,hqt,hqH,?_⟩
  intro x hx
  have hproduct : r^(1-alpha)*r^alpha=r := by
    rw [←Real.rpow_add hr]
    simp only [sub_add_cancel,Real.rpow_one]
  calc
    |v x-q x| ≤ L*r^3 := hqa r hr hr32 x hx
    _ = (L*r^(1-alpha))*r^alpha*r^2 := by
      calc
        _ = L*r*r^2 := by ring
        _ = L*(r^(1-alpha)*r^alpha)*r^2 := by rw [hproduct]
        _ = _ := by ring
    _ ≤ eta*r^alpha*r^2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hrate (Real.rpow_nonneg hr.le _)) (sq_nonneg _)

theorem actual_halfElliptic_L2_prescribed_holder_improvement_two {L : ℝ} (hL : 0 ≤ L) :
    ∃ M > 0, ∀ alpha : ℝ, 0 < alpha → alpha < 1 →
      ∀ eta : ℝ, 0 < eta → ∀ Rmax : ℝ, 0 < Rmax →
      ∃ r > 0, r ≤ (1/32 : ℝ) ∧ r ≤ Rmax ∧ r^alpha ≤ (1/2 : ℝ) ∧
      ∃ delta > 0, delta ≤ 1 ∧
      ∀ A : EllipticCoeff (2+2) (ball (0 : F) 1), (1/2 : ℝ) ≤ A.lam → A.Λ ≤ L →
      (∀ᵐ x ∂volume.restrict (ball (0 : F) 1), ∀ z : F,
        ‖z-matMulE (A.a x) z‖ ≤ delta*‖z‖) →
      ∀ f u : F → ℝ, ∀ hf : MemLp f 2 (volume.restrict (ball (0 : F) 1)),
      ‖hf.toLp f‖ ≤ delta → ActualScalarWeakEquationTwo A f u →
      ∀ uw : MemW1pWitness 2 u (ball (0 : F) 1), ‖uw.memLp.toLp u‖ ≤ 1 →
      ∃ q : F → ℝ, IsQuadraticPolynomial q ∧
        (∀ x, (realBlockHessian realDirections imagDirections q x).trace=0) ∧
        (∀ x, ‖realHessian q x‖ ≤ M) ∧
        (∫ x in ball (0 : F) r, (u x-q x)^2) ≤
          eta^2*(r^alpha)^2*r^4*(volume (ball (0 : F) r)).toReal := by
  obtain ⟨M,hM,hquad⟩ := actual_harmonic_halfBall_L2_prescribed_holder_taylor_two
  refine ⟨M,hM,?_⟩
  intro alpha halpha halpha1 eta heta Rmax hRmax
  obtain ⟨r,hr,hrb,hrmax,hralpha,hqapp⟩ :=
    hquad alpha halpha halpha1 (eta/2) (by positivity) Rmax hRmax
  let theta : ℝ := r^alpha
  have htheta : 0 < theta := Real.rpow_pos_of_pos hr alpha
  let V := (volume (ball (0 : F) r)).toReal
  have hV : 0 < V := ENNReal.toReal_pos (measure_ball_pos volume (0 : F) hr).ne' measure_ball_lt_top.ne
  let epsilon := min 1 (eta*theta*r^2*Real.sqrt V/2)
  have hepsilon : 0 < epsilon := lt_min (by norm_num) (by positivity)
  have he1 : epsilon ≤ 1 := min_le_left _ _
  have he2 : epsilon^2 ≤ eta^2*theta^2*r^4*V/4 := by
    calc
      epsilon^2 ≤ (eta*theta*r^2*Real.sqrt V/2)^2 :=
        (sq_le_sq₀ hepsilon.le (by positivity)).mpr (min_le_right _ _)
      _ = eta^2*theta^2*r^4*V/4 := by
        rw [div_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hV.le]
        ring
  obtain ⟨delta,hd,hd1,happ⟩ := actual_halfElliptic_uniform_harmonic_approximation_two hL hepsilon
  refine ⟨r,hr,hrb,hrmax,hralpha,delta,hd,hd1,?_⟩
  intro A hlam hAL hA f u hf hfn hu uw hun
  obtain ⟨v,hv,hzero,hvs,herr⟩ := happ A hlam hAL hA f u hf hfn hu uw hun
  let vw := MemW1p.someWitness hv.1
  obtain ⟨dw,hgrad,hge,hve⟩ := herr vw
  have hhalf : ball (0 : F) (1/2 : ℝ) ⊆ ball (0 : F) 1 := ball_subset_ball (by norm_num)
  have huh : MemLp u 2 (volume.restrict (ball (0 : F) (1/2 : ℝ))) :=
    uw.memLp.mono_measure (Measure.restrict_mono hhalf le_rfl)
  have huhn : ‖huh.toLp u‖ ≤ 1 :=
    (actual_scalar_L2_restrict_norm_le_two hhalf uw.memLp huh).trans hun
  have hvn : ‖vw.memLp.toLp v‖ ≤ 2 := by
    have hh := actual_scalar_L2_triangle_difference_two huh vw.memLp dw.memLp
    linarith
  obtain ⟨q,hqp,hqt,hqH,hqe⟩ := hqapp v hv (hvs 1).continuousOn vw hvn
  refine ⟨q,hqp,hqt,hqH,?_⟩
  have hrhalf : r ≤ (1/2 : ℝ) := by linarith
  have hsub := ball_subset_ball (x := (0 : F)) hrhalf
  have hur : MemLp u 2 (volume.restrict (ball (0 : F) r)) :=
    huh.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hvr : MemLp v 2 (volume.restrict (ball (0 : F) r)) :=
    vw.memLp.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hqr := actual_continuous_ball_memLp_two (IsQuadraticPolynomial_contDiff hqp 1).continuous (0 : F) r
  letI : IsFiniteMeasure (volume.restrict (ball (0 : F) r)) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have her : ∀ᵐ x ∂volume.restrict (ball (0 : F) r), |v x-q x| ≤ (eta/2)*theta*r^2 := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hqe x (ball_subset_closedBall hx)
  have hdn : ‖(hur.sub hvr).toLp (fun x => u x-v x)‖ ≤ epsilon :=
    (actual_scalar_L2_restrict_norm_le_two (f := fun x => u x-v x) hsub dw.memLp (hur.sub hvr)).trans hve
  have hdn2 : ‖(hur.sub hvr).toLp (fun x => u x-v x)‖^2 ≤ epsilon^2 :=
    (sq_le_sq₀ (norm_nonneg _) hepsilon.le).mpr hdn
  have hb := actual_quadratic_comparison_square_error_two hur hvr hqr
    (by positivity : 0 ≤ (eta/2)*theta*r^2) her
  change (∫ x in ball (0 : F) r, (u x-q x)^2) ≤
    2*‖(hur.sub hvr).toLp (fun x => u x-v x)‖^2+2*((eta/2)*theta*r^2)^2*V at hb
  change (∫ x in ball (0 : F) r, (u x-q x)^2) ≤ eta^2*theta^2*r^4*V
  nlinarith only [hb,hdn2,he2]

end PowerConvexity
