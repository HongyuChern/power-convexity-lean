import PowerConvexity.Analysis.ActualUniformQuarterAnnularDriftFour
import PowerConvexity.Calculus.QuadraticTaylor

/-! # Removing a bounded source with an error linear in boundary distance

The actual polynomial q(t)=t-t^2/2 is nonnegative and at most t on the unit
normal strip. Its exact Hessian and derivative make it a strict source
barrier when the drift is at most half the normal ellipticity constant.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "Bilin" => E →L[ℝ] E →L[ℝ] ℝ

def actualFlatNormalSourceBarrierFour (N x : E) : ℝ :=
  0+(innerSL ℝ N) x+((-1/2 : ℝ) • realRankOneForm N) x x

private theorem normal_source_quadratic_symmetric_four (N : E) :
    ∀ v w : E, ((-1/2 : ℝ) • realRankOneForm N) v w =
      ((-1/2 : ℝ) • realRankOneForm N) w v := by
  intro v w
  change (-1/2 : ℝ)*(inner ℝ N v*inner ℝ N w)=
    (-1/2 : ℝ)*(inner ℝ N w*inner ℝ N v)
  ring

theorem actual_normal_source_barrier_formula_four (N x : E) :
    actualFlatNormalSourceBarrierFour N x = inner ℝ N x-(inner ℝ N x)^2/2 := by
  change 0+inner ℝ N x+(-1/2 : ℝ)*(inner ℝ N x*inner ℝ N x)=_
  ring

theorem actual_normal_source_barrier_contDiff_four (N : E) (k : ℕ∞ω) :
    ContDiff ℝ k (actualFlatNormalSourceBarrierFour N) :=
  IsQuadraticPolynomial_contDiff
    ⟨0,innerSL ℝ N,(-1/2 : ℝ) • realRankOneForm N,
      normal_source_quadratic_symmetric_four N,fun _ => rfl⟩ k

theorem actual_normal_source_barrier_derivative_four (N x v : E) :
    fderiv ℝ (actualFlatNormalSourceBarrierFour N) x v =
      (1-inner ℝ N x)*inner ℝ N v := by
  change fderiv ℝ (fun y => 0+(innerSL ℝ N) y+
    ((-1/2 : ℝ) • realRankOneForm N) y y) x v=_
  rw [(quadratic_coeff_hasFDerivAt 0 (innerSL ℝ N)
    ((-1/2 : ℝ) • realRankOneForm N) (normal_source_quadratic_symmetric_four N) x).fderiv]
  change inner ℝ N v+2*((-1/2 : ℝ)*(inner ℝ N x*inner ℝ N v))=_
  ring

theorem actual_normal_source_barrier_hessian_four (N x : E) :
    realHessian (actualFlatNormalSourceBarrierFour N) x = (-1 : ℝ) • realRankOneForm N := by
  change realHessian (fun y => 0+(innerSL ℝ N) y+
    ((-1/2 : ℝ) • realRankOneForm N) y y) x=_
  rw [quadratic_coeff_realHessian 0 (innerSL ℝ N)
    ((-1/2 : ℝ) • realRankOneForm N) (normal_source_quadratic_symmetric_four N) x,
    smul_smul]
  norm_num

theorem actual_normal_source_barrier_bounds_four (N : E) {x : E}
    (hx : inner ℝ N x ∈ Icc (0 : ℝ) 1) :
    0 ≤ actualFlatNormalSourceBarrierFour N x ∧
      actualFlatNormalSourceBarrierFour N x ≤ inner ℝ N x := by
  rw [actual_normal_source_barrier_formula_four]
  constructor
  · nlinarith [hx.1,hx.2,mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  · nlinarith [sq_nonneg (inner ℝ N x)]

theorem actual_normal_source_barrier_derivative_bound_four {N : E} (hN : ‖N‖=1)
    {x : E} (hx : inner ℝ N x ∈ Icc (0 : ℝ) 1) (v : E) :
    |fderiv ℝ (actualFlatNormalSourceBarrierFour N) x v| ≤ ‖v‖ := by
  have hn : |inner ℝ N v| ≤ ‖v‖ := by
    simpa only [hN,one_mul] using abs_real_inner_le_norm N v
  rw [actual_normal_source_barrier_derivative_four,abs_mul,
    abs_of_nonneg (sub_nonneg.mpr hx.2)]
  exact (mul_le_mul_of_nonneg_left hn (sub_nonneg.mpr hx.2)).trans
    (by nlinarith [mul_nonneg hx.1 (norm_nonneg v)])

theorem actual_normal_source_barrier_operator_four {N : E} (hN : ‖N‖=1)
    {x : E} (hx : inner ℝ N x ∈ Icc (0 : ℝ) 1)
    (L : Bilin →ₗ[ℝ] ℝ) {ell : ℝ}
    (hnormal : ell ≤ L (realRankOneForm N)) {b : E} (hb : ‖b‖ ≤ ell/2) :
    L (realHessian (actualFlatNormalSourceBarrierFour N) x)+
      fderiv ℝ (actualFlatNormalSourceBarrierFour N) x b ≤ -ell/2 := by
  rw [actual_normal_source_barrier_hessian_four,map_smul,smul_eq_mul]
  have hd := (le_abs_self (fderiv ℝ (actualFlatNormalSourceBarrierFour N) x b)).trans
    (actual_normal_source_barrier_derivative_bound_four hN hx b)
  linarith

theorem actual_normal_source_corrected_equation_four {N : E} (hN : ‖N‖=1)
    {x : E} (hx : inner ℝ N x ∈ Icc (0 : ℝ) 1)
    (L : Bilin →ₗ[ℝ] ℝ) {ell F : ℝ} (hell : 0 < ell) (hF : 0 ≤ F)
    (hnormal : ell ≤ L (realRankOneForm N)) {b : E} (hb : ‖b‖ ≤ ell/2)
    {u : E → ℝ} (hu : ContDiffAt ℝ 2 u x)
    (hLu : L (realHessian u x)+fderiv ℝ u x b ≤ F) :
    L (realHessian (fun y => u y+(2*F/ell)*actualFlatNormalSourceBarrierFour N y) x)+
      fderiv ℝ (fun y => u y+(2*F/ell)*actualFlatNormalSourceBarrierFour N y) x b ≤ 0 := by
  have hq := (actual_normal_source_barrier_contDiff_four N 2).contDiffAt (x := x)
  have hD := ((hu.differentiableAt (by norm_num)).hasFDerivAt.add
    ((hq.differentiableAt (by norm_num)).hasFDerivAt.const_smul (2*F/ell))).fderiv
  change fderiv ℝ (fun y => u y+(2*F/ell)*actualFlatNormalSourceBarrierFour N y) x=
    fderiv ℝ u x+(2*F/ell) • fderiv ℝ (actualFlatNormalSourceBarrierFour N) x at hD
  rw [realHessian_add hu (contDiffAt_const.mul hq),realHessian_const_mul,
    map_add,map_smul,smul_eq_mul,hD,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul]
  have hqL := actual_normal_source_barrier_operator_four hN hx L hnormal hb
  have hqF := mul_le_mul_of_nonneg_left hqL (show 0 ≤ 2*F/ell by positivity)
  have he : (2*F/ell)*(ell/2)=F := by field_simp
  nlinarith

theorem actual_tangent_ball_normal_height_four {N : E} (hN : ‖N‖=1)
    {c x : E} {R : ℝ} (hc : inner ℝ N c=R) (hR : R ≤ 1/2)
    (hx : x ∈ closedBall c R) : inner ℝ N x ∈ Icc (0 : ℝ) 1 := by
  have hh : |inner ℝ N (x-c)| ≤ R := by
    have hd : ‖x-c‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm] using hx
    have hh' : |inner ℝ N (x-c)| ≤ ‖x-c‖ := by
      simpa only [hN,one_mul] using abs_real_inner_le_norm N (x-c)
    exact hh'.trans hd
  rw [inner_sub_right,hc,abs_le] at hh
  exact ⟨by linarith [hh.1],by linarith [hh.2]⟩

variable [ProperSpace E]

theorem actual_uniform_source_quarter_annular_propagation_four
    {ell T C R : ℝ} (hell : 0 < ell) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hCsmall : C ≤ ell/2) (hR : 0 < R) (hRsmall : R ≤ 1/2) :
    ∃ theta > 0, ∀ c N : E, ‖N‖=1 → inner ℝ N c=R →
      ∀ L : E → Bilin →ₗ[ℝ] ℝ, ∀ b : E → E, ∀ u : E → ℝ,
      ContinuousOn u (closedBall c R) → ContDiffOn ℝ 2 u (ball c R) →
      (∀ x ∈ closedBall c R, 0 ≤ u x) →
      (∀ x ∈ ball c R, HessianPositive (L x)) →
      (∀ x ∈ ball c R, ∀ v : E, ell*‖v‖^2 ≤ L x (realRankOneForm v)) →
      (∀ x ∈ ball c R, L x realInnerForm ≤ T) →
      (∀ x ∈ ball c R, ‖b x‖ ≤ C) →
      ∀ F ≥ 0, (∀ x ∈ ball c R, L x (realHessian u x)+fderiv ℝ u x (b x) ≤ F) →
      ∀ m > 0, (∀ x ∈ closedBall c (R/4), m ≤ u x) →
      ∀ d ∈ Icc (0 : ℝ) (R/2),
        (m*theta-2*F/ell)*d ≤ u (c-(R-d) • N) := by
  obtain ⟨theta,htheta,hprop⟩ := actual_uniform_quarter_annular_normal_propagation_four
    (E := E) hell hT hC hR
  refine ⟨theta,htheta,?_⟩
  intro c N hN hc L b u huC hu hun hL hlower htrace hb F hF hLu m hm hinner d hd
  let w : E → ℝ := fun x => u x+(2*F/ell)*actualFlatNormalSourceBarrierFour N x
  have hq := actual_normal_source_barrier_contDiff_four N 2
  have hwC : ContinuousOn w (closedBall c R) := huC.add (continuousOn_const.mul hq.continuous.continuousOn)
  have hw : ContDiffOn ℝ 2 w (ball c R) := hu.add (contDiffOn_const.mul hq.contDiffOn)
  have hnonneg (x : E) (hx : x ∈ closedBall c R) : 0 ≤ actualFlatNormalSourceBarrierFour N x :=
    (actual_normal_source_barrier_bounds_four N (actual_tangent_ball_normal_height_four hN hc hRsmall hx)).1
  have hwu (x : E) (hx : x ∈ closedBall c R) : u x ≤ w x := by
    dsimp only [w]
    exact le_add_of_nonneg_right (mul_nonneg (by positivity) (hnonneg x hx))
  have hwn : ∀ x ∈ closedBall c R, 0 ≤ w x := fun x hx => (hun x hx).trans (hwu x hx)
  have hwL (x : E) (hx : x ∈ ball c R) :
      L x (realHessian w x)+fderiv ℝ w x (b x) ≤ 0 := by
    apply actual_normal_source_corrected_equation_four hN
      (actual_tangent_ball_normal_height_four hN hc hRsmall (ball_subset_closedBall hx))
      (L x) hell hF
    · simpa only [hN,one_pow,mul_one] using hlower x hx N
    · exact (hb x hx).trans hCsmall
    · exact hu.contDiffAt (isOpen_ball.mem_nhds hx)
    · exact hLu x hx
  have hwinner (x : E) (hx : x ∈ closedBall c (R/4)) : m ≤ w x :=
    (hinner x hx).trans (hwu x (closedBall_subset_closedBall (by linarith) hx))
  have hh := hprop c N hN L b w hwC hw hwn hL hlower htrace hb hwL m hm hwinner d hd
  have hxheight : inner ℝ N (c-(R-d) • N)=d := by
    rw [inner_sub_right,inner_smul_right,hc,real_inner_self_eq_norm_sq,hN,one_pow,mul_one]
    ring
  have hd1 : d ≤ 1 := by linarith [hd.2]
  have hqbound : actualFlatNormalSourceBarrierFour N (c-(R-d) • N) ≤ d := by
    have hh := (actual_normal_source_barrier_bounds_four N
      (show inner ℝ N (c-(R-d) • N) ∈ Icc (0 : ℝ) 1 from by rw [hxheight]; exact ⟨hd.1,hd1⟩)).2
    rwa [hxheight] at hh
  have hmul := mul_le_mul_of_nonneg_left hqbound (show 0 ≤ 2*F/ell by positivity)
  dsimp only [w] at hh
  nlinarith

end PowerConvexity
