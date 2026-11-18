import DifferentialGeometry.External.DeGiorgi.Harnack

/-! # Pointwise uniform Harnack for the same nonnegative weak response

Only almost-everywhere nonnegativity and boundedness are assumed on the whole
ball. The given continuous representative is retained on the half ball.
This is the interior positive-propagation input for a boundary slope argument;
it is not itself a boundary quotient regularity theorem.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology
namespace PowerConvexity
open DeGiorgi
local notation "E" => AmbientSpace (2+2)

private theorem harnack_continuous_order_of_ae_four {U : Set E} (hU : IsOpen U)
    {u v : E → ℝ} (hu : ContinuousOn u U) (hv : ContinuousOn v U)
    (hae : ∀ᵐ x ∂volume.restrict U, u x≤v x) : ∀ x∈U, u x≤v x := by
  have he : (fun x => max (u x) (v x)) =ᵐ[volume.restrict U] v := by
    filter_upwards [hae] with x hx
    exact max_eq_right hx
  have hh := Measure.eqOn_open_of_ae_eq he hU (hu.sup hv) hv
  intro x hx
  exact (le_max_left _ _).trans (hh hx).le

def actualUniformHarnackFactorFour (L : ℝ) : ℝ :=
  Real.exp (|CHarnack (2+2)| *L^((1 : ℝ)/2))

theorem actual_uniform_harnack_factor_positive_four (L : ℝ) :
    0 < actualUniformHarnackFactorFour L := Real.exp_pos _

theorem actual_bounded_nonnegative_weak_harnack_four
    (A : NormalizedEllipticCoeff (2+2) (ball (0 : E) 1)) {L M : ℝ}
    (hL : A.1.Λ≤L) {u : E → ℝ}
    (hu : IsHomogeneousWeakSolution A.1 u)
    (huC : ContinuousOn u (ball (0 : E) (1/2 : ℝ)))
    (hun : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), 0≤u x)
    (hub : ∀ᵐ x ∂volume.restrict (ball (0 : E) 1), u x≤M) :
    ∀ x∈ball (0 : E) (1/2 : ℝ), ∀ y∈ball (0 : E) (1/2 : ℝ),
      u x≤actualUniformHarnackFactorFour L*u y := by
  let H := Real.exp (CHarnack (2+2)*A.1.Λ^((1 : ℝ)/2))
  have hH : 0 < H := Real.exp_pos _
  have hhalf : ball (0 : E) (1/2 : ℝ) ⊆ ball (0 : E) 1 := ball_subset_ball (by norm_num)
  have hunhalf := ae_restrict_of_ae_restrict_of_subset hhalf hun
  have hubhalf := ae_restrict_of_ae_restrict_of_subset hhalf hub
  have hupoint := harnack_continuous_order_of_ae_four isOpen_ball continuousOn_const huC hunhalf
  have hbounded (eps : ℝ) (heps : 0<eps) :
      ∀ x∈ball (0 : E) (1/2 : ℝ), ∀ y∈ball (0 : E) (1/2 : ℝ),
        u x+eps≤H*(u y+eps) := by
    let v : E → ℝ := fun z => max (u z) 0+eps
    have heq : (fun z => u z+eps) =ᵐ[volume.restrict (ball (0 : E) 1)] v := by
      filter_upwards [hun] with z hz
      simp only [v,max_eq_left hz]
    have hvsol : IsSolution A.1 v := by
      apply IsSolution.congr_ae heq
      simpa only [sub_neg_eq_add] using
        (isHomogeneousWeakSolution_isSolution hu).sub_const_ball (by norm_num) (-eps)
    have hvpos : ∀ z∈ball (0 : E) 1, 0<v z := by
      intro z _
      exact add_pos_of_nonneg_of_pos (le_max_right _ _) heps
    have hvC : ContinuousOn v (ball (0 : E) (1/2 : ℝ)) :=
      (huC.sup continuousOn_const).add continuousOn_const
    have heqpoint := Measure.eqOn_open_of_ae_eq
      (ae_restrict_of_ae_restrict_of_subset hhalf heq) isOpen_ball
      (huC.add continuousOn_const) hvC
    have hvbound : ∀ᵐ z ∂volume.restrict (ball (0 : E) (1/2 : ℝ)), v z≤M+eps := by
      filter_upwards [hunhalf,hubhalf] with z hn hb
      simp only [v,max_eq_left hn]
      linarith
    have hvnonneg : ∀ᵐ z ∂volume.restrict (ball (0 : E) (1/2 : ℝ)), eps≤v z :=
      Filter.Eventually.of_forall (fun z => le_add_of_nonneg_left (le_max_right _ _))
    have hsup := harnack_continuous_order_of_ae_four isOpen_ball hvC continuousOn_const
      (ae_le_essSup (show IsBoundedUnder (·≤·) (ae (volume.restrict
        (ball (0 : E) (1/2 : ℝ)))) v from ⟨M+eps,hvbound⟩))
    have hinf := harnack_continuous_order_of_ae_four isOpen_ball continuousOn_const hvC
      (ae_essInf_le (show IsBoundedUnder (·≥·) (ae (volume.restrict
        (ball (0 : E) (1/2 : ℝ)))) v from ⟨eps,hvnonneg⟩))
    have hhar := harnack (by norm_num : 2 < ((2+2 : ℕ) : ℝ)) A hvpos hvsol
    intro x hx y hy
    have hxe : u x+eps=v x := heqpoint hx
    have hye : u y+eps=v y := heqpoint hy
    rw [hxe,hye]
    exact (hsup x hx).trans (hhar.trans (mul_le_mul_of_nonneg_left (hinf y hy) hH.le))
  intro x hx y hy
  have hxy : u x≤H*u y := by
    apply le_of_forall_pos_le_add
    intro delta hdelta
    let eps := delta/(H+1)
    have hHp : 0<H+1 := by linarith
    have heps : 0<eps := div_pos hdelta hHp
    have he := hbounded eps heps x hx y hy
    have heq : (H+1)*eps=delta := mul_div_cancel₀ delta hHp.ne'
    nlinarith
  have hfac : H≤actualUniformHarnackFactorFour L := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul (le_abs_self _) (Real.rpow_le_rpow A.1.Λ_nonneg hL (by norm_num : (0 : ℝ)≤1/2))
      (Real.rpow_nonneg A.1.Λ_nonneg _) (abs_nonneg _)
  exact hxy.trans (mul_le_mul_of_nonneg_right hfac (hupoint y hy))

end PowerConvexity
