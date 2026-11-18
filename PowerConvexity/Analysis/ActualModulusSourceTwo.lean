import PowerConvexity.Analysis.ActualRescaledScalarSourceTwo

/-! # Scalar residual sources controlled by an actual local modulus

The original coefficient and source need only the displayed bounds on the
same physical ball. No derivative bound for the coefficient is used here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_rescaled_harmonic_quadratic_modulus_smallness_two
    {R a epsilon K : ℝ} (hR : 0 < R) (ha : 0 < a)
    (heps : 0 ≤ epsilon) (hK : 0 ≤ K)
    {A : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {f q : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : E) R)))
    (hqf : MemLp (quadraticScalarSourceTwo A q) 2 (volume.restrict (ball (0 : E) R)))
    (hA : ∀ x ∈ ball (0 : E) R, ∀ v : E,
      ‖v-matMulE (A x) v‖ ≤ (epsilon*a)*‖v‖)
    (hfn : ∀ x ∈ ball (0 : E) R, |f x| ≤ epsilon*a)
    (hH : ∀ x ∈ ball (0 : E) R, ‖realHessian q x‖ ≤ K)
    (htrace : ∀ x ∈ ball (0 : E) R,
      (realBlockHessian realDirections imagDirections q x).trace = 0) :
    ∃ hg : MemLp (fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)))
      2 (volume.restrict (ball (0 : E) 1)),
      ‖hg.toLp (fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)))‖ ≤
        epsilon*(1+16*K)*Real.sqrt (volume (ball (0 : E) 1)).toReal := by
  have hg : MemLp (fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)))
      2 (volume.restrict (ball (0 : E) 1)) := by
    simpa only [zero_add,Pi.sub_apply] using
      (actual_memLp_affine_rescale_two hR (hf.sub hqf)).const_mul a⁻¹
  refine ⟨hg,?_⟩
  letI : IsFiniteMeasure (volume.restrict (ball (0 : E) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply actual_scalar_L2_bound_of_ae_bound_two hg (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hz1 : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
  have hx : R • z ∈ ball (0 : E) R := by
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    nlinarith
  have hqbound := actual_harmonic_quadratic_source_bound_two
    (mul_nonneg heps ha.le) hK (hA _ hx) (hH _ hx) (htrace _ hx)
  have hs : |f (R • z)-quadraticScalarSourceTwo A q (R • z)| ≤
      (epsilon*(1+16*K))*a := by
    exact (abs_sub _ _).trans ((add_le_add (hfn _ hx) hqbound).trans_eq (by ring))
  rw [abs_mul,abs_of_pos (inv_pos.mpr ha)]
  exact (mul_le_mul_of_nonneg_left hs (inv_pos.mpr ha).le).trans_eq (by field_simp)

end PowerConvexity
