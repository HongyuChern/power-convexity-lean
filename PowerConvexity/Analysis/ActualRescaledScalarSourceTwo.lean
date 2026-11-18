import PowerConvexity.Analysis.ActualQuadraticSourceBoundTwo
import PowerConvexity.Analysis.ActualQuadraticScaleNormalizationTwo

/-! # Actual L2 source control under quadratic-scale iteration.
The scalar pullback is proved directly by measurable change of variables.
The residual bound retains the same original coefficient and polynomial.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_memLp_affine_rescale_two {p : ENNReal} {c : E} {R : ℝ} {f : E → ℝ}
    (hR : 0 < R) (hf : MemLp f p (volume.restrict (ball c R))) :
    MemLp (fun z => f (c+R • z)) p (volume.restrict (ball (0 : E) 1)) := by
  let T : E → E := fun z => c+R • z
  have hT : MeasurableEmbedding T :=
    ((MeasurableEquiv.addLeft c).measurableEmbedding).comp
      ((Homeomorph.smul (isUnit_iff_ne_zero.2 hR.ne').unit).toMeasurableEquiv.measurableEmbedding)
  have hpre : T ⁻¹' ball c R = ball (0 : E) 1 := by
    ext z
    simp only [T,mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero,
      norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    constructor <;> intro h <;> nlinarith
  rw [show (fun z => f (c+R • z)) = f ∘ T from rfl,← hpre,
    ← hT.memLp_map_measure_iff,← hT.restrict_map,
    show Measure.map T volume =
      ENNReal.ofReal (|R^Module.finrank ℝ E|⁻¹) • (volume : Measure E) from by
        rw [show T = (fun z : E => c+z) ∘ (fun z => R • z) from rfl,
          ← Measure.map_map (measurable_const_add c) (measurable_const_smul R),
          Measure.map_addHaar_smul volume hR.ne',Measure.map_smul,
          (measurePreserving_add_left volume c).map_eq,abs_inv],
    Measure.restrict_smul]
  exact hf.smul_measure ENNReal.ofReal_ne_top

theorem actual_scalar_L2_bound_of_ae_bound_two
    {U : Set E} [IsFiniteMeasure (volume.restrict U)] {f : E → ℝ}
    (hf : MemLp f 2 (volume.restrict U)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ᵐ x ∂volume.restrict U, |f x| ≤ B) :
    ‖hf.toLp f‖ ≤ B*Real.sqrt (volume U).toReal := by
  have hs := actual_scalar_L2_squared_bound_of_ae_bound_two hf hB hb
  have hv : 0 ≤ (volume U).toReal := ENNReal.toReal_nonneg
  have hv2 := Real.sq_sqrt hv
  have hprod : 0 ≤ B*Real.sqrt (volume U).toReal := by positivity
  nlinarith [norm_nonneg (hf.toLp f)]

theorem actual_rescaled_harmonic_quadratic_source_smallness_two
    {R a epsilon K : ℝ} (hR : 0 < R) (ha : 0 < a) (hRa : R ≤ a)
    (heps : 0 ≤ epsilon) (hK : 0 ≤ K)
    {A : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {f q : E → ℝ}
    (hf : MemLp f 2 (volume.restrict (ball (0 : E) R)))
    (hqf : MemLp (quadraticScalarSourceTwo A q) 2 (volume.restrict (ball (0 : E) R)))
    (hA : ∀ x ∈ ball (0 : E) R, ∀ v : E,
      ‖v-matMulE (A x) v‖ ≤ (epsilon*‖x‖)*‖v‖)
    (hfn : ∀ x ∈ ball (0 : E) R, |f x| ≤ epsilon*‖x‖)
    (hH : ∀ x ∈ ball (0 : E) R, ‖realHessian q x‖ ≤ K)
    (htrace : ∀ x ∈ ball (0 : E) R,
      (realBlockHessian realDirections imagDirections q x).trace = 0) :
    ∃ hg : MemLp (fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)))
      2 (volume.restrict (ball (0 : E) 1)),
      ‖hg.toLp (fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)))‖ ≤
        epsilon*(1+16*K)*Real.sqrt (volume (ball (0 : E) 1)).toReal := by
  have hg : MemLp (fun z => a⁻¹*(f (R • z)-quadraticScalarSourceTwo A q (R • z)))
      2 (volume.restrict (ball (0 : E) 1)) := by
    simpa only [zero_add,Pi.sub_apply] using (actual_memLp_affine_rescale_two hR (hf.sub hqf)).const_mul a⁻¹
  refine ⟨hg,?_⟩
  letI : IsFiniteMeasure (volume.restrict (ball (0 : E) 1)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  apply actual_scalar_L2_bound_of_ae_bound_two hg (by positivity)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hz1 : ‖z‖ < 1 := by simpa only [mem_ball,dist_zero_right] using hz
  have hx : R • z ∈ ball (0 : E) R := by
    rw [mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    nlinarith
  have hxa : ‖R • z‖ ≤ a := (by
    simpa only [mem_ball,dist_zero_right] using hx : ‖R • z‖ < R).le.trans hRa
  have hqbound := actual_harmonic_quadratic_source_bound_two
    (mul_nonneg heps (norm_nonneg (R • z))) hK (hA _ hx) (hH _ hx) (htrace _ hx)
  have hs : |f (R • z)-quadraticScalarSourceTwo A q (R • z)| ≤
      (epsilon*(1+16*K))*a := by
    calc
      _ ≤ |f (R • z)|+|quadraticScalarSourceTwo A q (R • z)| := abs_sub _ _
      _ ≤ epsilon*‖R • z‖+16*(epsilon*‖R • z‖)*K := add_le_add (hfn _ hx) hqbound
      _ = (epsilon*(1+16*K))*‖R • z‖ := by ring
      _ ≤ (epsilon*(1+16*K))*a := mul_le_mul_of_nonneg_left hxa (by positivity)
  rw [abs_mul,abs_of_pos (inv_pos.mpr ha)]
  exact (mul_le_mul_of_nonneg_left hs (inv_pos.mpr ha).le).trans_eq (by field_simp)

end PowerConvexity
