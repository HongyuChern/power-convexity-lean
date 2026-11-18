import CHS.Algebra.PositiveCone
import PowerConvexity.Calculus.VariableDensityCofactor
import PowerConvexity.Calculus.VariableDensityTraceBarrierTwo

/-! # Compact Hermitian margins and a determinant-lower cofactor barrier -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Filter Metric Matrix
open scoped Topology ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity

theorem actual_compact_hermitian_scalar_margin_two
    {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (B : X → Matrix (Fin 2) (Fin 2) ℂ) (hB : Continuous B)
    (hherm : ∀ x, (B x).IsHermitian) (hpos : ∀ x ∈ K, (B x).PosDef) :
    ∃ eps : ℝ, 0 < eps ∧ ∀ x ∈ K,
      (B x-(eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosDef := by
  let F : ℝ × X → Matrix (Fin 2) (Fin 2) ℂ :=
    fun z => B z.2-(z.1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  have hF : Continuous F := (hB.comp continuous_snd).sub
    ((Complex.continuous_ofReal.comp continuous_fst).smul continuous_const)
  have hFH : ∀ z, (F z).IsHermitian := by
    intro z
    exact (hherm z.2).sub (Matrix.isHermitian_one.smul (by
      change star (z.1 : ℂ) = (z.1 : ℂ)
      simp))
  have ho : IsOpen {z | (F z).PosDef} := CHS.Algebra.isOpen_posDef_preimage hF hFH
  have hev : ∀ᶠ eps : ℝ in 𝓝 0, ∀ x ∈ K, (F (eps,x)).PosDef :=
    hK.eventually_forall_of_forall_eventually (fun x hx => ho.mem_nhds (by
      change (F (0,x)).PosDef
      simpa only [F,Complex.ofReal_zero,zero_smul,sub_zero] using hpos x hx))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r/2,by positivity,?_⟩
  have hh : r/2 ∈ ball (0 : ℝ) r := by
    rw [mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < r/2)]
    linarith
  exact hball hh

theorem actual_trace_adjugate_lower_det_one_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hdet : 1 ≤ A.det.re) :
    2 ≤ A.adjugate.trace.re := by
  have hp := positive_complex_adjugate hA
  have ht : 0 < A.adjugate.trace.re := (Complex.pos_iff.mp hp.trace_pos).1
  have hd : A.adjugate.det = A.det := by simp only [Matrix.det_adjugate,Fintype.card_fin]; norm_num
  have hdisc := hermitian_trace_discriminant_nonneg_two hp.isHermitian
  rw [hd] at hdisc
  nlinarith

theorem actual_cofactor_trace_lower_scalar_margin_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) (hdet : 1 ≤ A.det.re)
    {eps : ℝ} (heps : 0 ≤ eps)
    (hB : (B-(eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    2*eps ≤ (B*A.adjugate).trace.re := by
  have hh := CHS.Algebra.trace_product_posSemidef_nonneg hB
    (positive_complex_adjugate hA).posSemidef
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul] at hh
  simp only [smul_eq_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at hh
  have ht := mul_le_mul_of_nonneg_left (actual_trace_adjugate_lower_det_one_two hA hdet) heps
  nlinarith

end PowerConvexity
