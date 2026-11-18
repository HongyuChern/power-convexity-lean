import PowerConvexity.Calculus.UniformStrictPshMarginTwo
import PowerConvexity.Calculus.StrictSubsolutionLinearizedBarrierTwo

/-! # A scaled genuine subsolution absorbs inverse-Hessian trace errors

A single positive scalar is chosen from the fixed strict psh barrier and the
compact actual closure, before the unknown determinant-one solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem trace_quotient_lower_of_two_identity_margin_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef)
    (hB : (B-(2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    2*(A⁻¹).trace.re ≤ (B*A⁻¹).trace.re := by
  have hh := CHS.Algebra.trace_product_posSemidef_nonneg hB hA.inv.posSemidef
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul] at hh
  norm_num [Complex.sub_re,Complex.mul_re,Complex.mul_im] at hh
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem strictPsh_scaled_uniform_trace_barrier_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E → ℝ, ContDiffOn ℝ 2 u U →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) →
      ∀ x ∈ U,
        complexHessianContraction e (fun j => Complex.I • e j)
          (complexHessian e (fun j => Complex.I • e j) u x)⁻¹
          (realHessian (fun y => u y-c*w y) x) ≤
        -(1/2 : ℝ)*(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re) := by
  obtain ⟨eps,heps,hmargin⟩ := compact_strictPsh_has_uniform_scalar_margin_two e hab hK hw hwp
  let c : ℝ := 2/eps
  have hc : 0 < c := div_pos (by norm_num) heps
  have hce : c*eps = 2 := div_mul_cancel₀ _ heps.ne'
  refine ⟨c,hc,?_⟩
  intro u hu hup hud x hx
  let a := e
  let b := fun j => Complex.I • e j
  let A := complexHessian a b u x
  let B := complexHessian a b (fun y => c*w y) x
  have hux : ContDiffAt ℝ 2 u x := hu.contDiffAt (hU.mem_nhds hx)
  have hwc : ContDiffAt ℝ 2 (fun y => c*w y) x := contDiffAt_const.mul hw.contDiffAt
  have hA : A.PosDef := hup x hx
  have hAd : A.det = 1 := hud x hx
  have hB : (B-(2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
    have hp := (hmargin x (subset_closure hx)).smul
      (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
    have he : (c : ℂ) • (complexHessian a b w x-(eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        B-(2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      dsimp only [B]
      rw [complexHessian_const_mul_at hw.contDiffAt,smul_sub,smul_smul,← Complex.ofReal_mul,hce]
      rfl
    rw [he] at hp
    exact hp.posSemidef
  have htrace := trace_quotient_lower_of_two_identity_margin_two hA hB
  have hmin := two_sqrt_det_re_le_trace hA.inv.posSemidef
  have hAdi : (A⁻¹).det = 1 := by simp [Matrix.det_nonsing_inv,hAd]
  rw [hAdi,Complex.one_re,Real.sqrt_one] at hmin
  have hself := complexHessianContraction_self_eq_card hux a b (by rw [hAd]; exact one_ne_zero)
  have hBtrace : complexHessianContraction a b A⁻¹ (realHessian (fun y => c*w y) x) =
      (B*A⁻¹).trace.re := by
    rw [← complexHessianContraction_pairing a b _ hwc,complex_contraction_eq_trace hwc]
  change complexHessianContraction a b A⁻¹ (realHessian (fun y => u y-c*w y) x) ≤
    -(1/2 : ℝ)*(1+(A⁻¹).trace.re)
  rw [realHessian_sub_at hux hwc,
    map_sub (complexHessianContraction a b A⁻¹) (realHessian u x)
      (realHessian (fun y => c*w y) x),hself,hBtrace]
  norm_num at *
  linarith

end PowerConvexity
