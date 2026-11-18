import PowerConvexity.Calculus.UniformStrictPshMarginTwo
import PowerConvexity.Calculus.LinearizedDirichletC0Two
import PowerConvexity.Algebra.MinkowskiDeterminantTwo

/-! # A uniform trace barrier with a bounded variable determinant

Unlike the inherited determinant-one barrier, this estimate applies to the
actual auxiliary equations f_s. Its scalar is chosen from the fixed strict
subsolution and a uniform upper density bound, before any auxiliary solution.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem inverse_trace_lower_of_det_upper_two
    {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef)
    {D : ℝ} (hD : 1 ≤ D) (hdet : A.det.re ≤ D) :
    1 ≤ D*(A⁻¹).trace.re := by
  let d := A.det.re
  let r := (A⁻¹).det.re
  let T := (A⁻¹).trace.re
  have hd : 0 < d := (Complex.pos_iff.mp hA.det_pos).1
  have hT : 0 < T := (Complex.pos_iff.mp hA.inv.trace_pos).1
  have him : A.det.im = 0 := (Complex.pos_iff.mp hA.det_pos).2.symm
  have hprod : r*d = 1 := by
    have h := congrArg Complex.re (A.det_nonsing_inv_mul_det
      (isUnit_iff_ne_zero.mpr hA.det_pos.ne'))
    simpa only [Complex.mul_re,him,mul_zero,sub_zero,Complex.one_re] using h
  have hdisc : 4*r ≤ T^2 := hermitian_trace_discriminant_nonneg_two hA.inv.isHermitian
  have hfour : 4 ≤ d*T^2 := by
    have h := mul_le_mul_of_nonneg_left hdisc hd.le
    nlinarith [hprod]
  by_contra hn
  have hDT : D*T < 1 := lt_of_not_ge hn
  have hTone : T < 1 := by
    have h := mul_le_mul_of_nonneg_right hD hT.le
    nlinarith
  have hsq : T^2 ≤ T := by nlinarith
  have hcomp : d*T^2 ≤ D*T :=
    (mul_le_mul_of_nonneg_right hdet (sq_nonneg T)).trans
      (mul_le_mul_of_nonneg_left hsq (by linarith : 0 ≤ D))
  linarith

theorem trace_quotient_lower_of_scalar_margin_two
    {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.PosDef) {k : ℝ}
    (hB : (B-(k : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef) :
    k*(A⁻¹).trace.re ≤ (B*A⁻¹).trace.re := by
  have hh := CHS.Algebra.trace_product_posSemidef_nonneg hB hA.inv.posSemidef
  rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul] at hh
  simp only [smul_eq_mul,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] at hh
  linarith

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [FiniteDimensional ℝ E]

theorem strictPsh_variable_density_uniform_trace_barrier_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {U : Set E} (hU : IsOpen U) (hK : IsCompact (closure U))
    {w : E → ℝ} (hw : ContDiff ℝ 2 w)
    (hwp : ∀ x ∈ closure U, (complexHessian e (fun j => Complex.I • e j) w x).PosDef)
    {D : ℝ} (hD : 1 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E → ℝ, ContDiffOn ℝ 2 u U →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
      (∀ x ∈ U, (complexHessian e (fun j => Complex.I • e j) u x).det.re ≤ D) →
      ∀ x ∈ U,
        linearizedCMAOperatorTwo e (fun j => Complex.I • e j) u
          (fun y => u y-c*w y) x ≤
          -(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re) := by
  obtain ⟨eps,heps,hmargin⟩ := compact_strictPsh_has_uniform_scalar_margin_two e hab hK hw hwp
  let k : ℝ := 3*D+1
  have hk : 0 < k := by dsimp only [k]; linarith
  let c : ℝ := k/eps
  have hc : 0 < c := div_pos hk heps
  have hce : c*eps = k := div_mul_cancel₀ _ heps.ne'
  refine ⟨c,hc,?_⟩
  intro u hu hup hud x hx
  let a := e
  let b := fun j => Complex.I • e j
  let A := complexHessian a b u x
  let B := complexHessian a b (fun y => c*w y) x
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hwc : ContDiffAt ℝ 2 (fun y => c*w y) x := contDiffAt_const.mul hw.contDiffAt
  have hA : A.PosDef := hup x hx
  have hB : (B-(k : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
    have hp := (hmargin x (subset_closure hx)).smul
      (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
    have he : (c : ℂ) • (complexHessian a b w x-(eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        B-(k : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      dsimp only [B]
      rw [complexHessian_const_mul_at hw.contDiffAt,smul_sub,smul_smul,← Complex.ofReal_mul,hce]
    rw [he] at hp
    exact hp.posSemidef
  have htrace := trace_quotient_lower_of_scalar_margin_two hA hB
  have hmin := inverse_trace_lower_of_det_upper_two hA hD (hud x hx)
  have hself := linearizedCMAOperatorTwo_self a b hux hA
  have hBtrace : complexHessianContraction a b A⁻¹ (realHessian (fun y => c*w y) x) =
      (B*A⁻¹).trace.re := by
    rw [← complexHessianContraction_pairing a b _ hwc,complex_contraction_eq_trace hwc]
  change complexHessianContraction a b A⁻¹ (realHessian (fun y => u y-c*w y) x) ≤
    -(1+(A⁻¹).trace.re)
  rw [realHessian_sub_at hux hwc,
    map_sub (complexHessianContraction a b A⁻¹) (realHessian u x)
      (realHessian (fun y => c*w y) x),hBtrace]
  change linearizedCMAOperatorTwo a b u u x-(B*A⁻¹).trace.re ≤ -(1+(A⁻¹).trace.re)
  rw [hself]
  dsimp only [k] at htrace
  nlinarith

end PowerConvexity
