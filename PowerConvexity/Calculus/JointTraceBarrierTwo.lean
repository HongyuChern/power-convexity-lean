import PowerConvexity.Calculus.JointStrictPshMarginTwo
import PowerConvexity.Calculus.StrongLinearizedSubsolutionBarrierTwo

/-! # One trace-absorbing linearized barrier before the domain parameter -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E]

theorem joint_strictPsh_scaled_uniform_trace_barrier_two
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {V : ℝ → Set E} {s d : ℝ} (hd : 0 < d)
    (hgraph : IsCompact {q : ℝ × E | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 ∈ closure (V q.1)})
    (hOpen : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → IsOpen (V t))
    {w : ℝ × E → ℝ} (hw : ContDiffOn ℝ 4 w (ball s (2*d) ×ˢ (univ : Set E)))
    (hwp : ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 → ∀ x ∈ closure (V t),
      (complexHessian e (fun j => Complex.I • e j) (fun y => w (t,y)) x).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ t ∈ closedBall s d, t ∈ Icc (0 : ℝ) 1 →
      ∀ u : E → ℝ, ContDiffOn ℝ 2 u (V t) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).PosDef) →
        (∀ x ∈ V t, (complexHessian e (fun j => Complex.I • e j) u x).det = 1) →
        ∀ x ∈ V t,
          complexHessianContraction e (fun j => Complex.I • e j)
            (complexHessian e (fun j => Complex.I • e j) u x)⁻¹
            (realHessian (fun y => u y-c*w (t,y)) x) ≤
          -(1/2 : ℝ)*(1+((complexHessian e (fun j => Complex.I • e j) u x)⁻¹).trace.re) := by
  obtain ⟨eps,heps,hmargin⟩ := joint_strictPsh_has_uniform_scalar_and_paired_margin_two
    e hab hd hgraph hw hwp
  let c : ℝ := 2/eps
  have hc : 0 < c := div_pos (by norm_num) heps
  have hce : c*eps = 2 := div_mul_cancel₀ _ heps.ne'
  refine ⟨c,hc,?_⟩
  intro t ht hI u hu hup hud x hx
  let a := e
  let b := fun j => Complex.I • e j
  let A := complexHessian a b u x
  let B := complexHessian a b (fun y => c*w (t,y)) x
  have hux : ContDiffAt ℝ 2 u x := hu.contDiffAt ((hOpen t ht hI).mem_nhds hx)
  have hwq : ContDiffAt ℝ 2 w (t,x) :=
    (hw.contDiffAt ((isOpen_ball.prod isOpen_univ).mem_nhds
      ⟨closedBall_subset_ball (by linarith : d < 2*d) ht,mem_univ x⟩)).of_le (by norm_num)
  have hwx : ContDiffAt ℝ 2 (fun y => w (t,y)) x :=
    hwq.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hwc : ContDiffAt ℝ 2 (fun y => c*w (t,y)) x := contDiffAt_const.mul hwx
  have hA : A.PosDef := hup x hx
  have hAd : A.det = 1 := hud x hx
  have hB : (B-(2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).PosSemidef := by
    have hp := ((hmargin t ht hI x (subset_closure hx)).1).smul
      (show (0 : ℂ) < (c : ℂ) from Complex.pos_iff.mpr ⟨hc,by simp⟩)
    have he : (c : ℂ) • (complexHessian a b (fun y => w (t,y)) x -
        (eps : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
        B-(2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
      dsimp only [B]
      rw [complexHessian_const_mul_at hwx,smul_sub,smul_smul,← Complex.ofReal_mul,hce]
      rfl
    rw [he] at hp
    exact hp.posSemidef
  have htrace := trace_quotient_lower_of_two_identity_margin_two hA hB
  have hmin := two_sqrt_det_re_le_trace hA.inv.posSemidef
  have hAdi : (A⁻¹).det = 1 := by simp [Matrix.det_nonsing_inv,hAd]
  rw [hAdi,Complex.one_re,Real.sqrt_one] at hmin
  have hself := complexHessianContraction_self_eq_card hux a b (by rw [hAd]; exact one_ne_zero)
  have hBtrace : complexHessianContraction a b A⁻¹ (realHessian (fun y => c*w (t,y)) x) =
      (B*A⁻¹).trace.re := by
    rw [← complexHessianContraction_pairing a b _ hwc,complex_contraction_eq_trace hwc]
  change complexHessianContraction a b A⁻¹ (realHessian (fun y => u y-c*w (t,y)) x) ≤
    -(1/2 : ℝ)*(1+(A⁻¹).trace.re)
  rw [realHessian_sub_at hux hwc,
    map_sub (complexHessianContraction a b A⁻¹) (realHessian u x)
      (realHessian (fun y => c*w (t,y)) x),hself,hBtrace]
  norm_num at *
  linarith

end PowerConvexity
