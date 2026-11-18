import PowerConvexity.Calculus.LinearizationCovariance
import PowerConvexity.Calculus.QuadraticTaylor
import PowerConvexity.Calculus.UniformNormalizedAOperatorJetsTwo

/-! # Frame-independent local ellipticity of the actual linearized operator

The frame is constant while taking derivatives. Quadratic test functions
transfer the rank-one and trace forms without choosing a differentiable frame.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem complexHessianContraction_complexFrame_symmetric
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E)
    (H : E →L[ℝ] E →L[ℝ] ℝ) (hs : ∀ v w, H v w = H w v) :
    complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
      (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹ H =
      complexHessianContraction a b (complexHessian a b u x)⁻¹ H := by
  let J : E →L[ℝ] E →L[ℝ] ℝ := (1/2:ℝ) • H
  let q : E → ℝ := fun y => 0+(0 : E →L[ℝ] ℝ) y+J y y
  have hJ : ∀ v w, J v w = J w v := by
    intro v w
    simp only [J,smul_apply,smul_eq_mul,hs v w]
  have hq : ContDiffAt ℝ 2 q x :=
    (IsQuadraticPolynomial_contDiff ⟨0,0,J,hJ,fun _ => rfl⟩ 2).contDiffAt
  have hH : realHessian q x = H := by
    rw [quadratic_coeff_realHessian 0 0 J hJ x]
    simp only [J,smul_smul]
    norm_num
  have hh := congrArg Complex.re (complex_contraction_complexFrame hu hq Q hQ a b)
  rw [complexHessianContraction_pairing _ _ _ hq,
    complexHessianContraction_pairing _ _ _ hq,hH] at hh
  exact hh

theorem complexHessianContraction_complexFrame_rankOne
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E) (v : E) :
    complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
      (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹
        (realRankOneForm v) =
      complexHessianContraction a b (complexHessian a b u x)⁻¹ (realRankOneForm v) := by
  apply complexHessianContraction_complexFrame_symmetric hu Q hQ a b
  intro w z
  simp only [realRankOneForm,ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply,smul_apply,smul_eq_mul]
  ring

theorem complexHessianContraction_complexFrame_trace
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x)
    (Q : Matrix ι ι ℂ) (hQ : IsUnit Q.det) (a b : ι → E) :
    complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
      (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u x)⁻¹
        (realInnerForm (E := E)) =
      complexHessianContraction a b (complexHessian a b u x)⁻¹
        (realInnerForm (E := E)) := by
  apply complexHessianContraction_complexFrame_symmetric hu Q hQ a b
  intro v w
  exact (real_inner_comm v w).symm

theorem hessianPositive_contraction_le_norm_trace
    (L : (E →L[ℝ] E →L[ℝ] ℝ) →ₗ[ℝ] ℝ) (hL : HessianPositive L)
    (H : E →L[ℝ] E →L[ℝ] ℝ) {K Λ : ℝ} (hK : 0 ≤ K)
    (hH : ‖H‖ ≤ K) (htrace : L (realInnerForm (E := E)) ≤ Λ) :
    L H ≤ K*Λ := by
  have hh := hL (K • realInnerForm (E := E)-H) (by
    intro v
    have h1 := (H v).le_opNorm v
    have h2 := mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg v)
    have h3 := mul_le_mul_of_nonneg_right hH (sq_nonneg ‖v‖)
    have h4 : H v v ≤ ‖H v v‖ := le_abs_self _
    change 0 ≤ K*inner ℝ v v-H v v
    rw [real_inner_self_eq_norm_sq]
    nlinarith only [h1,h2,h3,h4])
  change 0 ≤ L (K • realInnerForm (E := E)-H) at hh
  rw [map_sub L,map_smul L,smul_eq_mul] at hh
  have ht := mul_le_mul_of_nonneg_left htrace hK
  linarith

variable [ProperSpace E] [Nontrivial E]

theorem exists_uniform_complexFrame_ellipticity
    (a b : ι → E) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (he : (e : (ι ⊕ ι) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    ∃ ell Λ : ℝ, 0 < ell ∧ 0 ≤ Λ ∧ ∀ᶠ y in 𝓝 x,
      ∀ Q : Matrix ι ι ℂ, IsUnit Q.det →
        (∀ v : E, ell*‖v‖^2 ≤
          complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
            (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u y)⁻¹
              (realRankOneForm v)) ∧
        complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
          (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u y)⁻¹
            (realInnerForm (E := E)) ≤ Λ := by
  obtain ⟨r,hr,hrU⟩ := Metric.isOpen_iff.mp hU x hx
  have hr2 : 0 < r/2 := by positivity
  have hKU : closedBall x (r/2) ⊆ U :=
    (closedBall_subset_ball (by linarith : r/2 < r)).trans hrU
  obtain ⟨ell,Λ,hell,hΛ,hlow,htrace⟩ := compact_matrixHessianContraction_bounds e
    (isCompact_closedBall x (r/2)) ⟨x,mem_closedBall_self hr2.le⟩
    (fun i j => (strictPsh_realCoefficients_continuousOn a b hU hu hpos i j).mono hKU)
    (fun y hy => realLinearizationMatrix_posDef (hpos y (hKU hy)).inv)
  refine ⟨ell,Λ,hell,hΛ,?_⟩
  filter_upwards [ball_mem_nhds x hr2] with y hy
  have hyK := ball_subset_closedBall hy
  have hy2 : ContDiffAt ℝ 2 u y := (hu.contDiffAt (hU.mem_nhds (hKU hyK))).of_le (by norm_num)
  intro Q hQ
  constructor
  · intro v
    rw [complexHessianContraction_complexFrame_rankOne hy2 Q hQ a b v]
    simpa only [complexHessianContraction,he] using hlow y hyK v
  · rw [complexHessianContraction_complexFrame_trace hy2 Q hQ a b]
    simpa only [complexHessianContraction,he] using htrace y hyK

/-- This already consumes C102: the bounded actual A-Hessians are contracted by
the actual inverse complex Hessian, uniformly over every normalizing frame. -/
theorem exists_uniform_normalized_A_linearized_bounds_two
    (a b : Fin 2 → E) (e : Module.Basis (Fin 2 ⊕ Fin 2) ℝ E)
    (he : (e : (Fin 2 ⊕ Fin 2) → E) = Sum.elim a b)
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} (hu : ContDiffOn ℝ 4 u U)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef) {x : E} (hx : x ∈ U) :
    ∃ K ell Λ : ℝ, 1 ≤ K ∧ 0 < ell ∧ 0 ≤ Λ ∧ ∀ᶠ y in 𝓝 x,
      ∀ Q : Matrix (Fin 2) (Fin 2) ℂ, IsUnit Q.det →
      modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u y = 1 →
      (∀ v : E, ell*‖v‖^2 ≤
        complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
          (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u y)⁻¹
            (realRankOneForm v)) ∧
      (complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
        (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u y)⁻¹
          (realInnerForm (E := E)) ≤ Λ) ∧
      ∀ i j,
        ‖fderiv ℝ (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).re) y‖ ≤ K ∧
        ‖fderiv ℝ (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).im) y‖ ≤ K ∧
        ‖realHessian (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).re) y‖ ≤ K ∧
        complexHessianContraction (complexFrameReal Q a b) (complexFrameImag Q a b)
          (complexHessian (complexFrameReal Q a b) (complexFrameImag Q a b) u y)⁻¹
            (realHessian (fun z => (modifiedA (complexFrameReal Q a b) (complexFrameImag Q a b) u z i j).re) y) ≤ K*Λ := by
  obtain ⟨K,hK,hjets⟩ := exists_uniform_normalized_A_operator_jets_two hU hu a b hneg hpos hx
  obtain ⟨ell,Λ,hell,hΛ,helliptic⟩ := exists_uniform_complexFrame_ellipticity a b e he hU hu hpos hx
  refine ⟨K,ell,Λ,hK,hell,hΛ,?_⟩
  filter_upwards [hU.mem_nhds hx,hjets,helliptic] with y hy hj helli
  intro Q hQ hI
  obtain ⟨hlow,htrace⟩ := helli Q hQ
  have hpos' := (complexHessian_posDef_complexFrame_iff
    ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) Q hQ a b).mpr (hpos y hy)
  refine ⟨hlow,htrace,?_⟩
  intro i j
  obtain ⟨hdRe,hdIm,hhRe,_⟩ := hj Q hQ hI i j
  exact ⟨hdRe,hdIm,hhRe,hessianPositive_contraction_le_norm_trace _
    (complexHessianContraction_positive _ _ hpos'.inv) _ (by linarith) hhRe htrace⟩

end PowerConvexity
