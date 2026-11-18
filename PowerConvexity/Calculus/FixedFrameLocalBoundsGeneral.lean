import PowerConvexity.Calculus.FixedFrameLocalBoundsTwo
import PowerConvexity.Calculus.FixedFrameJetBoundsGeneral

/-! # Genuine local uniform bounds from C4 regularity and the strict branch -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fixedFrameJetBoundGeneral_eventually {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : ι → E)
    (hpos : (complexHessian a b u x).PosDef) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ y in 𝓝 x, fixedFrameJetBoundGeneral a b u y K := by
  have hAm := modifiedA_contDiffAt_two hu hx a b
  have hA := complexHessian_contDiffAt_two hu a b
  have hiAm := field_inverse_contDiffAt_of_det_ne_zero hAm
    (ne_of_gt (modifiedA_posDef a b hx hpos).det_pos)
  have hiA := field_inverse_contDiffAt_of_det_ne_zero hA (ne_of_gt hpos.det_pos)
  obtain ⟨K₁,hK₁,h₁⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => modifiedA a b u y ij.1 ij.2)
    (fun ij => (hAm ij.1 ij.2).continuousAt)
  obtain ⟨K₂,hK₂,h₂⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => (modifiedA a b u y)⁻¹ ij.1 ij.2)
    (fun ij => (hiAm ij.1 ij.2).continuousAt)
  obtain ⟨K₃,hK₃,h₃⟩ := exists_eventually_uniform_norm_bound
    (fun ij : ι × ι => fun y => (complexHessian a b u y)⁻¹ ij.1 ij.2)
    (fun ij => (hiA ij.1 ij.2).continuousAt)
  obtain ⟨K₄,hK₄,h₄⟩ := exists_eventually_uniform_norm_bound
    (fun _ : Unit => fun y => (powerWeight (u y):ℂ))
    (fun _ => Complex.ofRealCLM.continuous.continuousAt.comp (powerWeight_contDiffAt hu hx).continuousAt)
  obtain ⟨K₅,hK₅,h₅⟩ := exists_eventually_uniform_norm_bound
    (fun i : ι => fun y => complexGradient a b u y i)
    (fun i => (complexGradient_contDiffAt_two (hu.of_le (by norm_num)) a b i).continuousAt)
  obtain ⟨K₆,hK₆,h₆⟩ := exists_eventually_uniform_norm_bound
    (fun I : Fin 4 × ι × ι × ι => fun y =>
      matrixDZ (a I.2.1) (b I.2.1) (powerHessianFieldsGeneral a b u I.1) y I.2.2.1 I.2.2.2)
    (fun I => (dz_contDiffAt_one (powerHessianFieldsGeneral_contDiffAt_two hu hx a b I.1 I.2.2.1 I.2.2.2)
      (a I.2.1) (b I.2.1)).continuousAt)
  obtain ⟨K₇,hK₇,h₇⟩ := exists_eventually_uniform_norm_bound
    (fun I : Fin 4 × ι × ι × ι => fun y =>
      matrixDZ (a I.2.1) (-b I.2.1) (powerHessianFieldsGeneral a b u I.1) y I.2.2.1 I.2.2.2)
    (fun I => (dz_contDiffAt_one (powerHessianFieldsGeneral_contDiffAt_two hu hx a b I.1 I.2.2.1 I.2.2.2)
      (a I.2.1) (-b I.2.1)).continuousAt)
  obtain ⟨K₈,hK₈,h₈⟩ := exists_eventually_uniform_norm_bound
    (fun I : ι × ι × ι × ι => fun y =>
      matrixDZ (a I.2.1) (-b I.2.1) (matrixDZ (a I.1) (b I.1) (modifiedA a b u)) y I.2.2.1 I.2.2.2)
    (fun I => dz_continuousAt_of_contDiffAt_one
      (dz_contDiffAt_one (hAm I.2.2.1 I.2.2.2) (a I.1) (b I.1)) (a I.2.1) (-b I.2.1))
  let K := K₁+K₂+K₃+K₄+K₅+K₆+K₇+K₈+1+‖a‖+‖b‖
  have hK : 1 ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₁K : K₁ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₂K : K₂ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₃K : K₃ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₄K : K₄ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₅K : K₅ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₆K : K₆ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₇K : K₇ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have h₈K : K₈ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have haK : ‖a‖ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  have hbK : ‖b‖ ≤ K := by dsimp [K]; linarith [norm_nonneg a,norm_nonneg b]
  refine ⟨K,hK,?_⟩
  filter_upwards [h₁,h₂,h₃,h₄,h₅,h₆,h₇,h₈] with y hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hy₈
  exact ⟨(fun i j => (hy₁ (i,j)).trans h₁K),(fun i j => (hy₂ (i,j)).trans h₂K),
    (fun i j => (hy₃ (i,j)).trans h₃K),(hy₄ ()).trans h₄K,
    (fun i => (hy₅ i).trans h₅K),
    (fun k p i j => (hy₆ (k,p,i,j)).trans h₆K),
    (fun k q i j => (hy₇ (k,q,i,j)).trans h₇K),
    (fun p q i j => (hy₈ (p,q,i,j)).trans h₈K),
    (fun i => (norm_le_pi_norm a i).trans haK),(fun i => (norm_le_pi_norm b i).trans hbK)⟩

end PowerConvexity
