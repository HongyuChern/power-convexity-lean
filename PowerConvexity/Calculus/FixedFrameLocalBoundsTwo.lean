import PowerConvexity.Calculus.FixedFrameJetBoundsTwo

/-! # Genuine local uniform bounds from C4 regularity and the strict branch -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_eventually_uniform_norm_bound {ι F : Type*} [Fintype ι]
    [NormedAddCommGroup F] {x : E} (f : ι → E → F)
    (hf : ∀ i, ContinuousAt (f i) x) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ y in 𝓝 x, ∀ i, ‖f i y‖ ≤ K := by
  have hc : ContinuousAt (fun y => fun i => f i y) x := continuousAt_pi.mpr hf
  have he : ∀ᶠ y in 𝓝 x, ‖(fun i => f i y)‖ < ‖(fun i => f i x)‖+1 :=
    hc.norm.eventually (gt_mem_nhds (by linarith))
  refine ⟨max 1 (‖(fun i => f i x)‖+1),le_max_left _ _,?_⟩
  filter_upwards [he] with y hy
  intro i
  exact (norm_le_pi_norm (fun j => f j y) i).trans (hy.le.trans (le_max_right _ _))

theorem dz_continuousAt_of_contDiffAt_one {f : E → ℂ} {x : E}
    (hf : ContDiffAt ℝ 1 f x) (a b : E) : ContinuousAt (dz a b f) x := by
  have hd := (hf.fderiv_right (m := 0) (by norm_num)).continuousAt
  exact continuousAt_const.mul
    ((hd.clm_apply continuousAt_const).sub (continuousAt_const.mul (hd.clm_apply continuousAt_const)))

theorem fixedFrameJetBoundTwo_eventually {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 4 u x) (hx : u x < 0) (a b : Fin 2 → E)
    (hpos : (complexHessian a b u x).PosDef) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ᶠ y in 𝓝 x, fixedFrameJetBoundTwo a b u y K := by
  have hAm := modifiedA_contDiffAt_two hu hx a b
  have hA := complexHessian_contDiffAt_two hu a b
  have hiAm := field_inverse_contDiffAt_of_det_ne_zero hAm
    (ne_of_gt (modifiedA_posDef a b hx hpos).det_pos)
  have hiA := field_inverse_contDiffAt_of_det_ne_zero hA (ne_of_gt hpos.det_pos)
  obtain ⟨K₁,hK₁,h₁⟩ := exists_eventually_uniform_norm_bound
    (fun ij : Fin 2 × Fin 2 => fun y => modifiedA a b u y ij.1 ij.2)
    (fun ij => (hAm ij.1 ij.2).continuousAt)
  obtain ⟨K₂,hK₂,h₂⟩ := exists_eventually_uniform_norm_bound
    (fun ij : Fin 2 × Fin 2 => fun y => (modifiedA a b u y)⁻¹ ij.1 ij.2)
    (fun ij => (hiAm ij.1 ij.2).continuousAt)
  obtain ⟨K₃,hK₃,h₃⟩ := exists_eventually_uniform_norm_bound
    (fun ij : Fin 2 × Fin 2 => fun y => (complexHessian a b u y)⁻¹ ij.1 ij.2)
    (fun ij => (hiA ij.1 ij.2).continuousAt)
  obtain ⟨K₄,hK₄,h₄⟩ := exists_eventually_uniform_norm_bound
    (fun _ : Unit => fun y => (powerWeight (u y):ℂ))
    (fun _ => Complex.ofRealCLM.continuous.continuousAt.comp (powerWeight_contDiffAt hu hx).continuousAt)
  obtain ⟨K₅,hK₅,h₅⟩ := exists_eventually_uniform_norm_bound
    (fun i : Fin 2 => fun y => complexGradient a b u y i)
    (fun i => (complexGradient_contDiffAt_two (hu.of_le (by norm_num)) a b i).continuousAt)
  obtain ⟨K₆,hK₆,h₆⟩ := exists_eventually_uniform_norm_bound
    (fun I : Fin 4 × Fin 2 × Fin 2 × Fin 2 => fun y =>
      matrixDZ (a I.2.1) (b I.2.1) (powerHessianFieldsTwo a b u I.1) y I.2.2.1 I.2.2.2)
    (fun I => (dz_contDiffAt_one (powerHessianFieldsTwo_contDiffAt_two hu hx a b I.1 I.2.2.1 I.2.2.2)
      (a I.2.1) (b I.2.1)).continuousAt)
  obtain ⟨K₇,hK₇,h₇⟩ := exists_eventually_uniform_norm_bound
    (fun I : Fin 4 × Fin 2 × Fin 2 × Fin 2 => fun y =>
      matrixDZ (a I.2.1) (-b I.2.1) (powerHessianFieldsTwo a b u I.1) y I.2.2.1 I.2.2.2)
    (fun I => (dz_contDiffAt_one (powerHessianFieldsTwo_contDiffAt_two hu hx a b I.1 I.2.2.1 I.2.2.2)
      (a I.2.1) (-b I.2.1)).continuousAt)
  obtain ⟨K₈,hK₈,h₈⟩ := exists_eventually_uniform_norm_bound
    (fun I : Fin 2 × Fin 2 × Fin 2 × Fin 2 => fun y =>
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
