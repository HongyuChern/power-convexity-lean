import PowerConvexity.Calculus.QuadraticBallPotential
import PowerConvexity.Calculus.UniformQuadraticRobustness
import PowerConvexity.Calculus.ScalarBasis
import PowerConvexity.Algebra.ShiftedSchurSpectral

/-! # The two shifted matrix estimates in Appendix A

The strict Schur condition is stated for its Hermitian numerator. The quotient
printed in cond:BABA is in general not Hermitian; its order is spectral.
The shift is obtained from actual Hessian lower bounds supplied by quadratic
robustness. It is not a new assumption on a public Dirichlet endpoint.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem norm_square_pureHessian (a b : ι → E)
    (hab : Orthonormal ℝ (Sum.elim a b)) (x : E) :
    pureHessian a b (fun y : E => ‖y‖^2) x = 0 := by
  ext i j
  have h := orthonormal_iff_ite.mp hab
  have haa : inner ℝ (a i) (a j) = if i=j then 1 else 0 := by
    simpa using h (Sum.inl i) (Sum.inl j)
  have hbb : inner ℝ (b i) (b j) = if i=j then 1 else 0 := by
    simpa using h (Sum.inr i) (Sum.inr j)
  have hab' : inner ℝ (a i) (b j) = 0 := by simpa using h (Sum.inl i) (Sum.inr j)
  have hba : inner ℝ (b i) (a j) = 0 := by simpa using h (Sum.inr i) (Sum.inl j)
  rw [pureHessian_real_entry (contDiff_norm_sq ℝ).contDiffAt]
  simp [realHessian_norm_square, haa, hbb, hab', hba]

theorem realHessian_strict_basis_matrices {f : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (e : Module.Basis (ι ⊕ ι) ℝ E)
    (hH : ∀ v : E, v ≠ 0 → 0 < realHessian f x v v) :
    (complexHessian (fun i => e (.inl i)) (fun i => e (.inr i)) f x).PosDef ∧
    (schurHessian (fun i => e (.inl i)) (fun i => e (.inr i)) f x).PosDef := by
  let a : ι → E := fun i => e (.inl i)
  let b : ι → E := fun i => e (.inr i)
  have hr := realBlockHessian_posDef_of_basis_quadratic hf e hH
  have hc : (complexBlockHessian a b f x).PosDef := by
    rw [actual_block_congruence_scaled hf a b,
      Matrix.IsUnit.posDef_star_right_conjugate_iff (halfHessianTransform_isUnit (ι := ι))]
    exact (real_matrix_posDef_iff_complexification (realBlockHessian_isHermitian hf a b)).mp hr
  have ha : (complexHessian a b f x).PosDef := hc.submatrix Sum.inl_injective
  exact ⟨ha, (complexBlockHessian_posDef_iff hf a b ha).mp hc⟩

/-- cond:Alowerbound and the strict Hermitian form of cond:BABA, with C1=delta/2. -/
theorem shifted_matrices_of_powerHessian_lower {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (e : OrthonormalBasis (ι ⊕ ι) ℝ E) {δ : ℝ} (hδ : 0 < δ)
    (hH : ∀ v : E, 2 * δ * sqrtSlope (u x) * ‖v‖^2 ≤
      realHessian (powerTransform u) x v v) :
    let a : ι → E := fun i => e (.inl i)
    let b : ι → E := fun i => e (.inr i)
    let A := modifiedA a b u x - ((δ / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
    A.PosDef ∧ (matrixSchur A (modifiedB a b u x)).PosDef := by
  let a : ι → E := fun i => e (.inl i)
  let b : ι → E := fun i => e (.inr i)
  let s := sqrtSlope (u x)
  let c := δ * s / 2
  let f : E → ℝ := fun y => powerTransform u y + (-c) * ‖y‖^2
  let A := modifiedA a b u x - ((δ / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
  have hs : 0 < s := sqrtSlope_pos hx
  have hf : ContDiffAt ℝ 2 f x :=
    (powerTransform_contDiffAt hu hx).add (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt)
  have he : Orthonormal ℝ (Sum.elim a b) := by
    have hfun : Sum.elim a b = fun i => e i := by funext i; cases i <;> rfl
    rw [hfun]
    exact e.orthonormal
  have hF (v : E) (hv : v ≠ 0) : 0 < realHessian f x v v := by
    dsimp only [f]
    rw [realHessian_add (powerTransform_contDiffAt hu hx)
      (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt), realHessian_const_mul]
    simp only [add_apply, smul_apply, smul_eq_mul, realHessian_norm_square,
      real_inner_self_eq_norm_sq]
    have hn : 0 < ‖v‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hb := hH v
    have hp := mul_pos (mul_pos hδ hs) hn
    dsimp only [c, s] at *
    nlinarith
  have hfa : complexHessian a b f x = (s : ℂ) • A := by
    rw [complexHessian_add_at (powerTransform_contDiffAt hu hx)
      (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
      complexHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt,
      norm_square_complexHessian a b he, power_mixed_matrix hu hx]
    ext i j
    simp only [A, c, s, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      smul_eq_mul, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_mul,
      Complex.ofReal_ofNat]
    ring
  have hfb : pureHessian a b f x = (s : ℂ) • modifiedB a b u x := by
    rw [pureHessian_add_at (powerTransform_contDiffAt hu hx)
      (contDiffAt_const.mul (contDiff_norm_sq ℝ).contDiffAt),
      pureHessian_const_mul_at (contDiff_norm_sq ℝ).contDiffAt,
      norm_square_pureHessian a b he, smul_zero, add_zero, power_pure_matrix hu hx]
  obtain ⟨ha, hm⟩ := realHessian_strict_basis_matrices hf e.toBasis hF
  change (complexHessian a b f x).PosDef at ha
  rw [hfa] at ha
  have ha' := (posDef_real_smul_iff A hs).mp ha
  change (matrixSchur (complexHessian a b f x) (pureHessian a b f x)).PosDef at hm
  rw [hfa, hfb, matrixSchur_real_smul _ _ ha' hs, posDef_real_smul_iff _ hs] at hm
  exact ⟨ha', hm⟩

variable [InnerProductSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem shifted_matrices_of_holomorphic_square_tests {u : E → ℝ} {x : E}
    (hu : ContDiffAt ℝ 2 u x) (hx : u x < 0)
    (e : OrthonormalBasis (ι ⊕ ι) ℝ E) {δ : ℝ} (hδ : 0 < δ)
    (htest : ∀ ell : E →L[ℂ] ℂ, ‖ell‖ = 1 → ∀ v : E,
      0 ≤ realHessian (powerTransform (fun y =>
        u y - δ * realPartSquare (ell.restrictScalars ℝ) x y)) x v v) :
    let a : ι → E := fun i => e (.inl i)
    let b : ι → E := fun i => e (.inr i)
    let A := modifiedA a b u x - ((δ / 2 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
    A.PosDef ∧ (matrixSchur A (modifiedB a b u x)).PosDef :=
  shifted_matrices_of_powerHessian_lower hu hx e hδ
    (powerHessian_lower_of_holomorphic_square_tests hu hx hδ.le htest)

variable [MeasurableSpace E] [BorelSpace E]

/-- A single C1 depends only on the L2 radius and bounded sets of integration
and centers. It is selected before u and x, and needs no uniform spectral-gap
or Hessian premise. The quadratic-ball hypothesis is exactly robustness. -/
theorem uniform_L2_shifted_matrices (μ : MeasureTheory.Measure E)
    [MeasureTheory.IsFiniteMeasureOnCompacts μ]
    {K X : Set E} (hK : IsCompact K) (hX : Bornology.IsBounded X)
    (e : OrthonormalBasis (ι ⊕ ι) ℝ E) {ε : ℝ} (hε : 0 < ε) :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ (u : E → ℝ) (x : E), x ∈ X →
      ContDiffAt ℝ 2 u x → u x < 0 →
      (∀ q : E → ℝ,
        IsPluriharmonicQuadratic (fun i : ι => e (.inl i))
          (fun i : ι => Complex.I • e (.inl i)) q →
        quadraticL2Energy μ K q ≤ ε → ∀ v : E,
        0 ≤ realHessian (powerTransform (fun y => u y + q y)) x v v) →
      let a : ι → E := fun i => e (.inl i)
      let b : ι → E := fun i => e (.inr i)
      let A := modifiedA a b u x - (C1 : ℂ) • (1 : Matrix ι ι ℂ)
      A.PosDef ∧ (matrixSchur A (modifiedB a b u x)).PosDef ∧
      ∃ (Q : Matrix ι ι ℂ) (d : ι → ℝ), IsUnit Q.det ∧
        Q * (modifiedB a b u x * (A.map star)⁻¹ *
          (modifiedB a b u x).map star * A⁻¹) * Q⁻¹ =
          Matrix.diagonal (fun j => (d j : ℂ)) ∧
        ∀ j, 0 ≤ d j ∧ d j < 1 := by
  obtain ⟨δ,hδ,hrad⟩ := exists_uniform_square_test_L2_radius μ hK hX hε
  refine ⟨δ/2, by positivity, ?_⟩
  intro u x hx hu hux htest
  have ht : ∀ ell : E →L[ℂ] ℂ, ‖ell‖ = 1 → ∀ v : E,
      0 ≤ realHessian (powerTransform (fun y =>
        u y - δ * realPartSquare (ell.restrictScalars ℝ) x y)) x v v := by
    intro ell hell v
    have hJ (i : ι) : ell.restrictScalars ℝ (Complex.I • e (.inl i)) =
        Complex.I * ell.restrictScalars ℝ (e (.inl i)) := by
      simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
    have hq := IsPluriharmonicQuadratic_const_mul
      (realPartSquare_isPluriharmonicQuadratic (ell.restrictScalars ℝ) x
        (fun i : ι => e (.inl i)) (fun i : ι => Complex.I • e (.inl i)) hJ) (-δ)
    have hE := hrad x hx (ell.restrictScalars ℝ)
      (by simpa only [ContinuousLinearMap.norm_restrictScalars] using hell)
    simpa only [sub_eq_add_neg, neg_mul] using
      htest (fun y => -δ * realPartSquare (ell.restrictScalars ℝ) x y) hq hE v
  obtain ⟨hA,hM⟩ := shifted_matrices_of_holomorphic_square_tests hu hux e hδ ht
  exact ⟨hA, hM, schur_positive_product_similarity hA (modifiedB_transpose hu _ _) hM⟩

end PowerConvexity
