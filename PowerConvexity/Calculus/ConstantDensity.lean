import PowerConvexity.Calculus.MatrixInverse

/-!
# The full matrix differential identities at arbitrary nonzero constant density

This transfers the locked CHS determinant-one proof to `det A = ρ ≠ 0`.
The inverse is differentiated on its nonsingular locus.  All third and fourth
order terms are the actual derivatives of the same real potential.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexHessian_det_const_second {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) (v w s t : E) :
    Matrix.trace ((complexHessian a b u x)⁻¹ *
      matrixDZ s t (matrixDZ v w (complexHessian a b u)) x) =
      Matrix.trace ((complexHessian a b u x)⁻¹ *
        matrixDZ s t (complexHessian a b u) x * (complexHessian a b u x)⁻¹ *
        matrixDZ v w (complexHessian a b u) x) := by
  let A := complexHessian a b u
  have hdetAt (y : E) (hy : y ∈ U) :
      (fun z => (A z).det) =ᶠ[𝓝 y] (fun _ => ρ) :=
    Filter.Eventually.mono (hU.mem_nhds hy) hdet
  have hTrace : (fun y => Matrix.trace ((A y)⁻¹ * matrixDZ v w A y)) =ᶠ[𝓝 x]
      (fun _ => (0 : ℂ)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hy3 : ContDiffAt ℝ 3 u y :=
      (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
    have h := complexHessian_det_const_first hy3 a b (hdetAt y hy) v w
    change (∑ i, ∑ j, (A y)⁻¹ i j * dz v w (fun z => A z j i) y) = 0
    rw [Finset.sum_comm]
    exact h
  have hA2 := complexHessian_contDiffAt_two (hu.contDiffAt (hU.mem_nhds hx)) a b
  have hA1 : MatrixDifferentiableAt A x :=
    fun i j => (hA2 i j).differentiableAt (by norm_num)
  have hn : (A x).det ≠ 0 := by rw [hdet x hx]; exact hρ
  have hInv := field_inverse_differentiableAt_of_det_ne_zero hA1 hn
  have hDZ := matrixDZ_differentiableAt hA2 v w
  have hProd := matrix_product_differentiable hInv hDZ
  have hTraceDeriv :
      Matrix.trace (matrixDZ s t (fun y => (A y)⁻¹ * matrixDZ v w A y) x) = 0 := by
    have h := dz_congr_nhds hTrace s t
    rw [dz_const] at h
    change (∑ i, dz s t (fun y => ((A y)⁻¹ * matrixDZ v w A y) i i) x) = 0
    rw [← dz_sum_at (fun i => hProd i i)]
    exact h
  rw [matrixDZ_product s t hInv hDZ,
    matrixDZ_inverse_of_det_ne_zero s t hA1 hn, Matrix.neg_mul,
    Matrix.trace_add, Matrix.trace_neg, neg_add_eq_sub, sub_eq_zero] at hTraceDeriv
  exact hTraceDeriv

theorem linearized_secondDerivative_det_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) (v w s t : E) :
    (∑ p, ∑ q, (complexHessian a b u x)⁻¹ q p *
      dz (a q) (-b q) (dz (a p) (b p)
        (dz s t (dz v w (fun y => (u y : ℂ))))) x) =
      Matrix.trace ((complexHessian a b u x)⁻¹ *
        matrixDZ s t (complexHessian a b u) x * (complexHessian a b u x)⁻¹ *
        matrixDZ v w (complexHessian a b u) x) :=
  (linearized_secondDerivative_eq_trace hU hu a b hx v w s t).trans
    (complexHessian_det_const_second hU hu a b hρ hdet hx v w s t)

private theorem trace_four_factors (W X Y : Matrix ι ι ℂ) :
    Matrix.trace (W * X * W * Y) =
      ∑ q, ∑ p, ∑ r, ∑ t, W q p * X p r * W r t * Y t q := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  calc
    _ = ∑ t, ∑ p, ∑ r, W q p * X p r * W r t * Y t q :=
      Finset.sum_congr rfl fun t _ => Finset.sum_comm
    _ = ∑ p, ∑ t, ∑ r, W q p * X p r * W r t * Y t q := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun p _ => Finset.sum_comm

/-- The first product expressions in the paper's equations (2.2) and (2.3). -/
theorem linearized_hessians_first_products_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let W := (A x)⁻¹
    (∀ G : E → Matrix ι ι ℂ, (G = A ∨ G = B) →
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x) =
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a p) (b p) A x * W * matrixDZ (a q) (-b q) G x)) := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let W := (A x)⁻¹
  let f : E → ℂ := fun y => (u y : ℂ)
  have hf4 : ContDiffOn ℝ 4 f U := Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hf3 : ContDiffOn ℝ 3 f U := hf4.of_le (by norm_num)
  have hfx := hf3.contDiffAt (hU.mem_nhds hx)
  have hux : ContDiffAt ℝ 3 u x :=
    (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hcomm (j : ι) (v : E) (q t : ι) :
      matrixDZ (a j) v A x t q =
        dz (a q) (-b q) (dz (a t) (b t) (dz (a j) v f)) x := by
    change dz (a j) v (dz (a t) (b t) (dz (a q) (-b q) f)) x = _
    calc
      _ = dz (a j) v (dz (a q) (-b q) (dz (a t) (b t) f)) x :=
        third_inner_comm_on hU hf3 _ _ _ _ _ _ hx
      _ = dz (a q) (-b q) (dz (a j) v (dz (a t) (b t) f)) x :=
        third_outer_comm_at hfx _ _ _ _ _ _
      _ = _ := third_inner_comm_on hU hf3 _ _ _ _ _ _ hx
  have hentry (G : E → Matrix ι ι ℂ) (i j : ι) (v : E)
      (hG : ∀ r, (fun y => G y r j) = dz (a r) (b r) (dz (a j) v f)) :
      (CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x)) i j =
      (CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a p) (b p) A x * W * matrixDZ (a q) (-b q) G x)) i j := by
    have hsecond := linearized_secondDerivative_det_const hU hu a b hρ hdet hx
      (a j) v (a i) (b i)
    let T (p q r t : ι) :=
      W q p * matrixDZ (a p) (b p) A x i r * W r t * matrixDZ (a q) (-b q) G x t j
    have hderiv (p q : ι) :
        (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x) i j =
          dz (a q) (-b q) (dz (a p) (b p) (dz (a i) (b i) (dz (a j) v f))) x := by
      change dz (a q) (-b q) (dz (a p) (b p) (fun y => G y i j)) x = _
      rw [hG i]
    simp only [CHS.SchurContractionCore.contract, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, hderiv]
    calc
      _ = Matrix.trace (W * matrixDZ (a i) (b i) A x * W * matrixDZ (a j) v A x) :=
        hsecond
      _ = ∑ q, ∑ p, ∑ r, ∑ t, T p q r t := by
        rw [trace_four_factors]
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro t _
        have hrow : matrixDZ (a i) (b i) A x p r = matrixDZ (a p) (b p) A x i r :=
          complexHessian_row_comm hux a b i p r
        have hcol : matrixDZ (a j) v A x t q = matrixDZ (a q) (-b q) G x t j := by
          rw [hcomm]
          change _ = dz (a q) (-b q) (fun y => G y t j) x
          rw [hG t]
        unfold T
        rw [hrow, hcol]
      _ = ∑ p, ∑ q, ∑ r, ∑ t, T p q r t := Finset.sum_comm
      _ = _ := by
        simp only [T, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        exact Finset.sum_comm
  dsimp only
  intro G hG
  rcases hG with rfl | rfl
  · ext i j
    exact hentry A i j (-b j) (fun r => rfl)
  · ext i j
    exact hentry B i j (b j) (fun r => rfl)

private theorem sum_rotate_four (T : ι → ι → ι → ι → ℂ) :
    (∑ t, ∑ r, ∑ q, ∑ p, T p q r t) = ∑ p, ∑ q, ∑ r, ∑ t, T p q r t := by
  calc
    _ = ∑ t, ∑ r, ∑ p, ∑ q, T p q r t :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ t, ∑ p, ∑ r, ∑ q, T p q r t :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p, ∑ t, ∑ r, ∑ q, T p q r t := Finset.sum_comm
    _ = ∑ p, ∑ t, ∑ q, ∑ r, T p q r t :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ p, ∑ q, ∑ t, ∑ r, T p q r t :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The conjugate product expressions in (2.2) and (2.3), using the transpose
of the inverse mixed Hessian as the conjugate inverse. -/
theorem linearized_hessians_conjugate_products_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let W := (A x)⁻¹
    let L := fun G : E → Matrix ι ι ℂ =>
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x)
    let P := fun C : E → Matrix ι ι ℂ =>
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) B x * W.transpose *
          matrixDZ (a p) (b p) C x)
    L A = P (pureHessian a (fun i => -b i) u) ∧ L B = P (fun y => (A y).transpose) := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let W := (A x)⁻¹
  let f : E → ℂ := fun y => (u y : ℂ)
  have hf4 : ContDiffOn ℝ 4 f U := Complex.ofRealCLM.contDiff.comp_contDiffOn hu
  have hf3 : ContDiffOn ℝ 3 f U := hf4.of_le (by norm_num)
  have hfx := hf3.contDiffAt (hU.mem_nhds hx)
  have hentry (G C : E → Matrix ι ι ℂ) (i j : ι) (v : E)
      (hG : (fun y => G y i j) = dz (a i) (b i) (dz (a j) v f))
      (hC : ∀ r, (fun y => C y r j) =ᶠ[𝓝 x] dz (a j) v (dz (a r) (-b r) f)) :
      (CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x)) i j =
      (CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) B x * W.transpose * matrixDZ (a p) (b p) C x)) i j := by
    let T (p q r t : ι) :=
      W q p * matrixDZ (a q) (-b q) B x i r * W t r * matrixDZ (a p) (b p) C x t j
    have hderiv (p q : ι) :
        (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x) i j =
          dz (a q) (-b q) (dz (a p) (b p) (dz (a i) (b i) (dz (a j) v f))) x := by
      change dz (a q) (-b q) (dz (a p) (b p) (fun y => G y i j)) x = _
      rw [hG]
    simp only [CHS.SchurContractionCore.contract, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, hderiv]
    calc
      _ = Matrix.trace (W * matrixDZ (a i) (b i) A x * W * matrixDZ (a j) v A x) :=
        linearized_secondDerivative_det_const hU hu a b hρ hdet hx (a j) v (a i) (b i)
      _ = ∑ t, ∑ r, ∑ q, ∑ p, T p q r t := by
        rw [trace_four_factors]
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro q _
        apply Finset.sum_congr rfl
        intro p _
        have hfirst : matrixDZ (a i) (b i) A x r q = matrixDZ (a q) (-b q) B x i r := by
          change dz (a i) (b i) (dz (a r) (b r) (dz (a q) (-b q) f)) x =
            dz (a q) (-b q) (dz (a i) (b i) (dz (a r) (b r) f)) x
          calc
            _ = dz (a i) (b i) (dz (a q) (-b q) (dz (a r) (b r) f)) x :=
              third_inner_comm_on hU hf3 _ _ _ _ _ _ hx
            _ = _ := third_outer_comm_at hfx _ _ _ _ _ _
        have hlast : matrixDZ (a j) v A x p t = matrixDZ (a p) (b p) C x t j := by
          change dz (a j) v (dz (a p) (b p) (dz (a t) (-b t) f)) x =
            dz (a p) (b p) (fun y => C y t j) x
          rw [dz_congr_nhds (hC t) (a p) (b p)]
          exact third_outer_comm_at hfx _ _ _ _ _ _
        unfold T
        rw [hfirst, hlast]
        ring
      _ = ∑ p, ∑ q, ∑ r, ∑ t, T p q r t := sum_rotate_four T
      _ = _ := by
        simp only [T, Matrix.mul_apply, Matrix.transpose_apply,
          Finset.sum_mul, Finset.mul_sum, mul_assoc]
        apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro q _
        exact Finset.sum_comm
  dsimp only
  constructor
  · ext i j
    apply hentry A _ i j (-b j) rfl
    intro r
    filter_upwards [hU.mem_nhds hx] with y hy
    exact dz_comm_at ((hf3.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) _ _ _ _
  · ext i j
    exact hentry B _ i j (b j) rfl (fun _ => Filter.EventuallyEq.rfl)

private theorem contract_star_flip (W : Matrix ι ι ℂ) (hW : W.IsHermitian)
    (F : ι → ι → Matrix ι ι ℂ) (i j : ι) :
    star ((CHS.SchurContractionCore.contract W F) i j) =
      (CHS.SchurContractionCore.contract W (fun p q r s => star (F q p r s))) i j := by
  simp only [CHS.SchurContractionCore.contract, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, star_sum, star_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  have hcoeff : star (W p q) = W q p := hW.apply q p
  rw [hcoeff]
  change star (F q p i j) * W q p = W q p * star (F q p i j)
  exact mul_comm _ _

private theorem matrix_map_star_mul (F G : Matrix ι ι ℂ) :
    (F * G).map star = F.map star * G.map star :=
  Matrix.map_mul (f := starRingEnd ℂ)

/-- Conjugating the first product formula for either Hessian. -/
theorem linearized_conjugate_first_product_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) (G : E → Matrix ι ι ℂ)
    (hG : G = complexHessian a b u ∨ G = pureHessian a b u) :
    let A := complexHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (G y).map star
    let W := (A x)⁻¹
    CHS.SchurContractionCore.contract W (fun p q =>
      matrixDZ (a p) (b p) (matrixDZ (a q) (-b q) C) x) =
    CHS.SchurContractionCore.contract W (fun p q =>
      matrixDZ (a q) (-b q) H x * W.transpose * matrixDZ (a p) (b p) C x) := by
  let A := complexHessian a b u
  let C := fun y => (G y).map star
  let W := (A x)⁻¹
  have hu2 : ContDiffAt ℝ 2 u x :=
    (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have hW : W.IsHermitian := (complexHessian_isHermitian hu2 a b).inv
  have hProduct := linearized_hessians_first_products_const hU hu a b hρ hdet hx G hG
  ext i j
  have h := congrArg (fun F : Matrix ι ι ℂ => star (F i j)) hProduct
  rw [contract_star_flip W hW, contract_star_flip W hW] at h
  change (CHS.SchurContractionCore.contract W (fun p q =>
      (matrixDZ (a p) (-b p) (matrixDZ (a q) (b q) G) x).map star)) i j =
    (CHS.SchurContractionCore.contract W (fun p q =>
      (matrixDZ (a q) (b q) A x * W * matrixDZ (a p) (-b p) G x).map star)) i j at h
  have hinner (q : ι) :
      matrixDZ (a q) (-b q) C =
        (fun y => (matrixDZ (a q) (b q) G y).map star) := by
    funext y
    change matrixDZ (a q) (-b q) (fun z => (G z).map star) y = _
    simp only [matrixDZ_map_star, neg_neg]
  change (CHS.SchurContractionCore.contract W (fun p q =>
      matrixDZ (a p) (b p) (matrixDZ (a q) (-b q) C) x)) i j = _
  simp only [hinner, matrixDZ_map_star, neg_neg,
    complexHessian_inverse_transpose hu2 a b]
  simp only [matrix_map_star_mul] at h
  exact h

/-- Cancellation between the derivative of the inverse and the derivative of
the differentiated field. The conjugate pure Hessian provides the application
in (2.4). -/
theorem inverseDerivativeField_contraction_zero_of_product_nonsingular (a b : ι → E)
    (W : Matrix ι ι ℂ) {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : MatrixDifferentiableAt H x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (H x).det ≠ 0)
    (hProduct : CHS.SchurContractionCore.contract W (fun p q =>
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x) =
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x)) :
    CHS.SchurContractionCore.contract W (fun p q =>
      matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x) = 0 := by
  have hK := field_inverse_differentiableAt_of_det_ne_zero hH hdet
  have hExpansion (p q : ι) :
      matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x =
        (H x)⁻¹ *
          (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x -
            matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) := by
    unfold inverseDerivativeField
    rw [matrixDZ_product (a q) (-b q) hK (matrixDZ_differentiableAt hC (a p) (b p)),
      matrixDZ_inverse_of_det_ne_zero (a q) (-b q) hH hdet]
    noncomm_ring
  simp only [hExpansion, CHS.SchurContractionCore.contract_mul_left,
    CHS.SchurContractionCore.contract_sub, hProduct, sub_self, mul_zero]

theorem inverse_conjugate_hessian_divergence_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) (G : E → Matrix ι ι ℂ)
    (hG : G = complexHessian a b u ∨ G = pureHessian a b u) :
    let A := complexHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (G y).map star
    CHS.SchurContractionCore.contract (A x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x) = 0 := by
  let A := complexHessian a b u
  let H := fun y => (A y).map star
  let C := fun y => (G y).map star
  let W := (A x)⁻¹
  have hux := hu.contDiffAt (hU.mem_nhds hx)
  have hC (i j : ι) : ContDiffAt ℝ 2 (fun y => C y i j) x := by
    rcases hG with rfl | rfl
    · exact Complex.conjCLE.contDiff.contDiffAt.comp x
        (complexHessian_contDiffAt_two hux a b i j)
    · exact Complex.conjCLE.contDiff.contDiffAt.comp x
        (pureHessian_contDiffAt_two hux a b i j)
  have hH : MatrixDifferentiableAt H x :=
    fun i j => (Complex.conjCLE.contDiff.contDiffAt.comp x
      (complexHessian_contDiffAt_two hux a b i j)).differentiableAt (by norm_num)
  have hHerm (y : E) (hy : y ∈ U) : (A y).IsHermitian :=
    complexHessian_isHermitian ((hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)) a b
  have hTranspose (y : E) (hy : y ∈ U) : H y = (A y).transpose := by
    ext i j
    exact (hHerm y hy).apply j i
  have hDet : (H x).det ≠ 0 := by
    rw [hTranspose x hx, Matrix.det_transpose, hdet x hx]
    exact hρ
  have hInv : (H x)⁻¹ = W.transpose := by
    rw [hTranspose x hx, Matrix.transpose_nonsing_inv]
  change CHS.SchurContractionCore.contract W (fun p q =>
    matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x) = 0
  apply inverseDerivativeField_contraction_zero_of_product_nonsingular a b W hH hC hDet
  rw [hInv]
  have h := linearized_conjugate_first_product_const hU hu a b hρ hdet hx G hG
  change CHS.SchurContractionCore.contract W (fun p q =>
    matrixDZ (a p) (b p) (matrixDZ (a q) (-b q) C) x) = _ at h
  have hComm (p q : ι) :
      matrixDZ (a p) (b p) (matrixDZ (a q) (-b q) C) x =
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x :=
    matrixDZ_mixed_comm_at _ _ _ _ hC
  simpa only [hComm] using h

/-- Equation (2.4), the pure-Hessian instance of inverse derivative cancellation. -/
theorem inverse_conjugate_pure_divergence_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) :
    let A := complexHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (pureHessian a b u y).map star
    CHS.SchurContractionCore.contract (A x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x) = 0 :=
  inverse_conjugate_hessian_divergence_const hU hu a b hρ hdet hx _ (Or.inr rfl)

/-- Lemma 2.1: both product expressions for the mixed and pure Hessians,
and the vanishing contraction for the conjugate pure Hessian. -/
theorem matrix_differential_identities_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (B y).map star
    let W := (A x)⁻¹
    let L := fun G : E → Matrix ι ι ℂ =>
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) G) x)
    let first := fun G : E → Matrix ι ι ℂ =>
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a p) (b p) A x * W * matrixDZ (a q) (-b q) G x)
    let second := fun G : E → Matrix ι ι ℂ =>
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) G x)
    L A = first A ∧ L A = second C ∧ L B = first B ∧ L B = second H ∧
      CHS.SchurContractionCore.contract W (fun p q =>
        matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x) = 0 := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let H := fun y => (A y).map star
  let C := fun y => (B y).map star
  have hT (y : E) (hy : y ∈ U) : H y = (A y).transpose := by
    have h2 : ContDiffAt ℝ 2 u y :=
      (hu.contDiffAt (hU.mem_nhds hy)).of_le (by norm_num)
    ext i j
    exact (complexHessian_isHermitian h2 a b).apply j i
  have hH : H =ᶠ[𝓝 x] fun y => (A y).transpose :=
    Filter.Eventually.mono (hU.mem_nhds hx) hT
  have hInv : (H x)⁻¹ = ((A x)⁻¹).transpose := by
    rw [hT x hx, Matrix.transpose_nonsing_inv]
  have hC : C = pureHessian a (fun i => -b i) u := by
    funext y
    exact pureHessian_conjugate a b u y
  have hFirst := linearized_hessians_first_products_const hU hu a b hρ hdet hx
  obtain ⟨hSecondA, hSecondB⟩ := linearized_hessians_conjugate_products_const hU hu a b hρ hdet hx
  refine ⟨hFirst A (Or.inl rfl), ?_, hFirst B (Or.inr rfl), ?_,
    inverse_conjugate_pure_divergence_const hU hu a b hρ hdet hx⟩
  · change _ = CHS.SchurContractionCore.contract (A x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) C x)
    rw [hC, hInv]
    exact hSecondA
  · change _ = CHS.SchurContractionCore.contract (A x)⁻¹ (fun p q =>
      matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x)
    rw [hInv]
    simpa only [matrixDZ_congr_nhds _ _ hH] using hSecondB



end PowerConvexity
