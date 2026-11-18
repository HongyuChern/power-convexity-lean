import PowerConvexity.Calculus.MatrixInverse

/-!
# Schur calculus without a constant determinant assumption

The CHS product-rule proof is reused at the locked source revision, replacing
its determinant-one inverse interface by the proved nonsingular-locus interface.
This supplies actual derivatives for the modified matrices of frozen §2.2.
-/

set_option autoImplicit false
open scoped BigOperators ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma schurField_contDiffAt_two_nonsingular {A B C H : E → Matrix ι ι ℂ} {x : E}
    (hA : ∀ i j, ContDiffAt ℝ 2 (fun y => A y i j) x)
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun y => B y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hdet : (H x).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => schurField A B C H y i j) x := by
  have hK := field_inverse_contDiffAt_of_det_ne_zero hH hdet
  exact (hA i j).sub (matrix_product_contDiffAt (matrix_product_contDiffAt hB hK) hC i j)

lemma returnField_contDiffAt_two_nonsingular {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (H x).det ≠ 0) (i j : ι) :
    ContDiffAt ℝ 2 (fun y => returnField H C y i j) x := by
  exact matrix_product_contDiffAt (field_inverse_contDiffAt_of_det_ne_zero hH hdet) hC i j

lemma inverseDerivativeField_contDiffAt_one_nonsingular (a b : ι → E)
    {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (H x).det ≠ 0) (p i j : ι) :
    ContDiffAt ℝ 1 (fun y => inverseDerivativeField a b H C p y i j) x := by
  exact matrix_product_contDiffAt
    (fun r s => (field_inverse_contDiffAt_of_det_ne_zero hH hdet r s).of_le (by norm_num))
    (fun r s => dz_contDiffAt_one (hC r s) (a p) (b p)) i j

lemma compensatedField_contDiffAt_one_nonsingular (a b : ι → E)
    {B H : E → Matrix ι ι ℂ} {x : E}
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun y => B y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hdet : (H x).det ≠ 0) (p i j : ι) :
    ContDiffAt ℝ 1 (fun y => compensatedField a b B H p y i j) x := by
  exact (dz_contDiffAt_one (hB i j) (a p) (b p)).sub
    (matrix_product_contDiffAt
      (matrix_product_contDiffAt
        (fun r s => (hB r s).of_le (by norm_num))
        (fun r s => (field_inverse_contDiffAt_of_det_ne_zero hH hdet r s).of_le (by norm_num)))
      (fun r s => dz_contDiffAt_one (hH r s) (a p) (b p)) i j)

/-- Equation (2.12), for actual matrix fields at a differentiability point. -/
lemma matrixDZ_schurField_nonsingular (a b : ι → E) (p : ι)
    {A B C H : E → Matrix ι ι ℂ} {x : E}
    (hA : MatrixDifferentiableAt A x) (hB : MatrixDifferentiableAt B x)
    (hC : MatrixDifferentiableAt C x) (hH : MatrixDifferentiableAt H x)
    (hdet : (H x).det ≠ 0) :
    matrixDZ (a p) (b p) (schurField A B C H) x =
      matrixDZ (a p) (b p) A x -
        compensatedField a b B H p x * returnField H C x -
        B x * inverseDerivativeField a b H C p x := by
  have hK := field_inverse_differentiableAt_of_det_ne_zero hH hdet
  have hBK := matrix_product_differentiable hB hK
  change matrixDZ (a p) (b p) (fun y => A y - (B y * (H y)⁻¹) * C y) x = _
  rw [matrixDZ_sub (a p) (b p) hA (matrix_product_differentiable hBK hC),
    matrixDZ_product (a p) (b p) hBK hC,
    matrixDZ_product (a p) (b p) hB hK]
  have h := schur_first_derivative_algebra
    (matrixDZ (a p) (b p) A x) (B x) (C x) (H x)⁻¹
    (matrixDZ (a p) (b p) B x) (matrixDZ (a p) (b p) C x)
    (matrixDZ (a p) (b p) H x) (matrixDZ (a p) (b p) (fun y => (H y)⁻¹) x)
    (matrixDZ_inverse_of_det_ne_zero (a p) (b p) hH hdet)
  simpa only [compensatedField, returnField, inverseDerivativeField, mul_assoc] using h

/-- Product-rule expansion before any PDE cancellation. The first-derivative
identity is established on a neighbourhood before it is differentiated. -/
lemma schurField_mixed_expansion_nonsingular (a b : ι → E)
    {A B C H : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ 2 (fun y => A y i j) U)
    (hB : ∀ i j, ContDiffOn ℝ 2 (fun y => B y i j) U)
    (hC : ∀ i j, ContDiffOn ℝ 2 (fun y => C y i j) U)
    (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U)
    (hdet : ∀ y ∈ U, (H y).det ≠ 0) {x : E} (hx : x ∈ U) (p q : ι) :
    matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurField A B C H)) x =
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x -
      matrixDZ (a q) (-b q) (compensatedField a b B H p) x * returnField H C x -
      compensatedField a b B H p x * matrixDZ (a q) (-b q) (returnField H C) x -
      matrixDZ (a q) (-b q) B x * inverseDerivativeField a b H C p x -
      B x * matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x := by
  have hAx i j := (hA i j).contDiffAt (hU.mem_nhds hx)
  have hBx i j := (hB i j).contDiffAt (hU.mem_nhds hx)
  have hCx i j := (hC i j).contDiffAt (hU.mem_nhds hx)
  have hHx i j := (hH i j).contDiffAt (hU.mem_nhds hx)
  have hdetx : (H x).det ≠ 0 := hdet x hx
  have hDA := matrixDZ_differentiableAt hAx (a p) (b p)
  have hBd : MatrixDifferentiableAt B x :=
    fun i j => (hBx i j).differentiableAt (by norm_num)
  have hEd : MatrixDifferentiableAt (compensatedField a b B H p) x :=
    fun i j => (compensatedField_contDiffAt_one_nonsingular a b hBx hHx hdetx p i j).differentiableAt (by norm_num)
  have hRd : MatrixDifferentiableAt (returnField H C) x :=
    fun i j => (returnField_contDiffAt_two_nonsingular hHx hCx hdetx i j).differentiableAt (by norm_num)
  have hTd : MatrixDifferentiableAt (inverseDerivativeField a b H C p) x :=
    fun i j => (inverseDerivativeField_contDiffAt_one_nonsingular a b hHx hCx hdetx p i j).differentiableAt (by norm_num)
  have hfirst : matrixDZ (a p) (b p) (schurField A B C H) =ᶠ[𝓝 x]
      (fun y => matrixDZ (a p) (b p) A y -
        compensatedField a b B H p y * returnField H C y -
        B y * inverseDerivativeField a b H C p y) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact matrixDZ_schurField_nonsingular a b p
      (fun i j => ((hA i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (fun i j => ((hB i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (fun i j => ((hC i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (fun i j => ((hH i j).contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
      (hdet y hy)
  rw [matrixDZ_congr_nhds (a q) (-b q) hfirst]
  rw [matrixDZ_sub (a q) (-b q)
      (matrix_sub_differentiable hDA (matrix_product_differentiable hEd hRd))
      (matrix_product_differentiable hBd hTd),
    matrixDZ_sub (a q) (-b q) hDA (matrix_product_differentiable hEd hRd),
    matrixDZ_product (a q) (-b q) hEd hRd,
    matrixDZ_product (a q) (-b q) hBd hTd]
  abel


theorem matrixDZ_inverse_return_nonsingular (a b : ι → E)
    {B C H : E → Matrix ι ι ℂ} {x : E} {q : ι}
    (hC : MatrixDifferentiableAt C x) (hH : MatrixDifferentiableAt H x)
    (hdet : (H x).det ≠ 0)
    (hCstar : C =ᶠ[𝓝 x] (fun y => (B y).conjTranspose))
    (hHstar : H =ᶠ[𝓝 x] (fun y => (H y).conjTranspose)) :
    matrixDZ (a q) (-b q) (returnField H C) x =
      (H x)⁻¹ * (compensatedField a b B H q x).conjTranspose := by
  have hK := field_inverse_differentiableAt_of_det_ne_zero hH hdet
  have hCD : matrixDZ (a q) (-b q) C x =
      (matrixDZ (a q) (b q) B x).conjTranspose :=
    (matrixDZ_congr_nhds (a q) (-b q) hCstar).trans (matrixDZ_conjTranspose (a q) (b q) B x)
  have hHD : matrixDZ (a q) (-b q) H x =
      (matrixDZ (a q) (b q) H x).conjTranspose :=
    (matrixDZ_congr_nhds (a q) (-b q) hHstar).trans (matrixDZ_conjTranspose (a q) (b q) H x)
  have hHx : (H x).conjTranspose = H x := hHstar.self_of_nhds.symm
  have hKstar : ((H x)⁻¹).conjTranspose = (H x)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hHx]
  change matrixDZ (a q) (-b q) (fun y => (H y)⁻¹ * C y) x = _
  rw [matrixDZ_product (a q) (-b q) hK hC,
    matrixDZ_inverse_of_det_ne_zero (a q) (-b q) hH hdet,
    hCD, hHD, hCstar.self_of_nhds]
  simp only [compensatedField, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_mul, hKstar]
  noncomm_ring


/-- TeX `qpB`, with the actual derivative and a nonsingular inverse. -/
theorem inverseDerivativeField_dzbar (a b : ι → E)
    {H C : E → Matrix ι ι ℂ} {x : E}
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hC : ∀ i j, ContDiffAt ℝ 2 (fun y => C y i j) x)
    (hdet : (H x).det ≠ 0) (p q : ι) :
    matrixDZ (a q) (-b q) (inverseDerivativeField a b H C p) x =
      (H x)⁻¹ * (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x -
        matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) := by
  have hHd : MatrixDifferentiableAt H x :=
    fun i j => (hH i j).differentiableAt (by norm_num)
  have hK := field_inverse_differentiableAt_of_det_ne_zero hHd hdet
  change matrixDZ (a q) (-b q) (fun y => (H y)⁻¹ * matrixDZ (a p) (b p) C y) x = _
  rw [matrixDZ_product (a q) (-b q) hK (matrixDZ_differentiableAt hC (a p) (b p)),
    matrixDZ_inverse_of_det_ne_zero (a q) (-b q) hHd hdet]
  noncomm_ring

/-- Corrected TeX `qsBp`: the first product ends with `∂p H`, not `∂p H⁻¹`. -/
theorem compensatedField_dzbar (a b : ι → E)
    {B H : E → Matrix ι ι ℂ} {x : E}
    (hB : ∀ i j, ContDiffAt ℝ 2 (fun y => B y i j) x)
    (hH : ∀ i j, ContDiffAt ℝ 2 (fun y => H y i j) x)
    (hdet : (H x).det ≠ 0) (p q : ι) :
    matrixDZ (a q) (-b q) (compensatedField a b B H p) x =
      (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x -
        matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) -
      B x * (H x)⁻¹ *
        (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) H) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) := by
  have hBd : MatrixDifferentiableAt B x :=
    fun i j => (hB i j).differentiableAt (by norm_num)
  have hHd : MatrixDifferentiableAt H x :=
    fun i j => (hH i j).differentiableAt (by norm_num)
  have hK := field_inverse_differentiableAt_of_det_ne_zero hHd hdet
  have hDpH := matrixDZ_differentiableAt hH (a p) (b p)
  change matrixDZ (a q) (-b q)
    (fun y => matrixDZ (a p) (b p) B y - B y * (H y)⁻¹ * matrixDZ (a p) (b p) H y) x = _
  rw [matrixDZ_sub (a q) (-b q) (matrixDZ_differentiableAt hB (a p) (b p))
      (matrix_product_differentiable (matrix_product_differentiable hBd hK) hDpH),
    matrixDZ_product (a q) (-b q) (matrix_product_differentiable hBd hK) hDpH,
    matrixDZ_product (a q) (-b q) hBd hK,
    matrixDZ_inverse_of_det_ne_zero (a q) (-b q) hHd hdet]
  noncomm_ring

/-- The five-term Schur residual identity before contraction, using actual
second derivatives. No CMA equation or cancellation is assumed. -/
theorem schurField_mixed_residual (a b : ι → E)
    {A B C H : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ 2 (fun y => A y i j) U)
    (hB : ∀ i j, ContDiffOn ℝ 2 (fun y => B y i j) U)
    (hC : ∀ i j, ContDiffOn ℝ 2 (fun y => C y i j) U)
    (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U)
    (hdet : ∀ y ∈ U, (H y).det ≠ 0) {x : E} (hx : x ∈ U)
    (hCstar : C =ᶠ[𝓝 x] (fun y => (B y).conjTranspose))
    (hHstar : H =ᶠ[𝓝 x] (fun y => (H y).conjTranspose)) (p q : ι) :
    matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurField A B C H)) x =
      (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x -
        matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) +
      B x * (H x)⁻¹ *
        (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) H) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
        (H x)⁻¹ * C x -
      (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x -
        matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
        (H x)⁻¹ * C x -
      B x * (H x)⁻¹ *
        (matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) -
      compensatedField a b B H p x * (H x)⁻¹ *
        (compensatedField a b B H q x).conjTranspose := by
  have hBx i j := (hB i j).contDiffAt (hU.mem_nhds hx)
  have hCx i j := (hC i j).contDiffAt (hU.mem_nhds hx)
  have hHx i j := (hH i j).contDiffAt (hU.mem_nhds hx)
  rw [schurField_mixed_expansion_nonsingular a b hU hA hB hC hH hdet hx,
    compensatedField_dzbar a b hBx hHx (hdet x hx),
    inverseDerivativeField_dzbar a b hHx hCx (hdet x hx),
    matrixDZ_inverse_return_nonsingular a b
      (fun i j => (hCx i j).differentiableAt (by norm_num))
      (fun i j => (hHx i j).differentiableAt (by norm_num))
      (hdet x hx) hCstar hHstar]
  dsimp only [returnField, inverseDerivativeField]
  noncomm_ring

theorem contract_add (W : Matrix ι ι ℂ) (F G : ι → ι → Matrix ι ι ℂ) :
    contract W (fun p q => F p q + G p q) = contract W F + contract W G := by
  simp only [contract, smul_add, Finset.sum_add_distrib]

/-- Frozen TeX `upqmpq` for actual C2 matrix fields, before substituting the
modified Hessians. The coefficient order is `W q p`. -/
theorem schurField_contracted_residual (a b : ι → E) (W : Matrix ι ι ℂ)
    {A B C H : E → Matrix ι ι ℂ} {U : Set E} (hU : IsOpen U)
    (hA : ∀ i j, ContDiffOn ℝ 2 (fun y => A y i j) U)
    (hB : ∀ i j, ContDiffOn ℝ 2 (fun y => B y i j) U)
    (hC : ∀ i j, ContDiffOn ℝ 2 (fun y => C y i j) U)
    (hH : ∀ i j, ContDiffOn ℝ 2 (fun y => H y i j) U)
    (hdet : ∀ y ∈ U, (H y).det ≠ 0) {x : E} (hx : x ∈ U)
    (hCstar : C =ᶠ[𝓝 x] (fun y => (B y).conjTranspose))
    (hHstar : H =ᶠ[𝓝 x] (fun y => (H y).conjTranspose)) :
    contract W (fun p q =>
      matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) (schurField A B C H)) x) =
      contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) A) x -
          matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) +
      B x * (H x)⁻¹ * contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) H) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
        (H x)⁻¹ * C x -
      contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) B) x -
          matrixDZ (a q) (-b q) B x * (H x)⁻¹ * matrixDZ (a p) (b p) H x) *
        (H x)⁻¹ * C x -
      B x * (H x)⁻¹ * contract W (fun p q =>
        matrixDZ (a q) (-b q) (matrixDZ (a p) (b p) C) x -
          matrixDZ (a q) (-b q) H x * (H x)⁻¹ * matrixDZ (a p) (b p) C x) -
      contract W (fun p q => compensatedField a b B H p x * (H x)⁻¹ *
        (compensatedField a b B H q x).conjTranspose) := by
  simp_rw [schurField_mixed_residual a b hU hA hB hC hH hdet hx hCstar hHstar]
  simp only [contract_sub, contract_add, contract_mul_left, contract_mul_right]

end PowerConvexity
