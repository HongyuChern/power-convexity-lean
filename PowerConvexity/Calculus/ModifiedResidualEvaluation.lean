import PowerConvexity.Calculus.ConjugateDensityProduct

/-! # Exact evaluations of all four residuals in `upqmpq`

The formulas contain only the original third derivatives, modified second
Hessians and gradients. The original fourth derivatives have been eliminated
by the constant-density equation. The compact matrix products preserve the
index and conjugation positions of the expanded expressions in §2.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ContDiff Topology

namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def residualEvaluation (W R T : Matrix ι ι ℂ)
    (X Y P Q : ι → Matrix ι ι ℂ) (S : ι → ι → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  contract W (fun p q => X q * (R-T) * Y p + S p q -
    P q * T * Y p - X q * T * Q p - P q * T * Q p)

/-- The four residual evaluations, in the order of `upqmpq`. In particular,
`R-T` is the difference of the ORIGINAL and MODIFIED conjugate inverses.
No normalized frame or eigenvalue approximation is assumed. -/
theorem modified_four_residuals_const {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    {x : E} (hx : x ∈ U) (hneg : u x < 0) :
    let A := complexHessian a b u
    let B := pureHessian a b u
    let H := fun y => (A y).map star
    let C := fun y => (B y).map star
    let Am := modifiedA a b u
    let Bm := modifiedB a b u
    let Hm := fun y => (Am y).map star
    let Cm := fun y => (Bm y).map star
    let W := (A x)⁻¹
    let R := (H x)⁻¹
    let T := (Hm x)⁻¹
    let h := (powerWeight (u x) : ℂ)
    let g := complexGradient a b u x
    let XB := fun q => matrixDZ (a q) (-b q) B x
    let XH := fun q => matrixDZ (a q) (-b q) H x
    let YC := fun p => matrixDZ (a p) (b p) C x
    let YH := fun p => matrixDZ (a p) (b p) H x
    let PB := modificationBbar h g (Am x)
    let PH := fun q => (modificationAz h g (Am x) (Bm x) q).map star
    let QC := fun p => (PB p).map star
    let QH := fun p => (modificationAbar h g (Am x) (Bm x) p).map star
    let SA := modificationASecond h g (Am x) (Bm x)
    let SB := modificationBSecond h g (Am x) (Bm x)
    let SH := fun p q => (SA q p).map star
    let SC := fun p q => (SB q p).map star
    (matrixL a b u Am x - contract W (fun p q =>
      matrixDZ (a q) (-b q) Bm x * T * matrixDZ (a p) (b p) Cm x) =
        residualEvaluation W R T XB YC PB QC SA) ∧
    (matrixL a b u Hm x - contract W (fun p q =>
      matrixDZ (a q) (-b q) Hm x * T * matrixDZ (a p) (b p) Hm x) =
        residualEvaluation W R T XH YH PH QH SH) ∧
    (matrixL a b u Bm x - contract W (fun p q =>
      matrixDZ (a q) (-b q) Bm x * T * matrixDZ (a p) (b p) Hm x) =
        residualEvaluation W R T XB YH PB QH SB) ∧
    (matrixL a b u Cm x - contract W (fun p q =>
      matrixDZ (a q) (-b q) Hm x * T * matrixDZ (a p) (b p) Cm x) =
        residualEvaluation W R T XH YC PH QC SC) := by
  let A := complexHessian a b u
  let B := pureHessian a b u
  let H := fun y => (A y).map star
  let C := fun y => (B y).map star
  let Am := modifiedA a b u
  let Bm := modifiedB a b u
  let Hm := fun y => (Am y).map star
  let Cm := fun y => (Bm y).map star
  let W := (A x)⁻¹
  let R := (H x)⁻¹
  let T := (Hm x)⁻¹
  let h := (powerWeight (u x) : ℂ)
  let g := complexGradient a b u x
  let XB := fun q => matrixDZ (a q) (-b q) B x
  let XH := fun q => matrixDZ (a q) (-b q) H x
  let YC := fun p => matrixDZ (a p) (b p) C x
  let YH := fun p => matrixDZ (a p) (b p) H x
  let PB := modificationBbar h g (Am x)
  let PH := fun q => (modificationAz h g (Am x) (Bm x) q).map star
  let QC := fun p => (PB p).map star
  let QH := fun p => (modificationAbar h g (Am x) (Bm x) p).map star
  let SA := modificationASecond h g (Am x) (Bm x)
  let SB := modificationBSecond h g (Am x) (Bm x)
  let SH := fun p q => (SA q p).map star
  let SC := fun p q => (SB q p).map star
  have hu4 := hu.contDiffAt (hU.mem_nhds hx)
  have hu3 : ContDiffAt ℝ 3 u x := hu4.of_le (by norm_num)
  have hdetn : (fun y => (A y).det) =ᶠ[𝓝 x] fun _ => ρ :=
    Filter.Eventually.mono (hU.mem_nhds hx) hdet
  have hXB (q : ι) : matrixDZ (a q) (-b q) Bm x = XB q + PB q :=
    matrixDZbar_modifiedB_correction hu3 hneg a b q
  have hXH (q : ι) : matrixDZ (a q) (-b q) Hm x = XH q + PH q := by
    dsimp only [Hm, H, XH, PH, Am, A]
    simp only [matrixDZ_map_star, neg_neg, matrixDZ_modifiedA_correction hu3 hneg,
      matrix_map_star_add]
    rfl
  have hYC (p : ι) : matrixDZ (a p) (b p) Cm x = YC p + QC p := by
    dsimp only [Cm, C, YC, QC, Bm, B, PB]
    simp only [matrixDZ_map_star, matrixDZbar_modifiedB_correction hu3 hneg,
      matrix_map_star_add]
    rfl
  have hYH (p : ι) : matrixDZ (a p) (b p) Hm x = YH p + QH p := by
    dsimp only [Hm, H, YH, QH, Am, A]
    simp only [matrixDZ_map_star, matrixDZbar_modifiedA_correction hu3 hneg,
      matrix_map_star_add]
    rfl
  have hd := matrix_differential_identities_const hU hu a b hρ hdet hx
  have hbaseA : matrixL a b u A x = contract W (fun p q => XB q * R * YC p) := hd.2.1
  have hbaseB : matrixL a b u B x = contract W (fun p q => XB q * R * YH p) := hd.2.2.2.1
  have hbaseH : matrixL a b u H x = contract W (fun p q => XH q * R * YH p) :=
    conjugate_density_product_const hU hu a b hρ hdet hx A (Or.inl rfl)
  have hbaseC : matrixL a b u C x = contract W (fun p q => XH q * R * YC p) :=
    conjugate_density_product_const hU hu a b hρ hdet hx B (Or.inr rfl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hr := contracted_modified_residual W R T XB YC PB QC SA _ _ hbaseA
        (modifiedA_contracted_second hu4 hneg a b hdetn)
    simp_rw [← hXB, ← hYC] at hr
    exact hr
  · have hr := contracted_modified_residual W R T XH YH PH QH SH _ _ hbaseH
        (modifiedA_conjugate_contracted_second hu4 hneg a b hdetn)
    simp_rw [← hXH, ← hYH] at hr
    exact hr
  · have hr := contracted_modified_residual W R T XB YH PB QH SB _ _ hbaseB
        (modifiedB_contracted_second hu4 hneg a b hdetn)
    simp_rw [← hXB, ← hYH] at hr
    exact hr
  · have hr := contracted_modified_residual W R T XH YC PH QC SC _ _ hbaseC
        (modifiedB_conjugate_contracted_second hu4 hneg a b hdetn)
    simp_rw [← hXH, ← hYC] at hr
    exact hr

end PowerConvexity
