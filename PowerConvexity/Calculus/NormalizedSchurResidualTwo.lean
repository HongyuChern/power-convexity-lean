import PowerConvexity.Calculus.ModifiedContactContractionTwo
import PowerConvexity.Algebra.ReadingTableCombinationBoundsTwo

/-! # Actual Schur contraction and its algebraic comparison at the contact value

The comparison keeps the original third derivatives fixed. Only the normalized
pure Hessian in ReadingTable and its outside coefficients are changed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.SchurContractionCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def actualReadingTableTwo (a b : Fin 2 → E) (u : E → ℝ) (x : E)
    (d : Fin 2 → ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  readingTableResidualsTwo (complexHessian a b u x)⁻¹ (powerWeight (u x):ℂ)
    (complexGradient a b u x) (Matrix.diagonal (fun i => (d i:ℂ)))
    (fun q => matrixDZ (a q) (-b q) (pureHessian a b u) x)
    (fun q => matrixDZ (a q) (-b q) (fun y => (complexHessian a b u y).map star) x)
    (fun p => matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x)
    (fun p => matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x)

theorem modifiedSchur_LM_normalized_two {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : Fin 2 → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : Fin 2 → ℝ)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ))) :
    matrixL a b u (modifiedSchur a b u) x 0 0 =
      readingTableCombinationTwo (d 0) (fun k => actualReadingTableTwo a b u x d k 0 0)-
      ∑ s,weightedSquare (complexHessian a b u x)⁻¹
        (fun p => modifiedCompensatedHessian a b u p x 0 s) := by
  have hm := modifiedSchur_LM_const_evaluated hU hu a b hρ hdet hneg hpos hx
  dsimp only at hm
  rw [hI,hD,matrix_map_star_nonsing_inv] at hm
  have hstar1 : (1 : Matrix (Fin 2) (Fin 2) ℂ).map star = 1 := by
    ext i j; simp [Matrix.one_apply]
  have hstarD : (Matrix.diagonal (fun i => (d i:ℂ))).map star =
      Matrix.diagonal (fun i => (d i:ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal_apply,Matrix.map_apply]
    · simp [Matrix.diagonal_apply,Matrix.map_apply,hij]
  rw [hstar1,inv_one,hstarD] at hm
  have hm0 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) hm
  have hs : contract (complexHessian a b u x)⁻¹
      (fun p q => modifiedCompensatedHessian a b u p x *
        (modifiedCompensatedHessian a b u q x).conjTranspose) 0 0 =
      ∑ s,weightedSquare (complexHessian a b u x)⁻¹
        (fun p => modifiedCompensatedHessian a b u p x 0 s) := by
    simp [contract,weightedSquare,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two]
    ring
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.mul_one,Matrix.one_mul,
    Matrix.diagonal_mul,Matrix.mul_diagonal] at hm0
  rw [hs] at hm0
  rw [hm0]
  simp [readingTableCombinationTwo,actualReadingTableTwo,readingTableResidualsTwo]
  ring

theorem actualReadingTableTwo_contact_value {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : Fin 2 → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (d : Fin 2 → ℝ) (hd : d 0 = 1) :
    readingTableCombinationTwo 1 (fun k => actualReadingTableTwo a b u x d k 0 0) =
      typeIQuadraticTwo (complexHessian a b u x)⁻¹ (skewThirdHessian a b u 0 x)+
      (Complex.normSq ((powerWeight (u x):ℂ)*
        (complexGradient a b u x 0-star (complexGradient a b u x 0))):ℂ)*
        ((complexHessian a b u x)⁻¹).trace := by
  let G := (complexHessian a b u x)⁻¹
  let W := skewThirdHessian a b u 0 x
  let h := powerWeight (u x)
  let g := complexGradient a b u x
  let τ : ℂ := (h:ℂ)*(g 0-star (g 0))
  let Bd := Matrix.diagonal (fun i => (d i:ℂ))
  let XB := fun q => matrixDZ (a q) (-b q) (pureHessian a b u) x
  let XH := fun q => matrixDZ (a q) (-b q) (fun y => (complexHessian a b u y).map star) x
  let YC := fun p => matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x
  let YH := fun p => matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x
  let PB := modificationBbar (h:ℂ) g 1
  let PH := fun q => (modificationAz (h:ℂ) g 1 Bd q).map star
  let QC := fun p => (PB p).map star
  let QH := fun p => (modificationAbar (h:ℂ) g 1 Bd p).map star
  let SA := modificationASecond (h:ℂ) g 1 Bd
  let SB := modificationBSecond (h:ℂ) g 1 Bd
  let SH := fun p q => (SA q p).map star
  let SC := fun p q => (SB q p).map star
  have hr := residual_four_contact_entry_trace_zero_two G W
    (skewThirdHessian_conjTranspose hu a b 0) τ XB XH YC YH PB PH QC QH SA SH SB SC
    (fun q s => readingTable_third_row_difference hu a b 0 s q)
    (fun p t => readingTable_third_column_difference hu a b 0 t p)
    (fun q s => readingTable_contact_P_row h g d hd q s)
    (fun p t => readingTable_contact_Q_column h g d hd p t)
    (fun p q => readingTable_contact_S_entry h g d hd p q)
    (skewThirdHessian_trace_zero hu a b hdet 0)
  simpa [readingTableCombinationTwo,actualReadingTableTwo,readingTableResidualsTwo,
    G,W,τ,h,g,Bd,XB,XH,YC,YH,PB,PH,QC,QH,SA,SB,SH,SC,Matrix.sub_apply,Matrix.add_apply] using hr

end PowerConvexity
