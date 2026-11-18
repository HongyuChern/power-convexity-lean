import PowerConvexity.Calculus.ModifiedContactContractionGeneral
import PowerConvexity.Algebra.ReadingTableCombinationBoundsGeneral

/-! # Actual Schur contraction and its algebraic comparison at the contact value

The comparison keeps the original third derivatives fixed. Only the normalized
pure Hessian in ReadingTable and its outside coefficients are changed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open CHS.Calculus CHS.SchurContractionCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def actualReadingTableGeneral (a b : ι → E) (u : E → ℝ) (x : E)
    (d : ι → ℝ) : Fin 4 → Matrix ι ι ℂ :=
  readingTableResidualsGeneral (complexHessian a b u x)⁻¹ (powerWeight (u x):ℂ)
    (complexGradient a b u x) (Matrix.diagonal (fun i => (d i:ℂ)))
    (fun q => matrixDZ (a q) (-b q) (pureHessian a b u) x)
    (fun q => matrixDZ (a q) (-b q) (fun y => (complexHessian a b u y).map star) x)
    (fun p => matrixDZ (a p) (b p) (fun y => (pureHessian a b u y).map star) x)
    (fun p => matrixDZ (a p) (b p) (fun y => (complexHessian a b u y).map star) x)

theorem modifiedSchur_LM_normalized_general {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : ι → ℝ) (k : ι)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ))) :
    matrixL a b u (modifiedSchur a b u) x k k =
      readingTableCombinationTwo (d k) (fun l => actualReadingTableGeneral a b u x d l k k)-
      ∑ s,weightedSquare (complexHessian a b u x)⁻¹
        (fun p => modifiedCompensatedHessian a b u p x k s) := by
  have hm := modifiedSchur_LM_const_evaluated hU hu a b hρ hdet hneg hpos hx
  dsimp only at hm
  rw [hI,hD,matrix_map_star_nonsing_inv] at hm
  have hstar1 : (1 : Matrix ι ι ℂ).map star = 1 := by
    ext i j; simp [Matrix.one_apply]
  have hstarD : (Matrix.diagonal (fun i => (d i:ℂ))).map star =
      Matrix.diagonal (fun i => (d i:ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Matrix.diagonal_apply,Matrix.map_apply]
    · simp [Matrix.diagonal_apply,Matrix.map_apply,hij]
  rw [hstar1,inv_one,hstarD] at hm
  have hm0 := congrArg (fun M : Matrix ι ι ℂ => M k k) hm
  have hs : contract (complexHessian a b u x)⁻¹
      (fun p q => modifiedCompensatedHessian a b u p x *
        (modifiedCompensatedHessian a b u q x).conjTranspose) k k =
      ∑ s,weightedSquare (complexHessian a b u x)⁻¹
        (fun p => modifiedCompensatedHessian a b u p x k s) := by
    simp only [contract, weightedSquare, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, ← mul_assoc]
    calc
      _ = ∑ p, ∑ s, ∑ q, (complexHessian a b u x)⁻¹ q p *
          modifiedCompensatedHessian a b u p x k s *
          star (modifiedCompensatedHessian a b u q x k s) := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.mul_one,Matrix.one_mul,
    Matrix.diagonal_mul,Matrix.mul_diagonal] at hm0
  rw [hs] at hm0
  rw [hm0]
  simp [readingTableCombinationTwo,actualReadingTableGeneral,readingTableResidualsGeneral]
  ring

theorem actualReadingTableGeneral_contact_value {u : E → ℝ} {x : E} {ρ : ℂ}
    (hu : ContDiffAt ℝ 3 u x) (a b : ι → E)
    (hdet : (fun y => (complexHessian a b u y).det) =ᶠ[𝓝 x] fun _ => ρ)
    (d : ι → ℝ) (k : ι) (hd : d k = 1) :
    readingTableCombinationTwo 1 (fun l => actualReadingTableGeneral a b u x d l k k) =
      typeIQuadratic (complexHessian a b u x)⁻¹ (skewThirdHessian a b u k x)+
      (Complex.normSq ((powerWeight (u x):ℂ)*
        (complexGradient a b u x k-star (complexGradient a b u x k))):ℂ)*
        ((complexHessian a b u x)⁻¹).trace := by
  let G := (complexHessian a b u x)⁻¹
  let W := skewThirdHessian a b u k x
  let h := powerWeight (u x)
  let g := complexGradient a b u x
  let τ : ℂ := (h:ℂ)*(g k-star (g k))
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
  have hr := residual_four_contact_entry_trace_zero k G W
    (skewThirdHessian_conjTranspose hu a b k) τ XB XH YC YH PB PH QC QH SA SH SB SC
    (fun q s => readingTable_third_row_difference hu a b k s q)
    (fun p t => readingTable_third_column_difference hu a b k t p)
    (fun q s => readingTable_contact_P_row_general h g d k hd q s)
    (fun p t => readingTable_contact_Q_column_general h g d k hd p t)
    (fun p q => readingTable_contact_S_entry_general h g d k hd p q)
    (skewThirdHessian_trace_zero hu a b hdet k)
  simpa [readingTableCombinationTwo,actualReadingTableGeneral,readingTableResidualsGeneral,
    G,W,τ,h,g,Bd,XB,XH,YC,YH,PB,PH,QC,QH,SA,SB,SH,SC,Matrix.sub_apply,Matrix.add_apply] using hr

end PowerConvexity
