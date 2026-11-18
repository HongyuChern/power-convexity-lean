import PowerConvexity.Calculus.ModifiedSchurEvaluated
import PowerConvexity.Calculus.ThirdDifferenceColumns
import PowerConvexity.Algebra.ResidualContactEntryGeneral
import PowerConvexity.Algebra.ReadingTableContactGeneral
import PowerConvexity.Calculus.ModifiedContactContractionTwo

/-! # ReadingTable assembled for the actual Schur contraction at b_0 = 1 -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators ContDiff Topology ComplexOrder
namespace PowerConvexity
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open CHS.Calculus CHS.SchurContractionCore
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem modifiedSchur_LM_contact_general {u : E → ℝ} {U : Set E}
    (hU : IsOpen U) (hu : ContDiffOn ℝ 4 u U) (a b : ι → E)
    {ρ : ℂ} (hρ : ρ ≠ 0)
    (hdet : ∀ y ∈ U, (complexHessian a b u y).det = ρ)
    (hneg : ∀ y ∈ U, u y < 0)
    (hpos : ∀ y ∈ U, (complexHessian a b u y).PosDef)
    {x : E} (hx : x ∈ U) (d : ι → ℝ) (k : ι)
    (hI : modifiedA a b u x = 1)
    (hD : modifiedB a b u x = Matrix.diagonal (fun i => (d i:ℂ))) (hd : d k = 1) :
    matrixL a b u (modifiedSchur a b u) x k k =
      typeIQuadratic (complexHessian a b u x)⁻¹ (skewThirdHessian a b u k x)+
      (Complex.normSq ((powerWeight (u x):ℂ)*
        (complexGradient a b u x k-star (complexGradient a b u x k))):ℂ)*
        ((complexHessian a b u x)⁻¹).trace-
      ∑ s,weightedSquare (complexHessian a b u x)⁻¹
        (fun p => modifiedCompensatedHessian a b u p x k s) := by
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
  have hu3 : ContDiffAt ℝ 3 u x := (hu.contDiffAt (hU.mem_nhds hx)).of_le (by norm_num)
  have htr : (∑ p,∑ q,G q p*W p q) = 0 :=
    skewThirdHessian_trace_zero hu3 a b (Filter.Eventually.mono (hU.mem_nhds hx) hdet) k
  have hr := residual_four_contact_entry_trace_zero k G W
    (skewThirdHessian_conjTranspose hu3 a b k) τ XB XH YC YH PB PH QC QH SA SH SB SC
    (fun q s => readingTable_third_row_difference hu3 a b k s q)
    (fun p t => readingTable_third_column_difference hu3 a b k t p)
    (fun q s => readingTable_contact_P_row_general h g d k hd q s)
    (fun p t => readingTable_contact_Q_column_general h g d k hd p t)
    (fun p q => readingTable_contact_S_entry_general h g d k hd p q) htr
  have hm := modifiedSchur_LM_const_evaluated hU hu a b hρ hdet hneg hpos hx
  dsimp only at hm
  rw [hI,hD,matrix_map_star_nonsing_inv] at hm
  have hstar1 : (1 : Matrix ι ι ℂ).map star = 1 := by
    ext i j; simp [Matrix.one_apply]
  have hstarD : (Matrix.diagonal (fun i => (d i:ℂ))).map star = Bd := by
    ext i j
    by_cases hij : i = j
    · subst j; simp [Bd,Matrix.diagonal_apply,Matrix.map_apply]
    · simp [Bd,Matrix.diagonal_apply,Matrix.map_apply,hij]
  rw [hstar1,inv_one,hstarD] at hm
  have hm0 := congrArg (fun M : Matrix ι ι ℂ => M k k) hm
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.mul_one,Matrix.one_mul,
    Bd,Matrix.diagonal_mul,Matrix.mul_diagonal,hd,Complex.ofReal_one,one_mul,mul_one] at hm0
  have hs : contract G (fun p q => modifiedCompensatedHessian a b u p x *
      (modifiedCompensatedHessian a b u q x).conjTranspose) k k =
      ∑ s,weightedSquare G (fun p => modifiedCompensatedHessian a b u p x k s) := by
    simp only [contract, weightedSquare, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.mul_sum, ← mul_assoc]
    calc
      _ = ∑ p, ∑ s, ∑ q, G q p * modifiedCompensatedHessian a b u p x k s *
          star (modifiedCompensatedHessian a b u q x k s) := by
        apply Finset.sum_congr rfl
        intro p _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  simp only [Matrix.sub_apply,Matrix.add_apply] at hr
  change matrixL a b u (modifiedSchur a b u) x k k = _
  dsimp only [G,W,τ,h,g] at hr hs
  rw [hm0,hs]
  linear_combination hr

end PowerConvexity
