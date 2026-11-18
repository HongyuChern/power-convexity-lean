import PowerConvexity.Calculus.ComplexFrameLinearRules
import PowerConvexity.Calculus.ChordDefectCalculus
import PowerConvexity.Calculus.PerturbationJets
import PowerConvexity.Algebra.InverseContactOrder

/-! # Actual complex Hessian contact and inverse order at a chord maximum -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped ContDiff ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem complexHessian_comp_linear {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (T : E →L[ℝ] F) {x : E} (hf : ContDiffAt ℝ 2 f (T x))
    (a b : ι → E) :
    complexHessian a b (fun y => f (T y)) x =
      complexHessian (fun i => T (a i)) (fun i => T (b i)) f (T x) := by
  simpa only [zero_add] using complexHessian_comp_affine T 0
    (by simpa only [zero_add] using hf) a b

theorem chordDefect_localMax_complex_contact
    {f : E → ℝ} {x y : E} (a b : ℝ) (e k : ι → E)
    (Q R : Matrix ι ι ℂ)
    (hx : ContDiffAt ℝ 2 f x) (hy : ContDiffAt ℝ 2 f y)
    (hz : ContDiffAt ℝ 2 f (a • x+b • y))
    (hm : IsLocalMax (chordDefect a b f) (x,y)) :
    ((a:ℂ) • (Q*complexHessian e k f x*Q.conjTranspose)+
      (b:ℂ) • (R*complexHessian e k f y*R.conjTranspose)-
      ((a:ℂ) • Q+(b:ℂ) • R)*complexHessian e k f (a • x+b • y)*
        ((a:ℂ) • Q+(b:ℂ) • R).conjTranspose).PosSemidef := by
  let ar : ι → E × E := fun i => (complexFrameReal Q e k i,complexFrameReal R e k i)
  let br : ι → E × E := fun i => (complexFrameImag Q e k i,complexFrameImag R e k i)
  let S := (a:ℂ) • Q+(b:ℂ) • R
  have hC : ContDiffAt ℝ 2 (fun z : E × E => f (chordLinearMap a b z)) (x,y) :=
    hz.comp (x,y) (chordLinearMap (E := E) a b).contDiff.contDiffAt
  have hX : ContDiffAt ℝ 2 (fun z : E × E => f z.1) (x,y) :=
    hx.comp (x,y) (ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt
  have hY : ContDiffAt ℝ 2 (fun z : E × E => f z.2) (x,y) :=
    hy.comp (x,y) (ContinuousLinearMap.snd ℝ E E).contDiff.contDiffAt
  have hAX : ContDiffAt ℝ 2 (fun z : E × E => a*f z.1) (x,y) := contDiffAt_const.mul hX
  have hBY : ContDiffAt ℝ 2 (fun z : E × E => b*f z.2) (x,y) := contDiffAt_const.mul hY
  have hm' : IsLocalMax (fun z : E × E => f (chordLinearMap a b z)-(a*f z.1+b*f z.2)) (x,y) := by
    convert hm using 1
    funext z
    change f (a • z.1+b • z.2)-(a*f z.1+b*f z.2) = f (a • z.1+b • z.2)-a*f z.1-b*f z.2
    ring
  have hc := complexHessian_sub_posSemidef_of_isLocalMax hC (hAX.add hBY) hm' ar br
  have hTreal : (fun i => chordLinearMap a b (ar i)) = complexFrameReal S e k := by
    funext i
    simp only [S,complexFrameReal_add,complexFrameReal_real_smul]
    rfl
  have hTimag : (fun i => chordLinearMap a b (br i)) = complexFrameImag S e k := by
    funext i
    simp only [S,complexFrameImag_add,complexFrameImag_real_smul]
    rfl
  have hCH : complexHessian ar br (fun z : E × E => f (chordLinearMap a b z)) (x,y) =
      S*complexHessian e k f (a • x+b • y)*S.conjTranspose := by
    rw [complexHessian_comp_linear (chordLinearMap a b) hz ar br,hTreal,hTimag]
    exact complexHessian_complexFrame hz S e k
  have hXH : complexHessian ar br (fun z : E × E => f z.1) (x,y) =
      Q*complexHessian e k f x*Q.conjTranspose := by
    change complexHessian ar br (fun z => f ((ContinuousLinearMap.fst ℝ E E) z)) (x,y) = _
    rw [complexHessian_comp_linear (ContinuousLinearMap.fst ℝ E E) hx ar br]
    exact complexHessian_complexFrame hx Q e k
  have hYH : complexHessian ar br (fun z : E × E => f z.2) (x,y) =
      R*complexHessian e k f y*R.conjTranspose := by
    change complexHessian ar br (fun z => f ((ContinuousLinearMap.snd ℝ E E) z)) (x,y) = _
    rw [complexHessian_comp_linear (ContinuousLinearMap.snd ℝ E E) hy ar br]
    exact complexHessian_complexFrame hy R e k
  rw [complexHessian_add_at hAX hBY,complexHessian_const_mul_at hX a,
    complexHessian_const_mul_at hY b,hXH,hYH,hCH] at hc
  exact hc

theorem chordDefect_localMax_inverse_complex_order
    {f : E → ℝ} {x y : E} (a b : ℝ) (e k : ι → E)
    (hx : ContDiffAt ℝ 2 f x) (hy : ContDiffAt ℝ 2 f y)
    (hz : ContDiffAt ℝ 2 f (a • x+b • y))
    (hpx : (complexHessian e k f x).PosDef)
    (hpy : (complexHessian e k f y).PosDef)
    (hpz : (complexHessian e k f (a • x+b • y)).PosDef)
    (hm : IsLocalMax (chordDefect a b f) (x,y)) :
    ((complexHessian e k f (a • x+b • y))⁻¹-
      ((a:ℂ) • (complexHessian e k f x)⁻¹+(b:ℂ) • (complexHessian e k f y)⁻¹)).PosSemidef := by
  let X := (complexHessian e k f x)⁻¹
  let Y := (complexHessian e k f y)⁻¹
  let S := (a:ℂ) • X+(b:ℂ) • Y
  have hS : S.IsHermitian :=
    (hpx.inv.isHermitian.smul (by simp [IsSelfAdjoint])).add
      (hpy.inv.isHermitian.smul (by simp [IsSelfAdjoint]))
  have hX : X*complexHessian e k f x*X.conjTranspose = X := by
    rw [hpx.inv.isHermitian.eq,Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp hpx.isUnit),Matrix.one_mul]
  have hY : Y*complexHessian e k f y*Y.conjTranspose = Y := by
    rw [hpy.inv.isHermitian.eq,Matrix.nonsing_inv_mul _
      ((Matrix.isUnit_iff_isUnit_det _).mp hpy.isUnit),Matrix.one_mul]
  have hc := chordDefect_localMax_complex_contact a b e k X Y hx hy hz hm
  rw [hX,hY] at hc
  change (S-S*complexHessian e k f (a • x+b • y)*S.conjTranspose).PosSemidef at hc
  rw [hS.eq] at hc
  exact inverse_sub_posSemidef_of_contact hpz hS hc

end PowerConvexity
