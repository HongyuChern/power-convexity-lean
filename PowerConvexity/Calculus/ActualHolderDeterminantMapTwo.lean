import PowerConvexity.Calculus.ActualHolderBilinearMapTwo
import PowerConvexity.Calculus.ActualHolderC2JetIdentificationTwo
import PowerConvexity.Calculus.ClosureStrictBranch
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # The actual complex determinant on the complete C2 Holder jet space

In complex dimension two the determinant is quadratic in the real Hessian.
The same actual Holder space is therefore stable under the nonlinear density
map.  Its Fréchet derivative is the genuine pointwise cofactor contraction.
No inverse, ellipticity estimate, or higher interior regularity is asserted
by this construction.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option synthInstance.maxHeartbeats 100000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Matrix
open scoped ContDiff Topology Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
local notation "Hess" => E →L[ℝ] E →L[ℝ] ℝ
local notation "Mat" => Matrix (Fin 2) (Fin 2) ℂ

def actualDirectedComplexHessianFormTwo (a b : Fin 2 → E) : Hess →L[ℝ] Mat :=
  ({ toFun := fun H i j => (4 : ℂ)⁻¹ *
      ((H (a i) (a j) : ℂ)+(H (b i) (b j) : ℂ)+Complex.I*
        ((H (a i) (b j) : ℂ)-(H (b i) (a j) : ℂ)))
     map_add' := by
       intro H K
       ext i j
       simp only [_root_.add_apply,Matrix.add_apply,Complex.ofReal_add]
       ring
     map_smul' := by
       intro r H
       ext i j
       simp only [_root_.smul_apply,Matrix.smul_apply,smul_eq_mul,Complex.ofReal_mul,
         Complex.real_smul,RingHom.id_apply]
       ring } : Hess →ₗ[ℝ] Mat).toContinuousLinearMap

theorem actualDirectedComplexHessianFormTwo_eq (a b : Fin 2 → E)
    {u : E → ℝ} {x : E} (hu : ContDiffAt ℝ 2 u x) :
    actualDirectedComplexHessianFormTwo a b (realHessian u x)=complexHessian a b u x := by
  ext i j
  exact (complexHessian_real_entry hu a b i j).symm

def actualComplexDeterminantBilinearTwo : Mat →L[ℝ] Mat →L[ℝ] ℝ :=
  ({ toFun := fun A =>
      ({ toFun := fun B => (A 0 0*B 1 1-A 0 1*B 1 0).re
         map_add' := by
           intro B C
           simp only [Matrix.add_apply,mul_add,Complex.add_re,Complex.sub_re]
           ring
         map_smul' := by
           intro r B
           simp only [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,
             RingHom.id_apply,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
             zero_mul,mul_zero,sub_zero,add_zero,Complex.sub_re]
           ring } : Mat →ₗ[ℝ] ℝ).toContinuousLinearMap
     map_add' := by
       intro A B
       ext C
       simp only [LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
         Matrix.add_apply,_root_.add_apply,add_mul,Complex.add_re,Complex.sub_re]
       ring
     map_smul' := by
       intro r A
       ext B
       simp only [LinearMap.coe_toContinuousLinearMap',LinearMap.coe_mk,AddHom.coe_mk,
         Matrix.smul_apply,_root_.smul_apply,Complex.real_smul,smul_eq_mul,RingHom.id_apply,
         Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,mul_zero,sub_zero,
         add_zero,Complex.sub_re]
       ring } : Mat →ₗ[ℝ] Mat →L[ℝ] ℝ).toContinuousLinearMap

theorem actualComplexDeterminantBilinearTwo_self (A : Mat) :
    actualComplexDeterminantBilinearTwo A A=A.det.re := by
  change (A 0 0*A 1 1-A 0 1*A 1 0).re=A.det.re
  rw [Matrix.det_fin_two]

theorem actualComplexDeterminantBilinearTwo_variation (A B : Mat) :
    actualComplexDeterminantBilinearTwo A B+actualComplexDeterminantBilinearTwo B A=
      (∑ i : Fin 2, ∑ j : Fin 2, A.adjugate j i*B i j).re := by
  simp only [actualComplexDeterminantBilinearTwo,LinearMap.coe_toContinuousLinearMap',
    LinearMap.coe_mk,AddHom.coe_mk,Fin.sum_univ_two,Matrix.adjugate_fin_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.neg_re,Complex.neg_im]
  ring

def actualHessianDeterminantBilinearTwo (a b : Fin 2 → E) : Hess →L[ℝ] Hess →L[ℝ] ℝ :=
  actualComplexDeterminantBilinearTwo.bilinearComp
    (actualDirectedComplexHessianFormTwo a b) (actualDirectedComplexHessianFormTwo a b)

variable (U : Set E) [CompactSpace (closure U)]
local instance actualDensityJetSeminormed (alpha : ℝ) :
    SeminormedAddCommGroup (actualHolderC2JetSpaceTwo U alpha) :=
  (inferInstance : NormedAddCommGroup (actualHolderC2JetSpaceTwo U alpha)).toSeminormedAddCommGroup

def actualHolderDeterminantTwo (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha) : actualHolderLoadSpaceTwo (closure U) ℝ alpha :=
  actualHolderLoadBilinearTwo alpha (actualHessianDeterminantBilinearTwo a b)
    (actualHolderC2JetSpaceTwo_hessian U alpha p) (actualHolderC2JetSpaceTwo_hessian U alpha p)

theorem actualHolderDeterminantTwo_apply (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha) (x : closure U) :
    actualHolderLoadSpaceTwo_value (closure U) ℝ alpha (actualHolderDeterminantTwo U alpha a b p) x=
      (actualDirectedComplexHessianFormTwo a b
        (actualHolderLoadSpaceTwo_value (closure U) Hess alpha
          (actualHolderC2JetSpaceTwo_hessian U alpha p) x)).det.re := by
  rw [actualHolderDeterminantTwo,actualHolderLoadBilinearTwo_apply]
  exact actualComplexDeterminantBilinearTwo_self _

theorem actualHolderDeterminantTwo_eq_actual (hU : IsOpen U) (alpha : ℝ)
    (a b : Fin 2 → E) (p : actualHolderC2JetSpaceTwo U alpha) {x : E} (hx : x ∈ U) :
    actualHolderLoadSpaceTwo_value (closure U) ℝ alpha (actualHolderDeterminantTwo U alpha a b p)
      ⟨x,subset_closure hx⟩ =
      (complexHessian a b (actualClosureExtensionTwo U p.1.1) x).det.re := by
  obtain ⟨hp,J,_,hJ⟩ := actualHolderC2JetSpaceTwo_regular U hU alpha p
  rw [actualHolderDeterminantTwo_apply]
  have he : actualHolderLoadSpaceTwo_value (closure U) Hess alpha
      (actualHolderC2JetSpaceTwo_hessian U alpha p) ⟨x,subset_closure hx⟩ =
      realHessian (actualClosureExtensionTwo U p.1.1) x := by
    have h := J.hessian_eq hx
    rw [hJ,actualClosureExtensionTwo_apply U _ (subset_closure hx)] at h
    exact h
  rw [he,actualDirectedComplexHessianFormTwo_eq a b (hp.contDiffAt (hU.mem_nhds hx))]

def actualHolderDeterminantDerivativeTwo (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha) :
    actualHolderC2JetSpaceTwo U alpha →L[ℝ] actualHolderLoadSpaceTwo (closure U) ℝ alpha :=
  let B := actualHolderLoadBilinearTwo (K := closure U) alpha (actualHessianDeterminantBilinearTwo a b)
  let H := actualHolderC2JetSpaceTwo_hessian U alpha
  B.precompR (actualHolderC2JetSpaceTwo U alpha) (H p) H+
    B.precompL (actualHolderC2JetSpaceTwo U alpha) H (H p)

theorem actualHolderDeterminantTwo_hasStrictFDerivAt (alpha : ℝ) (a b : Fin 2 → E)
    (p : actualHolderC2JetSpaceTwo U alpha) :
    HasStrictFDerivAt (actualHolderDeterminantTwo U alpha a b)
      (actualHolderDeterminantDerivativeTwo U alpha a b p) p := by
  let B := actualHolderLoadBilinearTwo (K := closure U) alpha (actualHessianDeterminantBilinearTwo a b)
  let H := actualHolderC2JetSpaceTwo_hessian U alpha
  exact B.hasStrictFDerivAt_of_bilinear (H.hasStrictFDerivAt) (H.hasStrictFDerivAt)

theorem actualHolderDeterminantDerivativeTwo_apply (alpha : ℝ) (a b : Fin 2 → E)
    (p q : actualHolderC2JetSpaceTwo U alpha) (x : closure U) :
    actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
      (actualHolderDeterminantDerivativeTwo U alpha a b p q) x =
      (∑ i : Fin 2, ∑ j : Fin 2,
        (actualDirectedComplexHessianFormTwo a b
          (actualHolderLoadSpaceTwo_value (closure U) Hess alpha
            (actualHolderC2JetSpaceTwo_hessian U alpha p) x)).adjugate j i *
        (actualDirectedComplexHessianFormTwo a b
          (actualHolderLoadSpaceTwo_value (closure U) Hess alpha
            (actualHolderC2JetSpaceTwo_hessian U alpha q) x)) i j).re := by
  change actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
    (actualHolderLoadBilinearTwo alpha (actualHessianDeterminantBilinearTwo a b)
      (actualHolderC2JetSpaceTwo_hessian U alpha p) (actualHolderC2JetSpaceTwo_hessian U alpha q)+
     actualHolderLoadBilinearTwo alpha (actualHessianDeterminantBilinearTwo a b)
      (actualHolderC2JetSpaceTwo_hessian U alpha q) (actualHolderC2JetSpaceTwo_hessian U alpha p)) x = _
  simp only [map_add,ContinuousMap.add_apply,actualHolderLoadBilinearTwo_apply]
  exact actualComplexDeterminantBilinearTwo_variation _ _

end PowerConvexity
