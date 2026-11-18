import PowerConvexity.Analysis.ActualGraphShearAlgebraFour
import PowerConvexity.Analysis.ActualLocalClassicalWeakTwo

/-! # Actual scalar fluxes with their full column-divergence term -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

def actualCoefficientColumnDivergenceFour (A : E → Mat) (x : E) : E :=
  WithLp.toLp 2 (fun j => ∑ i, fderiv ℝ (fun y => A y i j) x (EuclideanSpace.single i 1))

theorem actual_classical_divergence_with_drift_four
    {A : E → Matrix (Fin (2+2)) (Fin (2+2)) ℝ} {v : E → ℝ} {x : E}
    (hA : ∀ i j, DifferentiableAt ℝ (fun y => A y i j) x)
    (hv : ContDiffAt ℝ 2 v x) :
    classicalDivergence (fun y => matMulE (A y) (smoothGradField v y)) x =
      ∑ i, ∑ j, A x i j *
        realHessian v x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) +
      fderiv ℝ v x (actualCoefficientColumnDivergenceFour A x) := by
  let e : Fin (2+2) → E := fun i => EuclideanSpace.single i 1
  have hderiv := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd (j : Fin (2+2)) : DifferentiableAt ℝ (fun y => fderiv ℝ v y (e j)) x :=
    hderiv.clm_apply (differentiableAt_const _)
  have hsecond (i j : Fin (2+2)) :
      fderiv ℝ (fun y => fderiv ℝ v y (e j)) x (e i) =
        realHessian v x (e i) (e j) := by
    rw [(hderiv.hasFDerivAt.clm_apply (hasFDerivAt_const (e j) x)).fderiv]
    simp [realHessian]
  change (∑ i, fderiv ℝ (fun y => ∑ j, A y i j * fderiv ℝ v y (e j)) x (e i)) = _
  have hexpand (i : Fin (2+2)) :
      fderiv ℝ (fun y => ∑ j, A y i j * fderiv ℝ v y (e j)) x (e i) =
        ∑ j, (A x i j * realHessian v x (e i) (e j) +
          fderiv ℝ v x (e j) * fderiv ℝ (fun y => A y i j) x (e i)) := by
    rw [fderiv_fun_sum (u := Finset.univ)
      (A := fun j y => A y i j * fderiv ℝ v y (e j))
      (fun j _ => (hA i j).mul (hd j)), ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [fderiv_fun_mul (hA i j) (hd j)]
    simp only [ContinuousLinearMap.add_apply, _root_.smul_apply, smul_eq_mul, hsecond]
  simp only [hexpand, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [← actual_coordinate_sum_four (actualCoefficientColumnDivergenceFour A x)]
  simp only [map_sum,map_smul,smul_eq_mul,actualCoefficientColumnDivergenceFour,PiLp.toLp_apply,e]
  apply Finset.sum_congr rfl
  intro j _
  ring

end PowerConvexity
