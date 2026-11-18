import PowerConvexity.Analysis.ActualLinearCoefficientRegularityTwo
import PowerConvexity.Analysis.ActualScalarWeakScalingTwo

/-! # Regularity and divergence under the physical affine dilation

The coefficient of the rescaled weak equation is `a(c+r*z)`, without an
extra scalar factor.  The scalar source receives the factor `r^2` in the
already proved weak scaling theorem.  The column divergence below receives
exactly the factor `r`.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Filter Metric Matrix MeasureTheory
open scoped ContDiff Topology BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "Mat" => Matrix (Fin (2+2)) (Fin (2+2)) ℝ
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem actual_affine_coefficient_contDiffOn_two
    {U : Set E} {a : E → Mat} {n : ℕ∞ω}
    (ha : ∀ i j, ContDiffOn ℝ n (fun x => a x i j) U)
    (c : E) (r : ℝ) (i j : Fin (2+2)) :
    ContDiffOn ℝ n (fun z => a (c+r • z) i j) ((fun z => c+r • z) ⁻¹' U) := by
  have hT : ContDiff ℝ n (fun z : E => c+r • z) :=
    by
      fun_prop
  exact (ha i j).comp hT.contDiffOn (fun _ hz => hz)

theorem actual_affine_coefficient_fderiv_apply_two
    {a : E → Mat} {c z : E} {r : ℝ}
    (ha : ∀ i j, DifferentiableAt ℝ (fun x => a x i j) (c+r • z))
    (i j : Fin (2+2)) (v : E) :
    fderiv ℝ (fun y => a (c+r • y) i j) z v =
      r * fderiv ℝ (fun y => a y i j) (c+r • z) v := by
  have hT : HasFDerivAt (fun y : E => c+r • y)
      (r • ContinuousLinearMap.id ℝ E) z :=
    ((hasFDerivAt_id z).const_smul r).const_add c
  have hd := (ha i j).hasFDerivAt.comp z hT
  have he := hd.fderiv
  change fderiv ℝ (fun y => a (c+r • y) i j) z = _ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem actual_affine_coefficient_column_divergence_two
    {a : E → Mat} {c z : E} {r : ℝ}
    (ha : ∀ i j, DifferentiableAt ℝ (fun x => a x i j) (c+r • z))
    (j : Fin (2+2)) :
    (∑ i, fderiv ℝ (fun y => a (c+r • y) i j) z (EuclideanSpace.single i 1)) =
      r * ∑ i, fderiv ℝ (fun y => a y i j) (c+r • z) (EuclideanSpace.single i 1) := by
  simp_rw [actual_affine_coefficient_fderiv_apply_two ha]
  exact (Finset.mul_sum ..).symm

theorem actual_affine_coefficient_divergence_free_two
    {U : Set E} (hU : IsOpen U) {a : E → Mat}
    (ha : ∀ i j, ContDiffOn ℝ 1 (fun x => a x i j) U)
    (hdiv : ∀ x ∈ U, ∀ j,
      (∑ i, fderiv ℝ (fun y => a y i j) x (EuclideanSpace.single i 1)) = 0)
    (c : E) (r : ℝ) :
    ∀ z ∈ (fun z => c+r • z) ⁻¹' U, ∀ j,
      (∑ i, fderiv ℝ (fun y => a (c+r • y) i j) z (EuclideanSpace.single i 1)) = 0 := by
  intro z hz j
  rw [actual_affine_coefficient_column_divergence_two
    (fun i k => ((ha i k).contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))]
  rw [hdiv _ hz, mul_zero]

end PowerConvexity
