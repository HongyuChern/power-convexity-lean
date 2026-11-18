import PowerConvexity.Analysis.ActualFlatClosedInputFour
import PowerConvexity.Analysis.ActualFlatPhysicalNormalizationFour

/-! # The same actual equation normalized at an arbitrary flat boundary centre -/
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

def actualFlatCenteredNormalizeFour {N c : E} {lam Lambda alpha Ka Kf F B r k M L : ℝ}
    (G : E ≃L[ℝ] E) (hr : 0 < r) (halpha : 0 ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 1 ≤ M) (hL : 1 ≤ L)
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B)
    (hc : inner ℝ N c=0) (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ L)
    (hmap : MapsTo (fun z : E => c+G (r • z)) (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N 1))
    (hmapC : MapsTo (fun z : E => c+G (r • z)) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1))
    (hfreeze : actualLinearCongruenceMatrixTwo G (D.coeff.a c)=1) :
    ActualFlatLinearInputFour N (lam/M^2) (Lambda*L^2) alpha
      (L^2*Ka*(r*M)^alpha) (r^2*Kf*(r*M)^alpha) B := by
  have hinc : actualFlatUpperBallFour N 1 ⊆ actualFlatClosedUpperBallFour N 1 :=
    fun x hx => ⟨ball_subset_closedBall hx.1,by
      change 0 ≤ inner ℝ N x
      exact le_of_lt hx.2⟩
  have hzero : (0 : E) ∈ actualFlatClosedUpperBallFour N 1 := by
    constructor
    · simp only [mem_closedBall,dist_self]; norm_num
    · change 0 ≤ inner ℝ N (0 : E); simp
  have ht (n : ℕ∞ω) : ContDiffOn ℝ n (fun z : E => c+G (r • z)) (actualFlatUpperBallFour N 1) := by
    fun_prop
  have htC : ContinuousOn (fun z : E => c+G (r • z)) (actualFlatClosedUpperBallFour N 1) := by
    fun_prop
  have hAholder := actual_linear_scaled_congruence_holder_four G hr.le halpha hKa
    (zero_le_one.trans hM) (zero_le_one.trans hL) hG hInv hmapC D.holder
  have hfholder := actual_affine_scalar_source_holder_four G hr.le halpha hKf
    (zero_le_one.trans hM) hG hmapC D.source_holder
  have hbounds := actual_affine_normalized_uniform_ellipticity_four c G hr D.coeff hmap
    D.lower D.upper hM hL hG hInv
  exact {
    coeff := actualAffineNormalizedCoeffFour c G hr D.coeff hmap
    source := fun z => r^2*D.source (c+G (r • z))
    solution := fun z => D.solution (c+G (r • z))
    lower := hbounds.1
    upper := hbounds.2
    positive := actual_affine_normalized_coeff_posDef_four c G hr D.coeff hmap D.positive
    frozen := actual_affine_normalized_coeff_frozen_four c G hr D.coeff hmap hfreeze
    regular := actual_affine_normalized_coeff_regular_four c G hr D.coeff hmap D.regular
    divergence := actual_affine_normalized_coeff_divergence_four (actualFlatUpperBallFour_isOpen N 1)
      c G hr D.coeff hmap D.regular D.divergence
    holder := fun x hx y hy => hAholder x (hinc hx) y (hinc hy)
    growth := by
      intro x hx
      have hh := hAholder x (hinc hx) 0 hzero
      simpa only [actualAffineNormalizedCoeffFour_a,smul_zero,map_zero,add_zero,hfreeze,sub_zero] using hh
    source_regular := contDiffOn_const.mul (D.source_regular.comp (ht 1) hmap)
    source_holder := fun x hx y hy => hfholder x (hinc hx) y (hinc hy)
    source_growth := by
      intro x hx
      simpa only [sub_zero] using hfholder x (hinc hx) 0 hzero
    solution_regular := D.solution_regular.comp (ht 2) hmap
    solution_continuous := D.solution_continuous.comp htC hmapC
    solution_zero := actual_flat_affine_zero_boundary_four G hc hN hmapC D.solution_zero
    solution_bound := fun x hx => D.solution_bound _ (hmapC hx)
    equation := by
      intro x hx
      exact actual_affine_classical_equation_transport_four G c r
        (D.solution_regular.contDiffAt ((actualFlatUpperBallFour_isOpen N 1).mem_nhds (hmap hx)))
        (D.equation _ (hmap hx))
  }

@[simp] theorem actualFlatCenteredNormalizeFour_solution {N c : E}
    {lam Lambda alpha Ka Kf F B r k M L : ℝ} (G : E ≃L[ℝ] E)
    (hr : 0 < r) (halpha : 0 ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 1 ≤ M) (hL : 1 ≤ L)
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B)
    (hc : inner ℝ N c=0) (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ L)
    (hmap : MapsTo (fun z : E => c+G (r • z)) (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N 1))
    (hmapC : MapsTo (fun z : E => c+G (r • z)) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1))
    (hfreeze : actualLinearCongruenceMatrixTwo G (D.coeff.a c)=1) (z : E) :
    (actualFlatCenteredNormalizeFour G hr halpha hKa hKf hM hL D hc hN hG hInv hmap hmapC hfreeze).solution z
      = D.solution (c+G (r • z)) := rfl

@[simp] theorem actualFlatCenteredNormalizeFour_source {N c : E}
    {lam Lambda alpha Ka Kf F B r k M L : ℝ} (G : E ≃L[ℝ] E)
    (hr : 0 < r) (halpha : 0 ≤ alpha) (hKa : 0 ≤ Ka) (hKf : 0 ≤ Kf)
    (hM : 1 ≤ M) (hL : 1 ≤ L)
    (D : ActualFlatClosedLinearInputFour N lam Lambda alpha Ka Kf F B)
    (hc : inner ℝ N c=0) (hN : ∀ v : E, inner ℝ N (G v)=k*inner ℝ N v)
    (hG : ‖G.toContinuousLinearMap‖ ≤ M) (hInv : ‖G.symm.toContinuousLinearMap‖ ≤ L)
    (hmap : MapsTo (fun z : E => c+G (r • z)) (actualFlatUpperBallFour N 1) (actualFlatUpperBallFour N 1))
    (hmapC : MapsTo (fun z : E => c+G (r • z)) (actualFlatClosedUpperBallFour N 1)
      (actualFlatClosedUpperBallFour N 1))
    (hfreeze : actualLinearCongruenceMatrixTwo G (D.coeff.a c)=1) (z : E) :
    (actualFlatCenteredNormalizeFour G hr halpha hKa hKf hM hL D hc hN hG hInv hmap hmapC hfreeze).source z
      = r^2*D.source (c+G (r • z)) := rfl

end PowerConvexity
