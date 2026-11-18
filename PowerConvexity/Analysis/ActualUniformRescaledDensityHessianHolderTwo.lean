import PowerConvexity.Analysis.VariableDensityHessianHolderScaledTwo
import PowerConvexity.Calculus.ActualLocalTangentNormalization

/-! # Actual radius-uniform nonlinear interior Hessian Holder bounds

Subtract the actual tangent affine function after the exact quadratic
rescaling. A common Hessian norm bound gives a common normalized gradient
bound. Consequently alpha and C precede every R in (0,1], center and solution.
No third derivative bound or family Holder bound is assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Metric Matrix
open scoped BigOperators ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem actual_uniform_rescaled_density_hessian_holder_two
    {M D L Csrc : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ R : ℝ, 0 < R → R ≤ 1 →
      ∀ (x₀ : E) (u f : E → ℝ), ContDiffOn ℝ 4 u (ball x₀ (2*R)) →
      ContDiffOn ℝ 2 f (ball x₀ (2*R)) →
      (∀ x ∈ ball x₀ (2*R),
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball x₀ (2*R),
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball x₀ (2*R), 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball x₀ (2*R), ‖realHessian u x‖ ≤ M) →
      (∀ x ∈ ball x₀ (2*R), ∀ y ∈ ball x₀ (2*R), |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball x₀ (2*R), ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
        ‖realBlockHessian realDirections imagDirections u x-
          realBlockHessian realDirections imagDirections u y‖ ≤ C*(‖x-y‖/R)^alpha := by
  obtain ⟨alpha,C,halpha,halpha1,hC,hunit⟩ :=
    exists_variable_density_hessian_holder_local_two (M := M) (D := D)
      (P := 2*M) (L := L) (Csrc := Csrc) hM hD (by positivity) hL hCsrc
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro R hR hR1 x₀ u f hu hf hdet hA hfb hHnorm hfp hsource
  let w := euclideanRescalePotential u x₀ R
  let v := tangentNormalized w
  let g : E → ℝ := fun z => f (x₀+R • z)
  have hmap : MapsTo (fun z : E => x₀+R • z) (ball (0 : E) 2) (ball x₀ (2*R)) := by
    intro z hz
    rw [mem_ball,dist_eq_norm]
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    have hz' : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith
  have hw : ContDiffOn ℝ 4 w (ball (0 : E) 2) :=
    euclideanRescalePotential_contDiffOn hu x₀ R hmap
  have hv : ContDiffOn ℝ 4 v (ball (0 : E) 2) :=
    (hw.sub contDiffOn_const).sub (fderiv ℝ w 0).contDiff.contDiffOn
  have hg : ContDiffOn ℝ 2 g (ball (0 : E) 2) :=
    hf.comp (by fun_prop) hmap
  have hw2 (z : E) (hz : z ∈ ball (0 : E) 2) : ContDiffAt ℝ 2 w z :=
    (hw.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by norm_num)
  have hv2 (z : E) (hz : z ∈ ball (0 : E) 2) : ContDiffAt ℝ 2 v z :=
    (hv.contDiffAt (isOpen_ball.mem_nhds hz)).of_le (by norm_num)
  have hH (z : E) (hz : z ∈ ball (0 : E) 2) :
      realHessian v z = realHessian u (x₀+R • z) := by
    rw [show realHessian v z=realHessian w z from actual_realHessian_tangentNormalized_at (hw2 z hz)]
    exact realHessian_euclideanRescalePotential hR.ne'
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hmap hz))).of_le (by norm_num))
  have hcomplex (z : E) (hz : z ∈ ball (0 : E) 2) :
      complexHessian realDirections imagDirections v z =
        complexHessian realDirections imagDirections u (x₀+R • z) := by
    rw [show complexHessian realDirections imagDirections v z =
      complexHessian realDirections imagDirections w z from
      actual_complexHessian_tangentNormalized_at (hw2 z hz) realDirections imagDirections]
    exact complexHessian_euclideanRescalePotential realDirections imagDirections hR.ne'
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hmap hz))).of_le (by norm_num))
  have hvdet (z : E) (hz : z ∈ ball (0 : E) 2) :
      (complexHessian realDirections imagDirections v z).det = (g z : ℂ) := by
    rw [hcomplex z hz]
    exact hdet _ (hmap hz)
  have hvA (z : E) (hz : z ∈ ball (0 : E) 2) :
      (complexHessian realDirections imagDirections v z).PosDef := by
    rw [hcomplex z hz]
    exact hA _ (hmap hz)
  have hvH (z : E) (hz : z ∈ ball (0 : E) 2) : ‖realHessian v z‖ ≤ M := by
    rw [hH z hz]
    exact hHnorm _ (hmap hz)
  have hventry (z : E) (hz : z ∈ ball (0 : E) 2) (i j : Fin (2+2)) :
      |euclideanHessian v z i j| ≤ M := by
    have hh := (realHessian v z).le_opNorm₂
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
    have hh' : |euclideanHessian v z i j| ≤ ‖realHessian v z‖ := by
      simpa only [euclideanHessian,EuclideanSpace.norm_single,norm_one,mul_one,Real.norm_eq_abs] using hh
    exact hh'.trans (hvH z hz)
  have hvD0 : fderiv ℝ v 0=0 := by
    rw [show fderiv ℝ v 0=fderiv ℝ w 0-fderiv ℝ w 0 from
      actual_fderiv_tangentNormalized_at ((hw2 0 (mem_ball_self (by norm_num))).differentiableAt (by norm_num)),sub_self]
  have hvD (z : E) (hz : z ∈ ball (0 : E) 2) : ‖fderiv ℝ v z‖ ≤ 2*M := by
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => ((hv2 y hy).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      (fun y hy => hvH y hy) (convex_ball (0 : E) 2)
      (mem_ball_self (by norm_num : (0 : ℝ) < 2)) hz
    rw [hvD0,sub_zero,sub_zero] at hh
    have hz2 : ‖z‖ ≤ 2 := (show ‖z‖ < 2 from by simpa only [mem_ball,dist_zero_right] using hz).le
    exact hh.trans ((mul_le_mul_of_nonneg_left hz2 hM).trans_eq (by ring))
  have hdist (z w : E) : ‖(x₀+R • z)-(x₀+R • w)‖ = R*‖z-w‖ := by
    rw [add_sub_add_left_eq_sub,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
  have hvLip (z : E) (hz : z ∈ ball (0 : E) 2) (q : E) (hq : q ∈ ball (0 : E) 2) :
      |v z-v q| ≤ (2*M)*‖z-q‖ := by
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y hy => (hv2 y hy).differentiableAt (by norm_num)) hvD
      (convex_ball (0 : E) 2) hq hz
  have hgLip (z : E) (hz : z ∈ ball (0 : E) 2) (q : E) (hq : q ∈ ball (0 : E) 2) :
      |g z-g q| ≤ L*‖z-q‖ := by
    have hh := hfp _ (hmap hz) _ (hmap hq)
    rw [hdist] at hh
    exact hh.trans (by nlinarith [norm_nonneg (z-q),mul_nonneg hL (norm_nonneg (z-q))])
  have hgsource (z : E) (hz : z ∈ ball (0 : E) 2) (q : E) :
      -(Csrc*‖q‖^2) ≤
        (realHessian g z q q*g z-(fderiv ℝ g z q)^2)/(g z)^2 := by
    dsimp only [g]
    rw [density_second_source_homothety_two (hf.contDiffAt (isOpen_ball.mem_nhds (hmap hz)))]
    have hh := mul_le_mul_of_nonneg_left (hsource _ (hmap hz) q) (sq_nonneg R)
    have hR2 : R^2 ≤ 1 := by nlinarith
    have hterm : 0 ≤ Csrc*‖q‖^2 := mul_nonneg hCsrc (sq_nonneg _)
    nlinarith only [hh,mul_le_mul_of_nonneg_right hR2 hterm]
  intro x hx y hy
  let xi : E := R⁻¹ • (x-x₀)
  let eta : E := R⁻¹ • (y-x₀)
  have hxi : xi ∈ ball (0 : E) 1 := by
    have hx' : ‖x-x₀‖ < R := by simpa only [mem_ball,dist_eq_norm] using hx
    simp only [xi,mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_lt_iff₀ hR).mpr (by simpa using hx')
  have heta : eta ∈ ball (0 : E) 1 := by
    have hy' : ‖y-x₀‖ < R := by simpa only [mem_ball,dist_eq_norm] using hy
    simp only [eta,mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    exact (inv_mul_lt_iff₀ hR).mpr (by simpa using hy')
  have hbackx : x₀+R • xi = x := by
    simp only [xi,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel]
  have hbacky : x₀+R • eta = y := by
    simp only [eta,smul_smul,mul_inv_cancel₀ hR.ne',one_smul,add_sub_cancel]
  have hxi2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) hxi
  have heta2 := (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2)) heta
  have hblockx : realBlockHessian realDirections imagDirections v xi =
      realBlockHessian realDirections imagDirections u x := by
    ext i j
    change realHessian v xi _ _ = realHessian u x _ _
    rw [hH xi hxi2,hbackx]
  have hblocky : realBlockHessian realDirections imagDirections v eta =
      realBlockHessian realDirections imagDirections u y := by
    ext i j
    change realHessian v eta _ _ = realHessian u y _ _
    rw [hH eta heta2,hbacky]
  have hnorm : ‖xi-eta‖ = ‖x-y‖/R := by
    have hdif : xi-eta = R⁻¹ • (x-y) := by
      dsimp only [xi,eta]
      rw [←smul_sub]
      congr 1
      abel
    rw [hdif,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR)]
    ring
  have hh := hunit v g hv hg hvdet hvA (fun z hz => hfb _ (hmap hz)) hventry
    hvLip hgLip hgsource xi hxi eta heta
  rwa [hblockx,hblocky,hnorm] at hh

end PowerConvexity
