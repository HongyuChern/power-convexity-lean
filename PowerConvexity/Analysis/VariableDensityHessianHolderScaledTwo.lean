import PowerConvexity.Analysis.VariableDensityHessianHolderLocalTwo
import CHS.Calculus.EuclideanRescaling

/-! # Exact radius scaling of the variable-density estimate.
The potential is R^-2 u(x0+R x), while the density has no amplitude factor.
Its logarithmic second source scales by R^2. Constants precede both the
center and unknown functions; the positive radius is fixed beforehand.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Metric Matrix
open scoped BigOperators ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
local notation "E" => AmbientSpace (2+2)

theorem density_second_source_homothety_two
    {f : E → ℝ} {x₀ x : E} {R : ℝ}
    (hf : ContDiffAt ℝ 2 f (x₀+R • x)) (v : E) :
    (realHessian (fun y => f (x₀+R • y)) x v v*f (x₀+R • x)-
        (fderiv ℝ (fun y => f (x₀+R • y)) x v)^2)/(f (x₀+R • x))^2 =
      R^2*((realHessian f (x₀+R • x) v v*f (x₀+R • x)-
        (fderiv ℝ f (x₀+R • x) v)^2)/(f (x₀+R • x))^2) := by
  have ha : HasFDerivAt (fun y : E => x₀+R • y)
      (R • ContinuousLinearMap.id ℝ E) x :=
    (R • ContinuousLinearMap.id ℝ E).hasFDerivAt.const_add x₀
  have hD := ((hf.differentiableAt (by norm_num)).hasFDerivAt.comp x ha).fderiv
  have hH : realHessian (fun y => f (x₀+R • y)) x v v =
      realHessian f (x₀+R • x) (R • v) (R • v) := by
    simpa only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.id_apply] using
      realHessian_comp_affine (R • ContinuousLinearMap.id ℝ E) x₀ hf v v
  simp only [Function.comp_def] at hD
  rw [hH,hD]
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply,map_smul,smul_eq_mul]
  ring

theorem exists_variable_density_hessian_holder_scaled_two
    {M D P L Csrc : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc)
    (R : ℝ) (hR : 0 < R) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ (x₀ : E) (u f : E → ℝ), ContDiffOn ℝ 4 u (ball x₀ (2*R)) →
      ContDiffOn ℝ 2 f (ball x₀ (2*R)) →
      (∀ x ∈ ball x₀ (2*R),
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball x₀ (2*R),
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball x₀ (2*R), 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball x₀ (2*R), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      (∀ x ∈ ball x₀ (2*R), ∀ y ∈ ball x₀ (2*R), |u x-u y| ≤ P*‖x-y‖) →
      (∀ x ∈ ball x₀ (2*R), ∀ y ∈ ball x₀ (2*R), |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball x₀ (2*R), ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
        ‖realBlockHessian realDirections imagDirections u x-
          realBlockHessian realDirections imagDirections u y‖ ≤ C*(‖x-y‖/R)^alpha := by
  obtain ⟨alpha,C,halpha,halpha1,hC,hunit⟩ :=
    exists_variable_density_hessian_holder_local_two (M := M) (D := D)
      (P := P/R) (L := L*R) (Csrc := Csrc*R^2) hM hD
      (div_nonneg hP hR.le) (mul_nonneg hL hR.le) (mul_nonneg hCsrc (sq_nonneg R))
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro x₀ u f hu hf hdet hA hfb hentry hup hfp hsource
  let v := euclideanRescalePotential u x₀ R
  let g : E → ℝ := fun z => f (x₀+R • z)
  have hmap : MapsTo (fun z : E => x₀+R • z) (ball (0 : E) 2) (ball x₀ (2*R)) := by
    intro z hz
    rw [mem_ball,dist_eq_norm]
    simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    have hz' : ‖z‖ < 2 := by simpa only [mem_ball,dist_zero_right] using hz
    nlinarith
  have hv : ContDiffOn ℝ 4 v (ball (0 : E) 2) :=
    euclideanRescalePotential_contDiffOn hu x₀ R hmap
  have hg : ContDiffOn ℝ 2 g (ball (0 : E) 2) :=
    hf.comp (by fun_prop) hmap
  have hH (z : E) (hz : z ∈ ball (0 : E) 2) :
      realHessian v z = realHessian u (x₀+R • z) :=
    realHessian_euclideanRescalePotential hR.ne'
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hmap hz))).of_le (by norm_num))
  have hcomplex (z : E) (hz : z ∈ ball (0 : E) 2) :
      complexHessian realDirections imagDirections v z =
        complexHessian realDirections imagDirections u (x₀+R • z) :=
    complexHessian_euclideanRescalePotential realDirections imagDirections hR.ne'
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hmap hz))).of_le (by norm_num))
  have hvdet (z : E) (hz : z ∈ ball (0 : E) 2) :
      (complexHessian realDirections imagDirections v z).det = (g z : ℂ) := by
    rw [hcomplex z hz]
    exact hdet _ (hmap hz)
  have hvA (z : E) (hz : z ∈ ball (0 : E) 2) :
      (complexHessian realDirections imagDirections v z).PosDef := by
    rw [hcomplex z hz]
    exact hA _ (hmap hz)
  have hventry (z : E) (hz : z ∈ ball (0 : E) 2) (i j : Fin (2+2)) :
      |euclideanHessian v z i j| ≤ M := by
    simp only [euclideanHessian,hH z hz]
    exact hentry _ (hmap hz) i j
  have hdist (z w : E) : ‖(x₀+R • z)-(x₀+R • w)‖ = R*‖z-w‖ := by
    rw [add_sub_add_left_eq_sub,←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hR]
  have hvLip (z : E) (hz : z ∈ ball (0 : E) 2) (w : E) (hw : w ∈ ball (0 : E) 2) :
      |v z-v w| ≤ (P/R)*‖z-w‖ := by
    have hh := hup _ (hmap hz) _ (hmap hw)
    rw [hdist] at hh
    have hfac : 0 ≤ (R*R)⁻¹ := inv_nonneg.mpr (mul_nonneg hR.le hR.le)
    change |(R*R)⁻¹*u (x₀+R • z)-(R*R)⁻¹*u (x₀+R • w)| ≤ _
    rw [←mul_sub,abs_mul,abs_of_nonneg hfac]
    calc
      _ ≤ (R*R)⁻¹*(P*(R*‖z-w‖)) := mul_le_mul_of_nonneg_left hh hfac
      _ = _ := by field_simp
  have hgLip (z : E) (hz : z ∈ ball (0 : E) 2) (w : E) (hw : w ∈ ball (0 : E) 2) :
      |g z-g w| ≤ (L*R)*‖z-w‖ := by
    have hh := hfp _ (hmap hz) _ (hmap hw)
    rw [hdist] at hh
    simpa only [mul_assoc] using hh
  have hgsource (z : E) (hz : z ∈ ball (0 : E) 2) (q : E) :
      -((Csrc*R^2)*‖q‖^2) ≤
        (realHessian g z q q*g z-(fderiv ℝ g z q)^2)/(g z)^2 := by
    dsimp only [g]
    rw [density_second_source_homothety_two (hf.contDiffAt (isOpen_ball.mem_nhds (hmap hz)))]
    have hh := mul_le_mul_of_nonneg_left (hsource _ (hmap hz) q) (sq_nonneg R)
    nlinarith only [hh]
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

theorem exists_variable_density_hessian_holder_scaled_entry_two
    {M D P L Csrc : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc)
    (R : ℝ) (hR : 0 < R) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ (x₀ : E) (u f : E → ℝ), ContDiffOn ℝ 4 u (ball x₀ (2*R)) →
      ContDiffOn ℝ 2 f (ball x₀ (2*R)) →
      (∀ x ∈ ball x₀ (2*R),
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball x₀ (2*R),
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball x₀ (2*R), 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball x₀ (2*R), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      (∀ x ∈ ball x₀ (2*R), ∀ y ∈ ball x₀ (2*R), |u x-u y| ≤ P*‖x-y‖) →
      (∀ x ∈ ball x₀ (2*R), ∀ y ∈ ball x₀ (2*R), |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball x₀ (2*R), ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R, ∀ i j,
        |euclideanHessian u x i j-euclideanHessian u y i j| ≤ C*(‖x-y‖/R)^alpha := by
  obtain ⟨alpha,C,halpha,halpha1,hC,hbound⟩ :=
    exists_variable_density_hessian_holder_scaled_two hM hD hP hL hCsrc R hR
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro x₀ u f hu hf hdet hA hfb hentry hup hfp hsource x hx y hy i j
  exact (abs_euclideanHessian_sub_le_block_norm u x y i j).trans
    (hbound x₀ u f hu hf hdet hA hfb hentry hup hfp hsource x hx y hy)

end PowerConvexity
