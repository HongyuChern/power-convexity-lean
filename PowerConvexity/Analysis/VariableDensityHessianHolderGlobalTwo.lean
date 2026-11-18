import PowerConvexity.Analysis.VariableDensityHessianOscillationStepTwo
import CHS.Analysis.HessianHolderGlobal

/-! # Interior Holder continuity for the actual variable-density Hessian.
The constants precede the potential. The source correction is retained at
every radius and in the base oscillation, without requiring a C0 bound on u.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
open Set Metric Matrix
open scoped BigOperators ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

theorem correctedHessianOscillationTwo_le
    {u : E → ℝ} (hu : ContDiff ℝ 4 u) (t : Finset (J → ℝ))
    {Csrc R M P : ℝ} (hCsrc : 0 ≤ Csrc) (hR : 0 ≤ R)
    (hM : 0 ≤ M) (hP : 0 ≤ P) {x₀ : E}
    (hbound : ∀ x ∈ closedBall x₀ R,
      ‖realBlockHessian realDirections imagDirections u x‖ ≤ M)
    (hup : ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
      |u x-u y| ≤ P*‖x-y‖) :
    correctedHessianOscillationTwo t Csrc u x₀ R ≤
      2*M*(∑ z : t, realMatrixQuadraticWeight z.1)+
      2*P*R*(∑ z : t, hessianCorrectionCoefficientTwo Csrc z.1) := by
  classical
  have habs (z : t) (x : E) (hx : x ∈ closedBall x₀ R) :
      |hessianObservable u z.1 x| ≤ realMatrixQuadraticWeight z.1*M :=
    (abs_realMatrixQuadratic_le _ _).trans
      (mul_le_mul_of_nonneg_left (hbound x hx) (sq_nonneg _))
  have hosc (z : t) : compactOsc (correctedHessianObservableTwo Csrc u z.1)
      (closedBall x₀ R) ≤ 2*M*realMatrixQuadraticWeight z.1+
        2*P*R*hessianCorrectionCoefficientTwo Csrc z.1 := by
    apply compactOsc_le_of_sub_le (isCompact_closedBall _ _) ⟨x₀,mem_closedBall_self hR⟩
      (correctedHessianObservableTwo_continuous Csrc hu z.1).continuousOn
    intro x hx y hy
    have hdist : ‖x-y‖ ≤ 2*R := by
      have ht := dist_triangle x x₀ y
      have hx' : dist x x₀ ≤ R := hx
      have hy' : dist x₀ y ≤ R := by simpa only [mem_closedBall,dist_comm] using hy
      rw [dist_eq_norm x y] at ht
      linarith
    have hpot : u x-u y ≤ 2*P*R :=
      (le_abs_self _).trans ((hup x hx y hy).trans (by
        nlinarith only [mul_le_mul_of_nonneg_left hdist hP]))
    have hpotk := mul_le_mul_of_nonneg_left hpot
      (hessianCorrectionCoefficientTwo_nonneg hCsrc z.1)
    have h1 := (abs_le.mp (habs z x hx)).2
    have h2 := (abs_le.mp (habs z y hy)).1
    dsimp only [correctedHessianObservableTwo]
    nlinarith only [h1,h2,hpotk]
  calc
    _ ≤ ∑ z : t, (2*M*realMatrixQuadraticWeight z.1+
        2*P*R*hessianCorrectionCoefficientTwo Csrc z.1) :=
      Finset.sum_le_sum (fun z _ => hosc z)
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum]

theorem exists_variable_density_hessian_holder_global_two
    {M D P L Csrc : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ u f : E → ℝ, ContDiff ℝ 4 u →
      ContDiffOn ℝ 2 f (ball (0 : E) (3/2 : ℝ)) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ),
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ),
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ), 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ), ∀ i j, |euclideanHessian u x i j| ≤ M) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ), ∀ y ∈ ball (0 : E) (3/2 : ℝ),
        |u x-u y| ≤ P*‖x-y‖) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ), ∀ y ∈ ball (0 : E) (3/2 : ℝ),
        |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball (0 : E) (3/2 : ℝ), ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
        ‖realBlockHessian realDirections imagDirections u x-
          realBlockHessian realDirections imagDirections u y‖ ≤ C*‖x-y‖^alpha := by
  classical
  obtain ⟨t,D0,hD0,theta,K,htheta,htheta1,htheta8,hK,hstep⟩ :=
    exists_variable_density_hessian_oscillation_step_two M D P L Csrc hD hP hL hCsrc
  obtain ⟨alpha,halpha,halpha1,hdecay⟩ := exists_exponent_for_eighth_decay htheta htheta1
  let S : ℝ := ∑ z : t, realMatrixQuadraticWeight z.1
  let T : ℝ := ∑ z : t, hessianCorrectionCoefficientTwo Csrc z.1
  have hS : 0 ≤ S := Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun z _ => hessianCorrectionCoefficientTwo_nonneg hCsrc z.1)
  let B : ℝ := 2*M*S+P*T
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let A : ℝ := K/(theta-1/8)
  have hA : 0 ≤ A := div_nonneg hK (sub_pos.mpr htheta8).le
  let H : ℝ := D0*(B+A/8)+K/8
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let C : ℝ := max 1 (max (64*H) (16*M))
  have hC : 0 < C := zero_lt_one.trans_le (le_max_left _ _)
  have hCnear : 64*H ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCfar : 16*M ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro u f hu hf hdet hpos hfb hentry hup hfp hsource x hx y hy
  let U : Set E := ball 0 (3/2 : ℝ)
  have hsmall : ball (0 : E) 1 ⊆ U := ball_subset_ball (by norm_num)
  have hnorm (z : E) (hz : z ∈ U) :
      ‖realBlockHessian realDirections imagDirections u z‖ ≤ M :=
    realBlockHessian_norm_le_of_euclidean_bound hM (hentry z hz)
  have hclosed (r : ℝ) (hr : r ≤ 1/8) : closedBall x (2*r) ⊆ U := by
    intro z hz
    have hx' : dist x (0 : E) < 1 := hx
    have hz' : dist z x ≤ 2*r := hz
    change dist z (0 : E) < 3/2
    have ht := dist_triangle z x (0 : E)
    linarith
  have hlocal (r : ℝ) (hr : 0 < r) (hrsmall : r ≤ 1/8) :=
    hstep U isOpen_ball u f hu hf hdet hpos hfb hentry hup hfp hsource x r hr (hclosed r hrsmall)
  let F : ℝ → ℝ := correctedHessianOscillationTwo t Csrc u x
  have hiter : ∀ k : ℕ, F ((1/8 : ℝ)*(1/8 : ℝ)^k) ≤
      theta^k*(F (1/8)+A/8) := by
    simpa only [A,F,div_eq_mul_inv,one_mul] using
      (eighth_radius_linear_error_iterate htheta8 hK (by norm_num : 0 < (1/8 : ℝ))
        (fun r hr hrsmall => (hlocal r hr hrsmall).1))
  have hbase : F (1/8) ≤ B := by
    have hsub : closedBall x (1/8 : ℝ) ⊆ U :=
      (closedBall_subset_closedBall (by norm_num : (1/8 : ℝ) ≤ 2*(1/8))).trans (hclosed (1/8) le_rfl)
    have hh := correctedHessianOscillationTwo_le hu t hCsrc (by norm_num : 0 ≤ (1/8 : ℝ)) hM hP
      (fun z hz => hnorm z (hsub hz)) (fun z hz w hw => hup z (hsub hz) w (hsub hw))
    change F (1/8) ≤ 2*M*S+2*P*(1/8)*T at hh
    dsimp only [B]
    nlinarith only [hh,mul_nonneg hP hT]
  by_cases hxy : x = y
  · subst y
    simp only [sub_self,norm_zero,Real.zero_rpow halpha.ne',mul_zero,le_refl]
  have hdelta : 0 < ‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  by_cases hnear : ‖x-y‖ ≤ 1/8
  · obtain ⟨k,hkdist,hkpow⟩ := exists_eighth_scale_power_bound htheta.le halpha.le halpha1.le hdecay hdelta hnear
    let r : ℝ := (1/8 : ℝ)*(1/8 : ℝ)^k
    have hr : 0 < r := by dsimp only [r]; positivity
    have hrsmall : r ≤ 1/8 := by
      exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (by norm_num) (by norm_num) :
        (1/8 : ℝ)^k ≤ 1) (by norm_num : 0 ≤ (1/8 : ℝ))).trans_eq (mul_one _)
    have hyball : y ∈ closedBall x r := by
      simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hkdist
    have hpair := (hlocal r hr hrsmall).2 x (mem_closedBall_self hr.le) y hyball
    have hbasecor : F (1/8)+A/8 ≤ B+A/8 := add_le_add hbase le_rfl
    have hiterB : F r ≤ theta^k*(B+A/8) :=
      (hiter k).trans (mul_le_mul_of_nonneg_left hbasecor (pow_nonneg htheta.le _))
    have hrpow : r ≤ (1/8 : ℝ)*theta^k :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) htheta8.le k) (by norm_num)
    have herr : K*r ≤ (K/8)*theta^k := by
      nlinarith only [mul_le_mul_of_nonneg_left hrpow hK]
    have hfinal : ‖realBlockHessian realDirections imagDirections u x-
        realBlockHessian realDirections imagDirections u y‖ ≤ theta^k*H := by
      have hh := mul_le_mul_of_nonneg_left hiterB hD0.le
      dsimp only [H]
      nlinarith only [hpair,hh,herr]
    calc
      _ ≤ theta^k*H := hfinal
      _ ≤ (64*‖x-y‖^alpha)*H := mul_le_mul_of_nonneg_right hkpow hH
      _ = (64*H)*‖x-y‖^alpha := by ring
      _ ≤ C*‖x-y‖^alpha := mul_le_mul_of_nonneg_right hCnear (Real.rpow_nonneg hdelta.le _)
  · have hdlarge : (1/8 : ℝ) ≤ ‖x-y‖ := (lt_of_not_ge hnear).le
    have hpow : (1/8 : ℝ) ≤ ‖x-y‖^alpha :=
      (Real.self_le_rpow_of_le_one (by norm_num : 0 ≤ (1/8 : ℝ)) (by norm_num) halpha1.le).trans
        (Real.rpow_le_rpow (by norm_num) hdlarge halpha.le)
    calc
      _ ≤ ‖realBlockHessian realDirections imagDirections u x‖+
          ‖realBlockHessian realDirections imagDirections u y‖ := norm_sub_le _ _
      _ ≤ 2*M := by linarith [hnorm x (hsmall hx),hnorm y (hsmall hy)]
      _ ≤ (16*M)*‖x-y‖^alpha := by nlinarith
      _ ≤ C*‖x-y‖^alpha := mul_le_mul_of_nonneg_right hCfar (Real.rpow_nonneg hdelta.le _)

end PowerConvexity
