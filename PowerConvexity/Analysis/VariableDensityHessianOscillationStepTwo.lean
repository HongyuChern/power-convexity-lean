import PowerConvexity.Algebra.CorrectedDirectionalDeficitsTwo
import PowerConvexity.Analysis.CorrectedHessianObservablesTwo
import PowerConvexity.Analysis.VariableDensityCofactorEllipticity
import PowerConvexity.Analysis.FiniteOscillationWithError
import PowerConvexity.Analysis.OscillationLinearErrorIteration

/-! # A true one-step oscillation estimate for the variable-density CMA.
The corrected observables and the same cofactor field are used throughout.
Both density and potential variations appear in the radius error.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
noncomputable section
open Set Matrix Metric
open scoped BigOperators ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra DeGiorgi
local notation "E" => AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

theorem exists_variable_density_hessian_oscillation_step_two
    (M D P L Csrc : ℝ) (hD : 1 ≤ D) (hP : 0 ≤ P) (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc) :
    ∃ t : Finset (J → ℝ), ∃ D0 : ℝ, 0 < D0 ∧ ∃ theta K : ℝ,
      0 < theta ∧ theta < 1 ∧ (1/8 : ℝ) < theta ∧ 0 ≤ K ∧
      ∀ U : Set E, IsOpen U → ∀ u f : E → ℝ,
      ContDiff ℝ 4 u → ContDiffOn ℝ 2 f U →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ U, (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ U, 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ U, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      (∀ x ∈ U, ∀ y ∈ U, |u x-u y| ≤ P*‖x-y‖) →
      (∀ x ∈ U, ∀ y ∈ U, |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ U, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x₀ : E, ∀ R : ℝ, 0 < R → closedBall x₀ (2*R) ⊆ U →
        correctedHessianOscillationTwo t Csrc u x₀ (R/8) ≤
          theta*correctedHessianOscillationTwo t Csrc u x₀ R+K*R ∧
        ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ R,
          ‖realBlockHessian realDirections imagDirections u x-
            realBlockHessian realDirections imagDirections u y‖ ≤
              D0*correctedHessianOscillationTwo t Csrc u x₀ R+K*R := by
  classical
  have hd : 2 < ((2+2 : ℕ) : ℝ) := by norm_num
  obtain ⟨t,D0,hD0,hdetect⟩ := exists_finite_directions_detecting_elliptic_half_cone
    (inverseComplexDetLowerFamily_compact (n := 2) M)
    (fun _ h => inverseComplexDetLowerFamily_posDef h)
  let k := hessianCorrectionCoefficientTwo Csrc
  let S : ℝ := ∑ z ∈ t, realMatrixQuadraticWeight z
  let T : ℝ := ∑ z ∈ t, k z
  let W : ℝ := 1+S
  let Q : ℝ := 1+T
  have hk (z : J → ℝ) : 0 ≤ k z := hessianCorrectionCoefficientTwo_nonneg hCsrc z
  have hS : 0 ≤ S := Finset.sum_nonneg (fun z _ => sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun z _ => hk z)
  have hW : 0 ≤ W := by dsimp only [W]; linarith
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith
  have hzW (z : t) : realMatrixQuadraticWeight z.1 ≤ W := by
    have hh := Finset.single_le_sum (s := t) (fun y _ => sq_nonneg (∑ j, |y j|)) z.2
    change realMatrixQuadraticWeight z.1 ≤ S at hh
    dsimp only [W]
    linarith
  have hzQ (z : t) : k z.1 ≤ Q := by
    have hh := Finset.single_le_sum (s := t) (fun y _ => hk y) z.2
    change k z.1 ≤ T at hh
    dsimp only [Q]
    linarith
  let Kmat : ℝ := 2*D0*P*T+4*D*L*(D0*S+1)
  let Kpair : ℝ := W*Kmat+2*P*Q
  let K : ℝ := Kmat+2*(Fintype.card t : ℝ)*Kpair
  have hKm : 0 ≤ Kmat := by dsimp only [Kmat]; positivity
  have hKp : 0 ≤ Kpair := by dsimp only [Kpair]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hKmK : Kmat ≤ K := by
    dsimp only [K]
    exact le_add_of_nonneg_right (by positivity)
  have hKpK : 2*(Fintype.card t : ℝ)*Kpair ≤ K := by dsimp only [K]; linarith
  obtain ⟨c,hc,Lambda,hLambda,hcoeff⟩ := exists_uniform_variable_density_cofactor_coefficients (n := 2) M
  let theta := finiteOscillationFactor (2+2) hd Lambda (W*D0) (Fintype.card t)
  have htheta := finiteOscillationFactor_pos_lt_one hd Lambda (W*D0) (Fintype.card t)
  refine ⟨t,D0,hD0,theta,K,htheta.1,htheta.2,
    finiteOscillationFactor_one_eighth_lt hd Lambda (W*D0) (Fintype.card t),hK,?_⟩
  intro U hU u f hu hf hdet hA hfb hentry hup hfp hsource x₀ R hR hclosed
  have hKU : closedBall x₀ R ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hclosed
  have hdetlo (x : E) (hx : x ∈ U) : 1 ≤ (complexHessian realDirections imagDirections u x).det.re := by
    rw [hdet x hx,Complex.ofReal_re]
    exact (hfb x hx).1
  obtain ⟨B,hBLambda,hB⟩ := hcoeff U hU u hu.contDiffOn hdetlo hA hentry
  have hweight (x : E) (hx : x ∈ U) :
      (complexHessian realDirections imagDirections u x)⁻¹ ∈ inverseComplexDetLowerFamily 2 M :=
    mem_image_of_mem _ (complexHessian_mem_complexDetLowerFamily
      (hu.of_le (by norm_num)).contDiffAt (hA x hx) (hdetlo x hx) (hentry x hx))
  let F : t → E → ℝ := fun z => correctedHessianObservableTwo Csrc u z.1
  let N : (J → ℝ) → ℝ := fun z => compactSup (correctedHessianObservableTwo Csrc u z) (closedBall x₀ R)
  have hF (z : t) : Continuous (F z) := correctedHessianObservableTwo_continuous Csrc hu z.1
  have hupper (z : J → ℝ) (x : E) (hx : x ∈ closedBall x₀ R) :
      correctedHessianObservableTwo Csrc u z x ≤ N z :=
    le_compactSup (isCompact_closedBall _ _) (correctedHessianObservableTwo_continuous Csrc hu z).continuousOn hx
  have hdist (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) : ‖x-y‖ ≤ 2*R := by
    have hh := dist_triangle x x₀ y
    have hx' : dist x x₀ ≤ R := hx
    have hy' : dist x₀ y ≤ R := by simpa only [mem_closedBall,dist_comm] using hy
    rw [dist_eq_norm x y] at hh
    linarith
  have hpot (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) :
      |u x-u y| ≤ 2*P*R :=
    (hup x (hKU hx) y (hKU hy)).trans (by nlinarith only [mul_le_mul_of_nonneg_left (hdist x hx y hy) hP])
  have hden (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) :
      |f x-f y| ≤ 2*L*R :=
    (hfp x (hKU hx) y (hKU hy)).trans (by nlinarith only [mul_le_mul_of_nonneg_left (hdist x hx y hy) hL])
  have hnorm (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) :
      ‖realBlockHessian realDirections imagDirections u x-realBlockHessian realDirections imagDirections u y‖ ≤
        D0*(∑ z : t, (N z.1-F z y))+Kmat*R := by
    have hh := norm_sub_le_corrected_directional_deficits_two
      (S := inverseComplexDetLowerFamily 2 M) (t := t) (C := D0) (D := D)
      (Erho := 2*L*R) (Ep := 2*P*R) (H := realBlockHessian realDirections imagDirections u)
      (p := u) (k := k) hD0.le hD (by positivity) (by positivity) hdetect
      (fun z _ => hk z)
      (fun x _ => realBlockHessian_isHermitian (hu.of_le (by norm_num)).contDiffAt realDirections imagDirections)
      (fun x hx => by rw [complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt]; exact hA x (hKU hx))
      (fun x hx => by rw [complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt]; exact hdetlo x (hKU hx))
      (fun x hx => by rw [complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt,hdet x (hKU hx),Complex.ofReal_re]; exact (hfb x (hKU hx)).2)
      (fun x hx => by rw [complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt]; exact hweight x (hKU hx))
      (M := N) (fun z _ x hx => hupper z x hx) hx hy
      (by rw [complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt,
        complexProjection_realBlockHessian (hu.of_le (by norm_num)).contDiffAt,
        hdet x (hKU hx),hdet y (hKU hy),Complex.ofReal_re,Complex.ofReal_re]; exact hden x hx y hy)
      (fun z hz => hpot z hz y hy)
    rw [Finset.sum_coe_sort t (fun z => N z-correctedHessianObservableTwo Csrc u z y)]
    dsimp only [F,correctedHessianObservableTwo,hessianObservable] at ⊢
    dsimp only [Kmat,S,T] at ⊢
    change _ ≤ _ at hh
    nlinarith only [hh]
  have hpair (z : t) (x : E) (hx : x ∈ closedBall x₀ R) (y : E) (hy : y ∈ closedBall x₀ R) :
      |F z x-F z y| ≤ (W*D0)*(∑ j : t, (N j.1-F j y))+Kpair*R := by
    have he : F z x-F z y =
        realMatrixQuadratic (realBlockHessian realDirections imagDirections u x-
          realBlockHessian realDirections imagDirections u y) z.1+k z.1*(u x-u y) := by
      dsimp only [F,correctedHessianObservableTwo,hessianObservable,k]
      rw [realMatrixQuadratic_sub]
      ring
    rw [he]
    have hquad := abs_realMatrixQuadratic_le
      (realBlockHessian realDirections imagDirections u x-realBlockHessian realDirections imagDirections u y) z.1
    have hpotz : |k z.1*(u x-u y)| ≤ Q*(2*P*R) := by
      rw [abs_mul,abs_of_nonneg (hk z.1)]
      exact (mul_le_mul_of_nonneg_left (hpot x hx y hy) (hk z.1)).trans
        (mul_le_mul_of_nonneg_right (hzQ z) (by positivity))
    have hquadW := (mul_le_mul_of_nonneg_right (hzW z)
      (norm_nonneg (realBlockHessian realDirections imagDirections u x-realBlockHessian realDirections imagDirections u y)))
    have hnormW := mul_le_mul_of_nonneg_left (hnorm x hx y hy) hW
    have htri := abs_add_le
      (realMatrixQuadratic (realBlockHessian realDirections imagDirections u x-
        realBlockHessian realDirections imagDirections u y) z.1) (k z.1*(u x-u y))
    dsimp only [Kpair]
    nlinarith only [htri,hquad,hquadW,hnormW,hpotz]
  constructor
  · have hsub : ball x₀ R ⊆ U := ball_subset_closedBall.trans hKU
    let A := B.restrict hsub
    have hsuper (z : t) : IsSupersolution A.1 (fun y => N z.1-F z y) :=
      correctedHessianObservableTwo_deficit_supersolution hU hu.contDiffOn hf hdet
        (fun x hx => zero_lt_one.trans_le (hfb x hx).1) hA hc B hB hsource z.1 (N z.1)
        hR (by linarith : R < 2*R) hclosed
    have hh := finite_supersolution_oscillation_contraction_with_error hd hR
      (mul_nonneg hW hD0.le) (show 0 ≤ Kpair*R by positivity) A F hF hsuper hpair
    have hALambda : A.1.Λ = Lambda := hBLambda
    rw [hALambda] at hh
    change correctedHessianOscillationTwo t Csrc u x₀ (R/8) ≤
      theta*correctedHessianOscillationTwo t Csrc u x₀ R+2*(Fintype.card t : ℝ)*(Kpair*R) at hh
    have herr := mul_le_mul_of_nonneg_right hKpK hR.le
    nlinarith only [hh,herr]
  · intro x hx y hy
    have hsum : (∑ z : t, (N z.1-F z y)) ≤ correctedHessianOscillationTwo t Csrc u x₀ R := by
      apply Finset.sum_le_sum
      intro z _
      exact sub_le_sub_left (compactInf_le (isCompact_closedBall _ _) (hF z).continuousOn hy) _
    have hh := hnorm x hx y hy
    have hm := mul_le_mul_of_nonneg_left hsum hD0.le
    have herr := mul_le_mul_of_nonneg_right hKmK hR.le
    linarith

end PowerConvexity
