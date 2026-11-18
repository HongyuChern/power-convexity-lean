import PowerConvexity.Analysis.VariableDensityHessianHolderGlobalTwo
import CHS.Analysis.HessianHolder

/-! # Local C4 potentials, without an assumed global representative.
A constructed cutoff has the same actual derivatives on the smaller ball.
The actual density is unchanged; all source and Lipschitz inputs are local.
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

theorem exists_variable_density_hessian_holder_local_two
    {M D P L Csrc : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ u f : E → ℝ, ContDiffOn ℝ 4 u (ball (0 : E) 2) →
      ContDiffOn ℝ 2 f (ball (0 : E) 2) →
      (∀ x ∈ ball (0 : E) 2,
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball (0 : E) 2,
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball (0 : E) 2, 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball (0 : E) 2, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
        |u x-u y| ≤ P*‖x-y‖) →
      (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
        |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball (0 : E) 2, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
        ‖realBlockHessian realDirections imagDirections u x-
          realBlockHessian realDirections imagDirections u y‖ ≤ C*‖x-y‖^alpha := by
  obtain ⟨alpha,C,halpha,halpha1,hC,hglobal⟩ :=
    exists_variable_density_hessian_holder_global_two hM hD hP hL hCsrc
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro u f hu hf hdet hA hfb hentry hup hfp hsource
  let v : E → ℝ := cutoffRepresentative 0 (3/2) (7/4) u
  have hv : ContDiff ℝ 4 v := cutoffRepresentative_contDiff (k := 4) isOpen_ball
    (by norm_num : (0 : ℝ) < 3/2) (by norm_num : (3/2 : ℝ) < 7/4)
    (closedBall_subset_ball (by norm_num : (7/4 : ℝ) < 2)) hu
  have hsmall : ball (0 : E) (3/2 : ℝ) ⊆ ball (0 : E) 2 := ball_subset_ball (by norm_num)
  have heq (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ)) : v =ᶠ[nhds x] u :=
    cutoffRepresentative_eventuallyEq (by norm_num : (3/2 : ℝ) < 7/4) u hx
  have hH (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ)) : realHessian v x = realHessian u x :=
    realHessian_eq_of_eventuallyEq (heq x hx)
  have hcomplex (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ)) :
      complexHessian realDirections imagDirections v x =
        complexHessian realDirections imagDirections u x :=
    complexHessian_eq_of_eventuallyEq realDirections imagDirections (heq x hx)
      (hv.of_le (by norm_num)).contDiffAt
      ((hu.contDiffAt (isOpen_ball.mem_nhds (hsmall hx))).of_le (by norm_num))
  have hvdet (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ)) :
      (complexHessian realDirections imagDirections v x).det = (f x : ℂ) := by
    rw [hcomplex x hx]
    exact hdet x (hsmall hx)
  have hvpos (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ)) :
      (complexHessian realDirections imagDirections v x).PosDef := by
    rw [hcomplex x hx]
    exact hA x (hsmall hx)
  have hventry (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ)) (i j : Fin (2+2)) :
      |euclideanHessian v x i j| ≤ M := by
    simp only [euclideanHessian,hH x hx]
    exact hentry x (hsmall hx) i j
  have hvLip (x : E) (hx : x ∈ ball (0 : E) (3/2 : ℝ))
      (y : E) (hy : y ∈ ball (0 : E) (3/2 : ℝ)) : |v x-v y| ≤ P*‖x-y‖ := by
    rw [(heq x hx).eq_of_nhds,(heq y hy).eq_of_nhds]
    exact hup x (hsmall hx) y (hsmall hy)
  intro x hx y hy
  have hinner : ball (0 : E) 1 ⊆ ball (0 : E) (3/2 : ℝ) := ball_subset_ball (by norm_num)
  have hh := hglobal v f hv (hf.mono hsmall) hvdet hvpos
    (fun z hz => hfb z (hsmall hz)) hventry hvLip
    (fun z hz w hw => hfp z (hsmall hz) w (hsmall hw))
    (fun z hz => hsource z (hsmall hz)) x hx y hy
  rwa [realBlockHessian_eq_of_eventuallyEq realDirections imagDirections (heq x (hinner hx)),
    realBlockHessian_eq_of_eventuallyEq realDirections imagDirections (heq y (hinner hy))] at hh

theorem exists_variable_density_hessian_holder_local_entry_two
    {M D P L Csrc : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hP : 0 ≤ P) (hL : 0 ≤ L) (hCsrc : 0 ≤ Csrc) :
    ∃ alpha C : ℝ, 0 < alpha ∧ alpha < 1 ∧ 0 < C ∧
      ∀ u f : E → ℝ, ContDiffOn ℝ 4 u (ball (0 : E) 2) →
      ContDiffOn ℝ 2 f (ball (0 : E) 2) →
      (∀ x ∈ ball (0 : E) 2,
        (complexHessian realDirections imagDirections u x).det = (f x : ℂ)) →
      (∀ x ∈ ball (0 : E) 2,
        (complexHessian realDirections imagDirections u x).PosDef) →
      (∀ x ∈ ball (0 : E) 2, 1 ≤ f x ∧ f x ≤ D) →
      (∀ x ∈ ball (0 : E) 2, ∀ i j, |euclideanHessian u x i j| ≤ M) →
      (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
        |u x-u y| ≤ P*‖x-y‖) →
      (∀ x ∈ ball (0 : E) 2, ∀ y ∈ ball (0 : E) 2,
        |f x-f y| ≤ L*‖x-y‖) →
      (∀ x ∈ ball (0 : E) 2, ∀ v : E,
        -(Csrc*‖v‖^2) ≤ (realHessian f x v v*f x-(fderiv ℝ f x v)^2)/(f x)^2) →
      ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1, ∀ i j,
        |euclideanHessian u x i j-euclideanHessian u y i j| ≤ C*‖x-y‖^alpha := by
  obtain ⟨alpha,C,halpha,halpha1,hC,hbound⟩ :=
    exists_variable_density_hessian_holder_local_two hM hD hP hL hCsrc
  refine ⟨alpha,C,halpha,halpha1,hC,?_⟩
  intro u f hu hf hdet hA hfb hentry hup hfp hsource x hx y hy i j
  exact (abs_euclideanHessian_sub_le_block_norm u x y i j).trans
    (hbound u f hu hf hdet hA hfb hentry hup hfp hsource x hx y hy)

end PowerConvexity
