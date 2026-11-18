import PowerConvexity.Calculus.CMADeviationContactsTwo

/-! # Strict trace barriers cannot touch the actual small equation from below.
This is the pointwise comparison step for contact growth. It requires only
the actual determinant equation and a small lower quadratic bound at the
possible contact point. It does not assume global uniform ellipticity.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder BigOperators
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2
local notation "V" => Matrix J J ℝ
local notation "W" => Matrix (Fin 2) (Fin 2) ℂ

theorem small_paraboloid_lower_contact_trace_bound_two
    {H : V} {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hcontact : (H+a • (1 : V)).PosSemidef)
    (hdet : (1+complexProjection H).det = 1) : H.trace ≤ 4*a := by
  have hh := complexProjection_posSemidef hcontact
  have he : complexProjection (H+a • (1 : V)) =
      (1+complexProjection H)-((1-a/2 : ℝ) : ℂ) • (1 : W) := by
    rw [complexProjection_add_two,complexProjection_smul,complexProjection_one_two,smul_smul]
    ext i j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,
      Complex.real_smul,smul_eq_mul,Complex.ofReal_mul,Complex.ofReal_div,
      Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_ofNat]
    ring
  rw [he] at hh
  have ht := det_one_trace_upper_of_small_scalar_lower_two hdet ha ha1 hh
  norm_num [Matrix.trace_add,Matrix.trace_one] at ht
  have hp := four_complexProjection_trace_re H
  linarith only [ht,hp]

theorem realBlockHessian_scalar_lower_posSemidef_two
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x) {a : ℝ}
    (hcontact : ∀ v : E, -(a*‖v‖^2) ≤ realHessian w x v v) :
    (realBlockHessian realDirections imagDirections w x+a • (1 : V)).PosSemidef := by
  let q : E → ℝ := translatedBallPotential (a/2) 0 0
  have hq : ContDiffAt ℝ 2 q x := (translatedBallPotential_contDiff (a/2) 0 0 2).contDiffAt
  have hp := realBlockHessian_posSemidef_of_quadratic_nonneg (hw.add hq)
    realDirections imagDirections (fun v => by
      rw [realHessian_add hw hq]
      change 0 ≤ realHessian w x v v+realHessian q x v v
      rw [show realHessian q x v v = a*‖v‖^2 by
        dsimp only [q]
        rw [translatedBallPotential_realHessian,real_inner_self_eq_norm_sq]
        ring]
      linarith only [hcontact v])
  have he : realBlockHessian realDirections imagDirections (fun y => w y+q y) x =
      realBlockHessian realDirections imagDirections w x+a • (1 : V) := by
    have hqm := translated_paraboloid_realBlockHessian_two a (0 : E) x
    ext i j
    have hqi := congrFun (congrFun hqm i) j
    simpa only [realBlockHessian,realHessian_add hw hq,ContinuousLinearMap.add_apply,
      Matrix.add_apply,q] using congrArg (fun z =>
        realBlockHessian realDirections imagDirections w x i j+z) hqi
  rwa [he] at hp

theorem actual_small_semiconvex_trace_bound_two
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : ∀ v : E, -(a*‖v‖^2) ≤ realHessian w x v v) :
    (realBlockHessian realDirections imagDirections w x).trace ≤ 4*a := by
  apply small_paraboloid_lower_contact_trace_bound_two ha ha1
    (realBlockHessian_scalar_lower_posSemidef_two hw hcontact)
  rwa [complexProjection_realBlockHessian hw]

theorem actual_small_strict_trace_barrier_no_lower_contact_two
    {w p : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x) (hp : ContDiffAt ℝ 2 p x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hlower : ∀ v : E, -(a*‖v‖^2) ≤ realHessian p x v v)
    (htrace : 4*a < (realBlockHessian realDirections imagDirections p x).trace) :
    ¬ IsLocalMin (fun y => w y-p y) x := by
  intro hm
  have horder := realHessian_le_of_isLocalMin_sub hw hp hm
  have ht := actual_small_semiconvex_trace_bound_two hw ha ha1 hdet
    (fun v => (hlower v).trans (horder v))
  have htr : (realBlockHessian realDirections imagDirections p x).trace ≤
      (realBlockHessian realDirections imagDirections w x).trace := by
    apply Finset.sum_le_sum
    intro i _hi
    exact horder (Sum.elim realDirections imagDirections i)
  linarith only [htrace,htr,ht]

end PowerConvexity
