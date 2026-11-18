import PowerConvexity.Algebra.SmallParaboloidContactTwo
import PowerConvexity.Calculus.RealHessianBlockNormTwo
import PowerConvexity.Calculus.TranslatedBallBarrierTwo
import PowerConvexity.Calculus.RealHessianRules

/-! # Actual real Hessian bounds at small paraboloid contacts.
The equation is the actual determinant-one equation for the deviation
from the quadratic ball potential. The estimates below are at contact
points; no interior estimate away from the contact set is asserted.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Matrix
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus CHS.Analysis CHS.Algebra
local notation "E" => DeGiorgi.AmbientSpace (2+2)
local notation "J" => Fin 2 ⊕ Fin 2

theorem translated_paraboloid_realBlockHessian_two (a : ℝ) (c x : E) :
    realBlockHessian realDirections imagDirections
      (translatedBallPotential (a/2) 0 c) x =
        a • (1 : Matrix J J ℝ) := by
  ext i j
  simp only [realBlockHessian,translatedBallPotential_realHessian,
    blockDirection_eq_single,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  rw [orthonormal_iff_ite.mp (EuclideanSpace.orthonormal_single (𝕜 := ℝ))]
  simp only [Equiv.apply_eq_iff_eq]
  ring

theorem actual_small_semiconvex_hessian_bound_two
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : ∀ v : E, -(a*‖v‖^2) ≤ realHessian w x v v) :
    ‖realHessian w x‖ ≤ 144*a := by
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
      realBlockHessian realDirections imagDirections w x+a • (1 : Matrix J J ℝ) := by
    have hqm := translated_paraboloid_realBlockHessian_two a (0 : E) x
    ext i j
    have hqi := congrFun (congrFun hqm i) j
    simpa only [realBlockHessian,realHessian_add hw hq,ContinuousLinearMap.add_apply,
      Matrix.add_apply,q] using congrArg (fun z =>
        realBlockHessian realDirections imagDirections w x i j+z) hqi
  rw [he] at hp
  have hd : (1+complexProjection (realBlockHessian realDirections imagDirections w x)).det = 1 := by
    rwa [complexProjection_realBlockHessian hw]
  have hb := small_paraboloid_lower_contact_entry_bound_two ha ha1 hp hd
  have hh := realHessian_norm_le_sixteen_entry_bound_two (by positivity : 0 ≤ 9*a)
    (fun i j => by
      simpa only [realBlockHessian,blockDirection_eq_single,Equiv.apply_symm_apply,
        euclideanHessian] using hb (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
  convert hh using 1 <;> ring

theorem actual_small_semiconcave_hessian_bound_two
    {w : E → ℝ} {x : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha : 0 ≤ a)
    (hpsh : (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : ∀ v : E, realHessian w x v v ≤ a*‖v‖^2) :
    ‖realHessian w x‖ ≤ 80*a := by
  let q : E → ℝ := translatedBallPotential (a/2) 0 0
  have hq : ContDiffAt ℝ 2 q x := (translatedBallPotential_contDiff (a/2) 0 0 2).contDiffAt
  have hp := realBlockHessian_posSemidef_of_quadratic_nonneg (hq.sub hw)
    realDirections imagDirections (fun v => by
      rw [realHessian_sub_at hq hw]
      change 0 ≤ realHessian q x v v-realHessian w x v v
      rw [show realHessian q x v v = a*‖v‖^2 by
        dsimp only [q]
        rw [translatedBallPotential_realHessian,real_inner_self_eq_norm_sq]
        ring]
      linarith only [hcontact v])
  have he : realBlockHessian realDirections imagDirections (fun y => q y-w y) x =
      a • (1 : Matrix J J ℝ)-realBlockHessian realDirections imagDirections w x := by
    have hqm := translated_paraboloid_realBlockHessian_two a (0 : E) x
    ext i j
    have hqi := congrFun (congrFun hqm i) j
    simpa only [realBlockHessian,realHessian_sub_at hq hw,ContinuousLinearMap.sub_apply,
      Matrix.sub_apply,q] using congrArg (fun z =>
        z-realBlockHessian realDirections imagDirections w x i j) hqi
  rw [he] at hp
  have hd : (1+complexProjection (realBlockHessian realDirections imagDirections w x)).det = 1 := by
    rwa [complexProjection_realBlockHessian hw]
  have hpp : (1+complexProjection (realBlockHessian realDirections imagDirections w x)).PosSemidef := by
    rwa [complexProjection_realBlockHessian hw]
  have hb := small_paraboloid_upper_contact_entry_bound_two ha hp hpp hd
  have hh := realHessian_norm_le_sixteen_entry_bound_two (by positivity : 0 ≤ 5*a)
    (fun i j => by
      simpa only [realBlockHessian,blockDirection_eq_single,Equiv.apply_symm_apply,
        euclideanHessian] using hb (finSumFinEquiv.symm i) (finSumFinEquiv.symm j))
  convert hh using 1 <;> ring

theorem actual_small_lower_paraboloid_contact_hessian_bound_two
    {w : E → ℝ} {x c : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : IsLocalMin (fun y => w y+translatedBallPotential (a/2) 0 c y) x) :
    ‖realHessian w x‖ ≤ 144*a := by
  apply actual_small_semiconvex_hessian_bound_two hw ha ha1 hdet
  intro v
  have hq := (translatedBallPotential_contDiff (a/2) 0 c 2).contDiffAt (x := x)
  have hh := realHessian_nonneg_of_isLocalMin (hw.add hq) hcontact v
  rw [realHessian_add hw hq] at hh
  change 0 ≤ realHessian w x v v+realHessian (translatedBallPotential (a/2) 0 c) x v v at hh
  rw [translatedBallPotential_realHessian,real_inner_self_eq_norm_sq] at hh
  linarith only [hh]

theorem actual_small_upper_paraboloid_contact_hessian_bound_two
    {w : E → ℝ} {x c : E} (hw : ContDiffAt ℝ 2 w x)
    {a : ℝ} (ha : 0 ≤ a)
    (hpsh : (1+complexHessian realDirections imagDirections w x).PosSemidef)
    (hdet : (1+complexHessian realDirections imagDirections w x).det = 1)
    (hcontact : IsLocalMax (fun y => w y-translatedBallPotential (a/2) 0 c y) x) :
    ‖realHessian w x‖ ≤ 80*a := by
  apply actual_small_semiconcave_hessian_bound_two hw ha hpsh hdet
  intro v
  have hq := (translatedBallPotential_contDiff (a/2) 0 c 2).contDiffAt (x := x)
  have hh := realHessian_nonpos_of_isLocalMax (hw.sub hq) hcontact v
  rw [realHessian_sub_at hw hq] at hh
  change realHessian w x v v-realHessian (translatedBallPotential (a/2) 0 c) x v v ≤ 0 at hh
  rw [translatedBallPotential_realHessian,real_inner_self_eq_norm_sq] at hh
  linarith only [hh]

end PowerConvexity
