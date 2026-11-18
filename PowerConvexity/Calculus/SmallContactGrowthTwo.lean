import PowerConvexity.Calculus.ContactOpeningLocalizationTwo
import PowerConvexity.Calculus.SmallContactPenetrationTwo
import CHS.Calculus.PotentialConstants

/-! # Actual contact growth on a fixed compact convex domain.
Starting from one global lower contact, the new contacts have a fixed
larger opening. Their genuine vertices stay in the same convex domain.
The measure estimate uses the original solution's actual vertex map.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
open Set Metric Filter InnerProductSpace MeasureTheory
open scoped ContDiff Topology ENNReal
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

theorem exists_universal_small_contact_growth_two :
    ∃ M K : ℝ, 2 ≤ M ∧ 0 < K ∧
      ∀ (w : E → ℝ) (D : Set E) (x0 y1 x1 : E) (a r : ℝ),
        IsCompact D → Convex ℝ D →
        ContinuousOn w D → ContDiffOn ℝ 2 w (interior D) →
        (∀ x ∈ interior D,
          (1+complexHessian realDirections imagDirections w x).det = 1) →
        0 < a → M*a ≤ 1 → 0 < r →
        closedBall x0 r ⊆ interior D → y1 ∈ D → x1 ∈ ball x0 r →
        IsMinOn (fun x => w x+translatedBallPotential (a/2) 0 y1 x) D x1 →
        ∃ z ∈ ball x0 (r/16), ∃ S : Set E,
          IsCompact S ∧ S ⊆ ball x0 (r/8) ∧
          S ⊆ lowerParaboloidContactsTwo (M*a) w D D ∧
          volume ((fun y : E => M⁻¹ • (y1+(M-1) • y)) '' closedBall z (r/64)) ≤
            ENNReal.ofReal K*volume S := by
  obtain ⟨K,hK,hmeasure⟩ := exists_universal_small_lower_contact_image_measure_bound_two
  let C : ℝ := Real.exp 4096
  let M : ℝ := 1+8192*(C+1)
  have hC : 0 < C := Real.exp_pos _
  have hM1 : 1 < M := by dsimp only [M]; linarith only [hC]
  have hM2 : 2 ≤ M := by dsimp only [M]; linarith only [hC]
  have hM : 0 < M := lt_trans zero_lt_one hM1
  have hMcoef : M-1 = 8192*(C+1) := by dsimp only [M]; ring
  refine ⟨M,K,hM2,hK,?_⟩
  intro w D x0 y1 x1 a r hD hconv hwc hw hdet ha hMa hr hball hy1 hx1 hm
  have hCD : closedBall x0 r ⊆ D := hball.trans interior_subset
  have hBD : ball x0 r ⊆ interior D := ball_subset_closedBall.trans hball
  have hsmall : a ≤ (1+Real.exp 4096)⁻¹ := by
    have hCM : 1+C ≤ M := by dsimp only [M]; linarith only [hC]
    have hh : a*(1+C) ≤ 1 := by
      calc
        _ ≤ a*M := mul_le_mul_of_nonneg_left hCM ha.le
        _ = M*a := mul_comm _ _
        _ ≤ 1 := hMa
    simpa only [C,one_div] using (le_div_iff₀ (by positivity : 0 < 1+C)).mpr hh
  let m : ℝ := w x1+translatedBallPotential (a/2) 0 y1 x1
  let g : E → ℝ := fun x => w x-m
  let v : E → ℝ := fun x => w x+translatedBallPotential (a/2) 0 y1 x-m
  have hgc : ContinuousOn g (closedBall x0 r) := (hwc.mono hCD).sub continuousOn_const
  have hg : ContDiffOn ℝ 2 g (ball x0 r) := (hw.mono hBD).sub contDiffOn_const
  have hgdet (x : E) (hx : x ∈ ball x0 r) :
      (1+complexHessian realDirections imagDirections g x).det = 1 := by
    dsimp only [g]
    simp only [sub_eq_add_neg,complexHessian_add_const]
    exact hdet x (hBD hx)
  have hbelow (x : E) (hx : x ∈ closedBall x0 r) :
      -translatedBallPotential (a/2) 0 y1 x ≤ g x := by
    have hh : m ≤ w x+translatedBallPotential (a/2) 0 y1 x := hm (hCD hx)
    dsimp only [g]
    linarith only [hh]
  have htouch : g x1 = -translatedBallPotential (a/2) 0 y1 x1 := by
    dsimp only [g,m]; ring
  obtain ⟨z,hz,hzv⟩ := small_lower_contact_penetration_two ha hr hsmall hgc hg hgdet hbelow hx1 htouch
  have hzR : z ∈ ball x0 r := ball_subset_ball (by linarith : r/16 ≤ r) hz
  have hzD : z ∈ D := hCD (ball_subset_closedBall hzR)
  have hv : ∀ x ∈ D, 0 ≤ v x := by
    intro x hx
    exact sub_nonneg.mpr (show m ≤ w x+translatedBallPotential (a/2) 0 y1 x from hm hx)
  have hvz : v z ≤ C*a*r^2 := by
    dsimp only [g] at hzv
    dsimp only [v,C]
    linarith only [hzv]
  let b : ℝ := (M-1)*a
  let V : Set E := closedBall z (r/64)
  let S : Set E := lowerParaboloidContactsTwo b v D V
  let Y : E → E := fun y => M⁻¹ • (y1+(M-1) • y)
  have hb : b = 8192*(C+1)*a := by dsimp only [b]; rw [hMcoef]
  have hS : IsCompact S := lowerParaboloidContactsTwo_isCompact hD (isCompact_closedBall z (r/64))
    ((hwc.add (translatedBallPotential_contDiff (a/2) 0 y1 0).continuous.continuousOn).sub continuousOn_const)
  have hSlocal : S ⊆ ball z (r/16) := by
    dsimp only [S,V]
    rw [hb]
    exact lower_contacts_of_one_small_value_localized_two ha hr hC.le hzD hv hvz
  have hznorm : ‖z-x0‖ < r/16 := by simpa only [mem_ball,dist_eq_norm] using hz
  have hSsmall : S ⊆ ball x0 (r/8) := by
    intro x hx
    have hxn : ‖x-z‖ < r/16 := by simpa only [mem_ball,dist_eq_norm] using hSlocal hx
    rw [mem_ball,dist_eq_norm]
    calc
      ‖x-x0‖ = ‖(x-z)+(z-x0)‖ := by congr 1; module
      _ ≤ ‖x-z‖+‖z-x0‖ := norm_add_le _ _
      _ < r/8 := by linarith only [hxn,hznorm]
  have hSI : S ⊆ interior D :=
    hSsmall.trans ((ball_subset_ball (by linarith : r/8 ≤ r)).trans hBD)
  have hVD : V ⊆ D := by
    intro y hy
    have hyn : ‖y-z‖ ≤ r/64 := by simpa only [V,mem_closedBall,dist_eq_norm] using hy
    apply hCD
    rw [mem_closedBall,dist_eq_norm]
    calc
      ‖y-x0‖ = ‖(y-z)+(z-x0)‖ := by congr 1; module
      _ ≤ ‖y-z‖+‖z-x0‖ := norm_add_le _ _
      _ ≤ r := by linarith only [hyn,hznorm,hr]
  have hYrelation (y : E) : (a+b) • Y y = a • y1+b • y := by
    have hs : (a+b)*M⁻¹ = a := by dsimp only [b]; field_simp; ring
    dsimp only [Y]
    rw [smul_smul,hs,smul_add,smul_smul]
    dsimp only [b]
    rw [mul_comm a (M-1)]
  have hab : a+b = M*a := by dsimp only [b]; ring
  have hYmem (y : E) (hy : y ∈ V) : Y y ∈ D := by
    have he : M⁻¹+(M-1)*M⁻¹ = 1 := by field_simp; ring
    have hh := hconv hy1 (hVD hy) (inv_pos.mpr hM).le
      (mul_nonneg (sub_pos.mpr hM1).le (inv_pos.mpr hM).le) he
    convert hh using 1 <;> dsimp only [Y] <;> module
  have hcombine : S ⊆ lowerParaboloidContactsTwo (M*a) w D (Y '' V) := by
    rw [← hab]
    exact lowerParaboloidContactsTwo_combine_openings a b m w y1 D V Y (fun y _ => hYrelation y)
  have hSactual : S ⊆ lowerParaboloidContactsTwo (M*a) w D D := by
    intro x hx
    obtain ⟨hxD,c,⟨y,hy,rfl⟩,hmin⟩ := hcombine hx
    exact ⟨hxD,Y y,hYmem y hy,hmin⟩
  have hreg (x : E) (hx : x ∈ S) : ContDiffAt ℝ 2 w x :=
    hw.contDiffAt (isOpen_interior.mem_nhds (hSI hx))
  have hlower (x : E) (hx : x ∈ S) (d : E) :
      -(M*a*‖d‖^2) ≤ realHessian w x d d := by
    obtain ⟨_,c,_,hmin⟩ := hSactual hx
    have hloc := hmin.isLocalMin (mem_interior_iff_mem_nhds.mp (hSI hx))
    have hq := (translatedBallPotential_contDiff (M*a/2) 0 c 2).contDiffAt (x := x)
    have hh := realHessian_nonneg_of_isLocalMin ((hreg x hx).add hq) hloc d
    rw [realHessian_add (hreg x hx) hq] at hh
    change 0 ≤ realHessian w x d d+realHessian (translatedBallPotential (M*a/2) 0 c) x d d at hh
    rw [translatedBallPotential_realHessian,real_inner_self_eq_norm_sq] at hh
    linarith only [hh]
  have hcoverage : Y '' V ⊆ paraboloidVertexMapTwo (M*a) w '' S := by
    rintro c ⟨y,hy,rfl⟩
    obtain ⟨x,hx,hmin⟩ := lowerParaboloidContactsTwo_exists_for_vertex hD ⟨z,hzD⟩
      ((hwc.add (translatedBallPotential_contDiff (a/2) 0 y1 0).continuous.continuousOn).sub continuousOn_const) hy
    have hxS : x ∈ S := hx
    have hxoriginal : IsMinOn (fun p => w p+translatedBallPotential (M*a/2) 0 (Y y) p) D x := by
      intro p hp
      have hh : v x+translatedBallPotential (b/2) 0 y x ≤
          v p+translatedBallPotential (b/2) 0 y p := hmin hp
      have hxi := translated_paraboloid_sum_difference_two a b y1 y (Y y) x (hYrelation y)
      have hpi := translated_paraboloid_sum_difference_two a b y1 y (Y y) p (hYrelation y)
      rw [hab] at hxi hpi
      dsimp only [v] at hh
      change w x+translatedBallPotential (M*a/2) 0 (Y y) x ≤
        w p+translatedBallPotential (M*a/2) 0 (Y y) p
      linarith only [hh,hxi,hpi]
    exact ⟨x,hxS,paraboloidVertexMapTwo_eq_vertex_of_lower_contact (mul_pos hM ha).ne'
      ((hreg x hxS).differentiableAt (by norm_num))
      (hxoriginal.isLocalMin (mem_interior_iff_mem_nhds.mp (hSI hxS)))⟩
  have hvol := hmeasure w S (M*a) hS.measurableSet (mul_pos hM ha) hMa hreg
    (fun x hx => hdet x (hSI hx)) hlower
  exact ⟨z,hz,S,hS,hSsmall,hSactual,(measure_mono hcoverage).trans hvol⟩

end PowerConvexity
