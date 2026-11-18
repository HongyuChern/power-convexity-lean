import PowerConvexity.Calculus.ActualClassicalMinkowskiExistenceTwo
import PowerConvexity.Calculus.MinkowskiStrongActualCommonCollarTwo
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Strong-domain power convexity through the actual original deformation

The actual classical family is constructed, its common true truncation
collar is proved, and the existing P119/exhaustion chain is applied. The
prescribed endpoint is retained literally. Auxiliary measure/compact-set
data are constructed here and do not strengthen the geometric hypotheses.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4200000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [FiniteDimensional ℝ E] [FiniteDimensional ℂ E] [CompleteSpace E]
local instance asdpRealSpace : NormedSpace ℝ E := InnerProductSpace.toNormedSpace
local instance asdpRealModule : Module ℝ E := (inferInstance : InnerProductSpace ℝ E).toModule

theorem actual_strong_defining_dirichlet_sigma_strictConvex_two
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    (h0 : (0 : E)∈U) {F : E → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFb : ∀ x∈frontier U, F x=0 ∧ fderiv ℝ F x≠0 ∧
      ∀ᶠ z in 𝓝 x, z∈U ↔ F z<0)
    {delta : ℝ} (hdelta : 0<delta)
    (hFH : ∀ x∈frontier U, ∀ v:E, 2*delta*‖v‖^2≤realHessian F x v v)
    (e : Module.Basis (Fin 2) ℂ E)
    (hab : Orthonormal ℝ (Sum.elim e (fun j => Complex.I • e j)))
    {u : E → ℝ} (hu : ClassicalDirichletDataTwo e (fun j => Complex.I • e j) U u) :
    (∀ x∈U, 0<modifiedSigmaTwo e (fun j => Complex.I • e j) u x) ∧
      StrictConvexOn ℝ U (powerTransform u) := by
  letI : Nontrivial E := ⟨⟨e 0,0,e.ne_zero 0⟩⟩
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  have hsmooth : HasSmoothLocalDefiningFunction U := fun x hx =>
    ⟨F,hF.contDiffAt,(hFb x hx).1,(hFb x hx).2.1,(hFb x hx).2.2⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds h0)
  let rho := min (r/2) (1/2 : ℝ)
  have hrho : 0<rho := lt_min (half_pos hr) (by norm_num)
  have hrhor : rho<r := (min_le_left _ _).trans_lt (half_lt_self hr)
  have hrho1 : rho<(1 : ℝ) := (min_le_right _ _).trans_lt (by norm_num)
  have hballA : closedBall (0:E) rho⊆U := (closedBall_subset_ball hrhor).trans hball
  have hballB : closedBall (0:E) rho⊆ball 0 (1 : ℝ) := closedBall_subset_ball hrho1
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (f := fun x:E => x) continuousOn_id
  let L := max (1:ℝ) C
  have hL : 0≤L := (by norm_num : (0:ℝ)≤1).trans (le_max_left _ _)
  have hAb : ∀ x∈U, ‖x‖≤L := fun x hx => (hC x (subset_closure hx)).trans (le_max_right _ _)
  have hBb : ∀ x∈ball (0:E) (1:ℝ), ‖x‖≤L := by
    intro x hx
    have hxn : ‖x‖<(1:ℝ) := by simpa only [mem_ball,dist_zero_right] using hx
    exact hxn.le.trans (le_max_left _ _)
  obtain ⟨v,hv,hend⟩ := actual_classical_minkowski_family_exists_two hU ⟨0,h0⟩ hconv hK
    hsmooth e hab hu (by norm_num : (0:ℝ)<1)
  let J := fun t => Classical.choice (hv t).2.1
  have hQ : IsCompact (closedBall (0:E) (1:ℝ)) := isCompact_closedBall _ _
  have hQi : (interior (closedBall (0:E) (1:ℝ))).Nonempty := by
    refine ⟨0,?_⟩
    rw [interior_closedBall (0:E) (by norm_num : (1:ℝ)≠0)]
    exact mem_ball_self (by norm_num)
  have hh := minkowski_strong_defining_actual_original_domain_exhaustion_two
    (volume : Measure E) hQ hQi hU hconv hK hF hFb hdelta hFH e hab
    (by norm_num : (0:ℝ)<1) hrho hL hballA hballB hAb hBb hv J ⟨1,by norm_num⟩
  have hB : (ball (0:E) (1:ℝ)).Nonempty := ⟨0,mem_ball_self (by norm_num)⟩
  simpa only [show ((⟨1,by norm_num⟩ : Icc (0:ℝ) 1):ℝ)=1 from rfl,
    minkowskiDomain_one hB,hend] using hh

end PowerConvexity
