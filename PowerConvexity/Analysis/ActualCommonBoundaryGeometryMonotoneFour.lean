import PowerConvexity.Analysis.ActualCommonNonlinearBoundaryGeometryFour
import PowerConvexity.Analysis.ActualUniformGraphHeightDilationFour

/-! # Actual physical rescaling and monotonicity of common boundary geometry

Shrinking the physical radius changes the actual height to
rho'(x)=rho((r'/r)x)/(r'/r). The same affine map has the same true domain
side, the first derivative bound is unchanged and the Hessian bound only
decreases. The resulting geometry record retains its original domain,
defining function and interior center.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "E" => AmbientSpace (2+2)
attribute [local instance] cat3 cat4 cat5 cat6 cat7 cat8 testCE pihNormSMul

theorem ActualUnitBoundaryChartsFour.rescale
    {U : Set E} {r r' H H' : ℝ}
    (hcharts : ActualUnitBoundaryChartsFour U r H)
    (hr' : 0 < r') (hrr : r' ≤ r) (hH : 0 ≤ H) (hHH : H ≤ H') :
    ActualUnitBoundaryChartsFour U r' H' := by
  have hr : 0 < r := hr'.trans_le hrr
  let q := r'/r
  have hq : 0 < q := div_pos hr' hr
  have hq1 : q ≤ 1 := (div_le_one hr).mpr hrr
  have hrq : r*q=r' := by dsimp only [q]; field_simp
  let N : E := EuclideanSpace.single 0 1
  intro c hc
  obtain ⟨G,hG,hGi,rho,hrho0,hD0,hinv,hreg,hside⟩ := hcharts c hc
  let psi := actualPhysicalGraphHeightFour rho q
  have hmap (x : E) (hx : x∈closedBall (0 : E) 2) : q • x∈closedBall (0 : E) 2 := by
    have hx2 : ‖x‖ ≤ 2 := by simpa only [mem_closedBall,dist_zero_right] using hx
    rw [mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,abs_of_pos hq]
    exact (mul_le_mul_of_nonneg_left hx2 hq.le).trans (by linarith)
  obtain ⟨_,hpsi0,hDpsi0⟩ := actual_physical_graph_regularity_four
    (R := q) (hreg 0 (mem_closedBall_self (by norm_num))).1 hrho0 hD0
  refine ⟨G,hG,hGi,psi,hpsi0,hDpsi0,?_,?_,?_⟩
  · exact actual_physical_graph_normal_invariance_four hinv q
  · intro x hx
    have hregq := (hreg (q • x) (hmap x hx)).1
    refine ⟨contDiffAt_const.mul (hregq.comp x (contDiffAt_id.const_smul q)),?_,?_⟩
    · rw [actual_physical_graph_fderiv_four hq.ne' (hregq.differentiableAt (by norm_num))]
      exact (hreg (q • x) (hmap x hx)).2.1
    · rw [actual_physical_graph_hessian_four hq.ne' (hregq.of_le (by norm_num)),
        norm_smul,Real.norm_eq_abs,abs_of_pos hq]
      exact (mul_le_mul_of_nonneg_left (hreg (q • x) (hmap x hx)).2.2 hq.le).trans
        ((mul_le_mul_of_nonneg_right hq1 hH).trans (by simpa only [one_mul] using hHH))
  · intro x hx
    have he : r' • actualGraphShearFour N psi x=r • actualGraphShearFour N rho (q • x) := by
      rw [←actual_physical_graph_conjugation_four hq.ne' N rho x,smul_smul,hrq]
    rw [he]
    exact (hside (q • x) (hmap x hx)).trans (by
      rw [inner_smul_right]
      exact mul_pos_iff_of_pos_left hq)

def ActualCommonNonlinearBoundaryGeometryFour.enlarge
    {r r' H H' F F' delta delta' rho D D' : ℝ}
    (Geo : ActualCommonNonlinearBoundaryGeometryFour r H F delta rho D)
    (hr' : 0 < r') (hrr : r' ≤ r) (hH : 0 ≤ H) (hHH : H ≤ H')
    (hFF : F ≤ F') (hdd : delta' ≤ delta) (hDD : D ≤ D') :
    ActualCommonNonlinearBoundaryGeometryFour r' H' F' delta' rho D' where
  domain := Geo.domain
  defining := Geo.defining
  isOpen := Geo.isOpen
  convex := Geo.convex
  compactClosure := Geo.compactClosure
  charts := Geo.charts.rescale hr' hrr hH hHH
  regular := Geo.regular
  boundary := Geo.boundary
  side := Geo.side
  firstBound := fun x hx => (Geo.firstBound x hx).trans hFF
  secondBound := fun x hx => (Geo.secondBound x hx).trans hFF
  thirdBound := fun x hx => (Geo.thirdBound x hx).trans hFF
  normalMargin := fun c hc => hdd.trans (Geo.normalMargin c hc)
  center := Geo.center
  innerBall := Geo.innerBall
  boundaryRadius := fun c hc => (Geo.boundaryRadius c hc).trans hDD

end PowerConvexity
