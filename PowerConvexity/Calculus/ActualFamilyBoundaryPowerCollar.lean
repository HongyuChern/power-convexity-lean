import PowerConvexity.Calculus.BoundaryPowerHessian
import PowerConvexity.Calculus.DistanceInteriorTruncation
import PowerConvexity.Calculus.SpectralHessianPositivityTwo
import Mathlib.Topology.MetricSpace.Thickening

/-! # A common actual distance collar from jointly continuous closure jets

Compactness is applied to the full moving closure graph.  The interior graph
is open, so a compact subset separated from the boundary graph has a common
positive spatial distance to each moving boundary.  The analytic input is
joint continuity of the actual value, derivative, and Hessian fields on that
closure graph, not merely continuity for each separately fixed parameter.

The conclusion chooses the thickness before both the smaller positive
truncation and the parameter.  The jet fields belong to the supplied same
solution family.  No assertion that these joint continuity hypotheses hold
for an arbitrary classical family is made here.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology ComplexOrder
namespace PowerConvexity
open CHS.Calculus

theorem compact_moving_domain_distance_collar_of_joint_boundary_germs
    {T E : Type*} [MetricSpace T] [MetricSpace E]
    {U : T → Set E} (hU : ∀ t, IsOpen (U t))
    (hgraph : IsOpen {p : T × E | p.2 ∈ U p.1})
    (hK : IsCompact {p : T × E | p.2 ∈ closure (U p.1)})
    (hfront : ∀ t, (frontier (U t)).Nonempty)
    {P : T × E → Prop}
    (hgerm : ∀ t, ∀ x ∈ frontier (U t),
      ∀ᶠ p in 𝓝 (t,x), p.2 ∈ U p.1 → P p) :
    ∃ delta > 0, ∀ t, ∀ x ∈ U t,
      infDist x (frontier (U t)) < delta → P (t,x) := by
  let O := interior {p : T × E | p.2 ∈ U p.1 → P p}
  have hO : IsOpen O := isOpen_interior
  let C := {p : T × E | p.2 ∈ closure (U p.1)} \ O
  have hC : IsCompact C := hK.diff hO
  have hCG : C ⊆ {p : T × E | p.2 ∈ U p.1} := by
    intro p hp
    by_contra hpU
    have hpF : p.2 ∈ frontier (U p.1) := by
      rw [(hU p.1).frontier_eq]
      exact ⟨hp.1,hpU⟩
    have hpO : p ∈ O := mem_interior_iff_mem_nhds.mpr (hgerm p.1 p.2 hpF)
    exact hp.2 hpO
  obtain ⟨delta,hdelta,hthick⟩ := hC.exists_thickening_subset_open hgraph hCG
  refine ⟨delta,hdelta,?_⟩
  intro t x hx hdist
  have hpO : (t,x) ∈ O := by
    by_contra hpO
    have hpC : (t,x) ∈ C := ⟨subset_closure hx,hpO⟩
    obtain ⟨z,hz,hxz⟩ := (infDist_lt_iff (hfront t)).mp hdist
    have hzt : (t,z) ∈ thickening delta C := by
      apply mem_thickening_iff.mpr
      refine ⟨(t,x),hpC,?_⟩
      simpa only [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,dist_comm] using hxz
    have hzU : z ∈ U t := hthick hzt
    rw [(hU t).frontier_eq] at hz
    exact hz.2 hzU
  exact (interior_subset hpO) hx

variable {T E : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem actual_family_power_hessian_joint_boundary_germ
    {U : T → Set E} (hU : ∀ t, IsOpen (U t)) {u : T → E → ℝ}
    (hu : ∀ t, ContDiffOn ℝ 2 (u t) (U t)) (J : ∀ t, ClosureC2Jet (u t) (U t))
    (hvalue : ContinuousOn (fun p : T × E => u p.1 p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hder : ContinuousOn (fun p : T × E => (J p.1).derivative p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hhess : ContinuousOn (fun p : T × E => (J p.1).hessian p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hneg : ∀ t, ∀ x ∈ U t, u t x < 0)
    {t : T} {x : E} (hx : x ∈ closure (U t)) (hux : u t x = 0)
    (htan : ∀ v : E, v ≠ 0 → (J t).derivative x v = 0 → 0 < (J t).hessian x v v) :
    ∀ᶠ p in 𝓝 (t,x), p.2 ∈ U p.1 → ∀ v : E, v ≠ 0 →
      0 < realHessian (powerTransform (u p.1)) p.2 v v := by
  letI : AddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toAddCommGroup
  letI : Module ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ)).toModule
  letI : TopologicalSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ)).toMetricSpace.toUniformSpace.toTopologicalSpace
  obtain ⟨lam,hlam,hQpos⟩ := exists_rankOne_stabilization_positive ((J t).hessian x)
    ((J t).derivative x) htan
  let Q : T × E → E →L[ℝ] E →L[ℝ] ℝ := fun p =>
    (J p.1).hessian p.2+lam • ((J p.1).derivative p.2).smulRight ((J p.1).derivative p.2)
  have hQc : ContinuousWithinAt Q {p : T × E | p.2 ∈ closure (U p.1)} (t,x) := by
    have hd := hder (t,x) hx
    have hh := hhess (t,x) hx
    have hr : ContinuousWithinAt (fun p : T × E =>
        (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)) ((J p.1).derivative p.2))
        {p | p.2 ∈ closure (U p.1)} (t,x) :=
      (ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] ℝ)).continuous.continuousAt.comp_continuousWithinAt hd
    exact hh.add ((hr.clm_apply hd).const_smul lam)
  have hQp : ∀ v : E, v ≠ 0 → 0 < Q (t,x) v v := by
    intro v hv
    simpa only [Q,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,pow_two] using hQpos v hv
  have heQ := eventually_nhdsWithin_iff.mp (positive_bilinear_eventually_within hQc hQp)
  have hub : -1/(2*lam) < u t x := by
    rw [hux]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have heu := eventually_nhdsWithin_iff.mp
    ((hvalue (t,x) hx).tendsto.eventually (lt_mem_nhds hub))
  filter_upwards [heQ,heu] with p hQp hup hp
  have hpcl : p.2 ∈ closure (U p.1) := subset_closure hp
  have hnp := hneg p.1 p.2 hp
  have hweight : lam ≤ 1/(2*(-u p.1 p.2)) := by
    apply (le_div_iff₀ (by linarith : 0 < 2*(-u p.1 p.2))).mpr
    have hh := (div_lt_iff₀ (by positivity : 0 < 2*lam)).mp (hup hpcl)
    nlinarith
  intro v hv
  have hpos := hQp hpcl v hv
  change 0 < (J p.1).hessian p.2 v v+lam*(((J p.1).derivative p.2 v)*((J p.1).derivative p.2 v)) at hpos
  rw [(J p.1).derivative_eq hp,(J p.1).hessian_eq hp] at hpos
  rw [realHessian_powerTransform ((hu p.1).contDiffAt ((hU p.1).mem_nhds hp)) hnp]
  apply mul_pos (sqrtSlope_pos hnp)
  have hm := mul_le_mul_of_nonneg_right hweight (sq_nonneg (fderiv ℝ (u p.1) p.2 v))
  have he : (fderiv ℝ (u p.1) p.2 v)*(fderiv ℝ (u p.1) p.2 v)/(2*(-u p.1 p.2)) =
      (1/(2*(-u p.1 p.2)))*(fderiv ℝ (u p.1) p.2 v)^2 := by ring
  rw [he]
  change 0 < realHessian (u p.1) p.2 v v+(1/(2*(-u p.1 p.2)))*(fderiv ℝ (u p.1) p.2 v)^2
  change 0 < realHessian (u p.1) p.2 v v+lam*((fderiv ℝ (u p.1) p.2 v)*(fderiv ℝ (u p.1) p.2 v)) at hpos
  nlinarith

theorem actual_family_common_truncation_power_hessian_of_joint_closure_jets
    {S : Type*} [MetricSpace S]
    {U : S → Set E} (hU : ∀ t, IsOpen (U t))
    (hgraph : IsOpen {p : S × E | p.2 ∈ U p.1})
    (hK : IsCompact {p : S × E | p.2 ∈ closure (U p.1)})
    (hfront : ∀ t, (frontier (U t)).Nonempty)
    {u : S → E → ℝ} (hu : ∀ t, ContDiffOn ℝ 2 (u t) (U t))
    (J : ∀ t, ClosureC2Jet (u t) (U t))
    (hvalue : ContinuousOn (fun p : S × E => u p.1 p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hder : ContinuousOn (fun p : S × E => (J p.1).derivative p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hhess : ContinuousOn (fun p : S × E => (J p.1).hessian p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hneg : ∀ t, ∀ x ∈ U t, u t x < 0)
    (hb : ∀ t, ∀ x ∈ frontier (U t), u t x = 0)
    (htan : ∀ t, ∀ x ∈ frontier (U t), ∀ v : E, v ≠ 0 →
      (J t).derivative x v = 0 → 0 < (J t).hessian x v v) :
    ∃ delta > 0, ∀ eps : ℝ, 0 < eps → eps < delta →
      ∀ t : S, ∀ x ∈ frontier (distanceInteriorDomain (U t) eps),
        ∀ v : E, v ≠ 0 → 0 < realHessian (powerTransform (u t)) x v v := by
  obtain ⟨delta,hdelta,hcollar⟩ :=
    compact_moving_domain_distance_collar_of_joint_boundary_germs hU hgraph hK hfront
      (P := fun p : S × E => ∀ v : E, v ≠ 0 →
        0 < realHessian (powerTransform (u p.1)) p.2 v v)
      (fun t x hx => actual_family_power_hessian_joint_boundary_germ
        hU hu J hvalue hder hhess hneg (frontier_subset_closure hx) (hb t x hx) (htan t x hx))
  refine ⟨delta,hdelta,?_⟩
  intro eps heps hepsdelta t x hx
  obtain ⟨hxU,hxd⟩ := distanceInteriorDomain_frontier_value (hU t) heps x hx
  exact hcollar t x hxU (by rw [hxd]; exact hepsdelta)

theorem actual_family_common_truncation_sigma_two_of_joint_closure_jets
    {S : Type*} [MetricSpace S] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    (e : Module.Basis (Fin 2) ℂ E)
    {U : S → Set E} (hU : ∀ t, IsOpen (U t))
    (hgraph : IsOpen {p : S × E | p.2 ∈ U p.1})
    (hK : IsCompact {p : S × E | p.2 ∈ closure (U p.1)})
    (hfront : ∀ t, (frontier (U t)).Nonempty)
    {u : S → E → ℝ} (hu : ∀ t, ContDiffOn ℝ 2 (u t) (U t))
    (J : ∀ t, ClosureC2Jet (u t) (U t))
    (hvalue : ContinuousOn (fun p : S × E => u p.1 p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hder : ContinuousOn (fun p : S × E => (J p.1).derivative p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hhess : ContinuousOn (fun p : S × E => (J p.1).hessian p.2)
      {p | p.2 ∈ closure (U p.1)})
    (hneg : ∀ t, ∀ x ∈ U t, u t x < 0)
    (hb : ∀ t, ∀ x ∈ frontier (U t), u t x = 0)
    (hA : ∀ t, ∀ x ∈ U t,
      (complexHessian e (fun j => Complex.I • e j) (u t) x).PosDef)
    (htan : ∀ t, ∀ x ∈ frontier (U t), ∀ v : E, v ≠ 0 →
      (J t).derivative x v = 0 → 0 < (J t).hessian x v v) :
    ∃ delta > 0, ∀ eps : ℝ, 0 < eps → eps < delta →
      ∀ t : S, ∀ x ∈ frontier (distanceInteriorDomain (U t) eps),
        0 < modifiedSigmaTwo e (fun j => Complex.I • e j) (u t) x := by
  obtain ⟨delta,hdelta,hcollar⟩ :=
    actual_family_common_truncation_power_hessian_of_joint_closure_jets
      hU hgraph hK hfront hu J hvalue hder hhess hneg hb htan
  refine ⟨delta,hdelta,?_⟩
  intro eps heps hepsdelta t x hx
  have hxU := (distanceInteriorDomain_frontier_value (hU t) heps x hx).1
  exact (modifiedSigmaTwo_pos_iff_powerHessian_pos e
    ((hu t).contDiffAt ((hU t).mem_nhds hxU)) (hneg t x hxU) (hA t x hxU)).mpr
    (hcollar eps heps hepsdelta t x hx)

end PowerConvexity
