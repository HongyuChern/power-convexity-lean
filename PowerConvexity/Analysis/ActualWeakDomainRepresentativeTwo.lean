import PowerConvexity.Analysis.ActualWeakBallRepresentativeTwo
import Mathlib.Topology.Compactness.Lindelof

/-! # Actual representatives on an arbitrary open domain.
Continuous local representatives agree pointwise on overlaps, because they
agree almost everywhere and the actual volume is positive on open sets.
A countable subcover proves global almost-everywhere equality. Thus no
global representative or compatibility hypothesis is silently assumed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis DeGiorgi
local notation "F" => AmbientSpace (2+2)

theorem actual_continuous_representative_of_local_two {U : Set F} {u : F → ℝ}
    (hloc : ∀ x ∈ U, ∃ (V : Set F) (v : F → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContinuousOn v V ∧
        v =ᵐ[volume.restrict V] u) :
    ∃ g : F → ℝ, ContinuousOn g U ∧ g =ᵐ[volume.restrict U] u := by
  classical
  choose V v hVo hxV hVU hvC hvAE using (fun x : U => hloc x x.property)
  let g : F → ℝ := fun x => if hx : x ∈ U then v ⟨x,hx⟩ x else u x
  have hmatch (i : U) : EqOn g (v i) (V i) := by
    intro y hy
    have hyU := hVU i hy
    let j : U := ⟨y,hyU⟩
    have hj : v j =ᵐ[volume.restrict (V j ∩ V i)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (hvAE j)
    have hi : v i =ᵐ[volume.restrict (V j ∩ V i)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (hvAE i)
    have he := Measure.eqOn_open_of_ae_eq (hj.trans hi.symm) ((hVo j).inter (hVo i))
      ((hvC j).mono inter_subset_left) ((hvC i).mono inter_subset_right)
    have hval := he (show y ∈ V j ∩ V i from ⟨hxV j,hy⟩)
    simpa only [g,dif_pos hyU,j] using hval
  have hgC : ContinuousOn g U := by
    intro x hx
    let i : U := ⟨x,hx⟩
    have hc := ((hvC i).congr (hmatch i)).continuousAt ((hVo i).mem_nhds (hxV i))
    exact hc.continuousWithinAt
  have hcover : U ⊆ ⋃ i : U, V i := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hxV ⟨x,hx⟩⟩
  obtain ⟨K,hK,hcov⟩ := (HereditarilyLindelofSpace.isLindelof U).elim_countable_subcover V hVo hcover
  have hbig : g =ᵐ[volume.restrict (⋃ i ∈ K, V i)] u := by
    apply (ae_restrict_biUnion_iff V hK (fun x => g x=u x)).mpr
    intro i _
    filter_upwards [ae_restrict_mem (hVo i).measurableSet,hvAE i] with x hx he
    exact (hmatch i hx).trans he
  exact ⟨g,hgC,ae_restrict_of_ae_restrict_of_subset hcov hbig⟩

theorem actual_homogeneous_weak_domain_continuous_representative_two
    {U : Set F} (hU : IsOpen U) (A : NormalizedEllipticCoeff (2+2) U)
    {u : F → ℝ} (hu : IsHomogeneousWeakSolution A.1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict U] u ∧
      IsHomogeneousWeakSolution A.1 v ∧ ContinuousOn v U := by
  have hlocal : ∀ x ∈ U, ∃ (V : Set F) (v : F → ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContinuousOn v V ∧ v =ᵐ[volume.restrict V] u := by
    intro x hx
    obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
    have hK : closedBall x (r/2) ⊆ U := by
      intro y hy
      exact hrU (mem_ball.mpr ((mem_closedBall.mp hy).trans_lt (by linarith)))
    have hB : ball x (r/2) ⊆ U := ball_subset_closedBall.trans hK
    let B := NormalizedEllipticCoeff.restrict A hB
    have hs := (isHomogeneousWeakSolution_isSolution hu).restrict_ball hU (half_pos hr) hK
    have hw : IsHomogeneousWeakSolution B.1 u :=
      IsSolution.isHomogeneousWeakSolution isOpen_ball hs
    obtain ⟨v,hvu,_,hvc⟩ := actual_homogeneous_weak_ball_continuous_representative_two (half_pos hr) B hw
    have hsmall : ball x (r/2/2) ⊆ ball x (r/2) := ball_subset_ball (by linarith)
    exact ⟨ball x (r/2/2),v,isOpen_ball,mem_ball_self (half_pos (half_pos hr)),
      hsmall.trans hB,hvc,ae_restrict_of_ae_restrict_of_subset hsmall hvu⟩
  obtain ⟨v,hvc,hvu⟩ := actual_continuous_representative_of_local_two hlocal
  exact ⟨v,hvu,actual_homogeneousWeakSolution_congr_ae hvu.symm hu,hvc⟩

theorem actual_identity_weak_domain_smooth_representative_two
    {U : Set F} (hU : IsOpen U) {u : F → ℝ}
    (hu : IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 u) :
    ∃ v : F → ℝ, v =ᵐ[volume.restrict U] u ∧
      IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 v ∧
      InnerProductSpace.HarmonicOnNhd v U ∧ ∀ n : ℕ∞ω, ContDiffOn ℝ n v U := by
  obtain ⟨v,hvu,hv,hvc⟩ := actual_homogeneous_weak_domain_continuous_representative_two hU
    (identityNormalizedEllipticCoeffTwo U) hu
  have hh := actual_identity_weak_continuous_is_classical_two hU hv hvc
  exact ⟨v,hvu,hv,hh,fun n => actual_classical_harmonic_contDiffOn_two hU hh n⟩

theorem actual_smooth_harmonic_replacement_domain_two
    {U : Set F} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {u : F → ℝ} (hu : MemW1p 2 u U) :
    ∃ v : F → ℝ, IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 v ∧
      MemH01 (fun x => v x-u x) U ∧
      (∀ n : ℕ∞ω, ContDiffOn ℝ n v U) ∧
      ∀ w : F → ℝ, IsHomogeneousWeakSolution (identityNormalizedEllipticCoeffTwo U).1 w →
        MemH01 (fun x => w x-u x) U → ContinuousOn w U → EqOn v w U := by
  obtain ⟨h,hh,hzero⟩ := aHarmonic_replacement_exists (by norm_num : 2 ≤ 2+2)
    hU hUb (identityNormalizedEllipticCoeffTwo U).1 hu
  obtain ⟨v,hvh,hv,_,hvs⟩ := actual_identity_weak_domain_smooth_representative_two hU hh
  have hz : MemH01 (fun x => v x-u x) U := by
    apply actual_zeroTrace_congr_ae (u := fun x => h x-u x) _ hzero
    filter_upwards [hvh] with x hx
    rw [hx]
  refine ⟨v,hv,hz,hvs,?_⟩
  intro w hw hwz hwc
  have he := aHarmonic_replacement_unique (by norm_num : 2 ≤ 2+2) hU hUb
    (identityNormalizedEllipticCoeffTwo U).1 hu hv hz hw hwz
  exact Measure.eqOn_open_of_ae_eq he hU (hvs 0).continuousOn hwc

end PowerConvexity
