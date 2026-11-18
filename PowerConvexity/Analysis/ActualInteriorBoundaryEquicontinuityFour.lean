import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Joining actual interior equicontinuity to a common boundary modulus

Boundary-to-closure estimates are sufficient: the other argument need not
already be an interior-boundary pair with a nearest-point choice.  On the
interior we use the actual family equicontinuity, then Arzela--Ascoli on the
compact closure.  No per-function continuity modulus is substituted for a
modulus common to the family, and no global modulus is postulated.

The topological statements are dimension independent; they are used for the
four-real-dimensional closure Hessian fields.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section
open Set Filter Metric
open scoped Topology BoundedContinuousFunction
namespace PowerConvexity

theorem actual_interior_boundary_equicontinuous_four
    {X Z ι : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Z]
    {U : Set X} (hU : IsOpen U) (F : ι → X → Z)
    (hinterior : EquicontinuousOn F U)
    {C delta gamma : ℝ} (hdelta : 0 < delta) (hgamma : 0 < gamma)
    (hboundary : ∀ i, ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < delta →
      ‖F i x-F i c‖ ≤ C*‖x-c‖^gamma) :
    EquicontinuousOn F (closure U) := by
  intro c hc
  by_cases hci : c ∈ U
  · have he : EquicontinuousAt F c := by
      simpa only [EquicontinuousWithinAt,
        nhdsWithin_eq_nhds.mpr (hU.mem_nhds hci),EquicontinuousAt]
        using hinterior c hci
    exact he.equicontinuousWithinAt (closure U)
  · have hcf : c ∈ frontier U := by
      rw [hU.frontier_eq]
      exact ⟨hc,hci⟩
    apply (equicontinuousAt_restrict_iff F (⟨c,hc⟩ : closure U)).mp
    have hcont : Continuous (fun x : closure U => C*‖(x : X)-c‖^gamma) :=
      continuous_const.mul ((Real.continuous_rpow_const hgamma.le).comp
        ((continuous_subtype_val.sub continuous_const).norm))
    have hlim : Tendsto (fun x : closure U => C*‖(x : X)-c‖^gamma)
        (𝓝 (⟨c,hc⟩ : closure U)) (𝓝 (0 : ℝ)) := by
      simpa only [sub_self,norm_zero,Real.zero_rpow hgamma.ne',mul_zero]
        using hcont.tendsto (⟨c,hc⟩ : closure U)
    apply Metric.equicontinuousAt_of_continuity_modulus _ hlim
    filter_upwards [Metric.ball_mem_nhds (⟨c,hc⟩ : closure U) hdelta] with x hx i
    have hnear : ‖(x : X)-c‖ < delta := by
      simpa only [mem_ball,Subtype.dist_eq,dist_eq_norm] using hx
    change dist (F i c) (F i x) ≤ C*‖(x : X)-c‖^gamma
    rw [dist_comm,dist_eq_norm]
    exact hboundary i c hcf x x.property hnear

theorem actual_compact_equicontinuous_sequence_uniform_subsequence_four
    {X Z : Type*} [MetricSpace X] [NormedAddCommGroup Z] [ProperSpace Z]
    {K : Set X} (hK : IsCompact K) (F : ℕ → X → Z)
    (hequi : EquicontinuousOn F K)
    (M : ℝ) (hbound : ∀ n x, x ∈ K → ‖F n x‖ ≤ M) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : X → Z,
      ContinuousOn g K ∧ TendstoUniformlyOn (fun n => F (phi n)) g atTop K ∧
      ∀ x ∈ K, ‖g x‖ ≤ M := by
  classical
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let fK : ℕ → K → Z := fun n x => F n x
  have hfk : Equicontinuous fK := (equicontinuous_restrict_iff F).mpr hequi
  let k : ℕ → K →ᵇ Z := fun n => BoundedContinuousFunction.mkOfCompact
    ⟨fK n,hfk.continuous n⟩
  have hcompactRange : ∀ (p : K →ᵇ Z) (x : K), p ∈ range k → p x ∈ closedBall (0 : Z) M := by
    rintro p x ⟨n,rfl⟩
    simpa only [k,fK,BoundedContinuousFunction.mkOfCompact_apply,ContinuousMap.coe_mk,
      mem_closedBall,dist_zero_right] using hbound n x x.property
  have hkequi : Equicontinuous ((↑) : range k → K → Z) := by
    intro x
    rw [Metric.equicontinuousAt_iff_right]
    intro epsilon hepsilon
    have hh := Metric.equicontinuousAt_iff_right.mp (hfk x) epsilon hepsilon
    filter_upwards [hh] with y hy p
    rcases p with ⟨p,⟨n,rfl⟩⟩
    exact hy n
  have hcompact := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : Z) M)
    (isCompact_closedBall (0 : Z) M) (range k) hcompactRange hkequi
  obtain ⟨g,_,phi,hphi,hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  have huniform : TendstoUniformly (fun n => fK (phi n)) (fun x => g x) atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  let gext : X → Z := fun x => if hx : x ∈ K then g ⟨x,hx⟩ else 0
  have heq (x : K) : gext x = g x := by simp only [gext,dif_pos,x.property]
  have hgext : ContinuousOn gext K := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous (fun x : K => gext x)
    have hh : (fun x : K => gext x) = g := funext heq
    rw [hh]
    exact g.continuous
  have huniformExt : TendstoUniformlyOn (fun n => F (phi n)) gext atTop K := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    simpa only [fK,Function.comp_def,heq] using huniform
  refine ⟨phi,hphi,gext,hgext,huniformExt,?_⟩
  intro x hx
  have hb : ‖g ⟨x,hx⟩‖ ≤ M := le_of_tendsto (huniform.tendsto_at ⟨x,hx⟩).norm
    (Eventually.of_forall (fun n => hbound (phi n) x hx))
  simpa only [gext,dif_pos hx] using hb

theorem actual_interior_boundary_uniform_subsequence_four
    {X Z : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Z] [ProperSpace Z]
    {U : Set X} (hU : IsOpen U) (hK : IsCompact (closure U))
    (F : ℕ → X → Z) (hinterior : EquicontinuousOn F U)
    {C delta gamma : ℝ} (hdelta : 0 < delta) (hgamma : 0 < gamma)
    (hboundary : ∀ n, ∀ c ∈ frontier U, ∀ x ∈ closure U, ‖x-c‖ < delta →
      ‖F n x-F n c‖ ≤ C*‖x-c‖^gamma)
    (M : ℝ) (hbound : ∀ n x, x ∈ closure U → ‖F n x‖ ≤ M) :
    ∃ phi : ℕ → ℕ, StrictMono phi ∧ ∃ g : X → Z,
      ContinuousOn g (closure U) ∧
      TendstoUniformlyOn (fun n => F (phi n)) g atTop (closure U) ∧
      ∀ x ∈ closure U, ‖g x‖ ≤ M :=
  actual_compact_equicontinuous_sequence_uniform_subsequence_four hK F
    (actual_interior_boundary_equicontinuous_four hU F hinterior hdelta hgamma hboundary)
    M hbound

end PowerConvexity
