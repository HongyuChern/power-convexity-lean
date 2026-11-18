import PowerConvexity.Calculus.ChordBoundaryDecay

/-! # Compact two-point maximum principle with a precise boundary input -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter
open scoped Topology
namespace PowerConvexity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem convexOn_closure_of_chord_maximum
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hK : IsCompact (closure U))
    {f : E → ℝ} (hf : ContinuousOn f (closure U))
    (hdf : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hboundary : ∀ x ∈ frontier U, f x = 0)
    (hnonpos : ∀ x ∈ closure U, f x ≤ 0)
    (hdecay : HasQuadraticBoundaryDecay f U)
    (hinterior : ∀ (a b : ℝ), 0 < a → 0 < b → a+b = 1 →
      ∀ x ∈ U, ∀ y ∈ U, IsLocalMax (chordDefect a b f) (x,y) →
        chordDefect a b f (x,y) ≤ 0) :
    ConvexOn ℝ (closure U) f := by
  have hcl : Convex ℝ (closure U) := hconv.closure
  have hdefect (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a+b = 1)
      (x : E) (hx : x ∈ closure U) (y : E) (hy : y ∈ closure U) :
      chordDefect a b f (x,y) ≤ 0 := by
    let T := closure U ×ˢ closure U
    have hc : ContinuousOn (chordDefect a b f) T := by
      have hcenter : ContinuousOn (fun p : E × E => f (a • p.1+b • p.2)) T :=
        hf.comp (by fun_prop) (fun p hp => hcl hp.1 hp.2 ha.le hb.le hab)
      have hleft : ContinuousOn (fun p : E × E => f p.1) T :=
        hf.comp continuousOn_fst (fun _ hp => hp.1)
      have hright : ContinuousOn (fun p : E × E => f p.2) T :=
        hf.comp continuousOn_snd (fun _ hp => hp.2)
      exact (hcenter.sub (continuousOn_const.mul hleft)).sub (continuousOn_const.mul hright)
    obtain ⟨p,hp,hm⟩ := (hK.prod hK).exists_isMaxOn (f := chordDefect a b f) ⟨(x,y),hx,hy⟩ hc
    by_contra hnot
    have hpos : 0 < chordDefect a b f p := (lt_of_not_ge hnot).trans_le (hm ⟨hx,hy⟩)
    by_cases hpx : p.1 ∈ U
    · by_cases hpy : p.2 ∈ U
      · have hlocal : IsLocalMax (chordDefect a b f) (p.1,p.2) := hm.isLocalMax
          (Filter.mem_of_superset ((hU.prod hU).mem_nhds ⟨hpx,hpy⟩)
            (fun _ hq => ⟨subset_closure hq.1,subset_closure hq.2⟩))
        exact (not_lt_of_ge (hinterior a b ha hb hab p.1 hpx p.2 hpy hlocal)) hpos
      · have hyfront : p.2 ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hp.2,hpy⟩
        have hz : b • p.2+a • p.1 ∈ U := by
          rw [← hU.interior_eq]
          exact hconv.combo_closure_interior_mem_interior hp.2
            (by rwa [hU.interior_eq]) hb.le ha (by linarith)
        obtain ⟨w,hw,hh⟩ := chordDefect_boundary_left_improves hb (hboundary p.2 hyfront)
          (hdf _ hz) (hdecay p.2 hyfront p.1 hpx)
        rw [chordDefect_swap b a f p.2 p.1,chordDefect_swap b a f w p.1] at hh
        exact (not_lt_of_ge (hm (show (p.1,w) ∈ T from ⟨hp.1,subset_closure hw⟩))) hh
    · have hxfront : p.1 ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hp.1,hpx⟩
      by_cases hpy : p.2 ∈ U
      · have hz : a • p.1+b • p.2 ∈ U := by
          rw [← hU.interior_eq]
          exact hconv.combo_closure_interior_mem_interior hp.1
            (by rwa [hU.interior_eq]) ha.le hb hab
        obtain ⟨w,hw,hh⟩ := chordDefect_boundary_left_improves ha (hboundary p.1 hxfront)
          (hdf _ hz) (hdecay p.1 hxfront p.2 hpy)
        exact (not_lt_of_ge (hm (show (w,p.2) ∈ T from ⟨subset_closure hw,hp.2⟩))) hh
      · have hyfront : p.2 ∈ frontier U := by rw [hU.frontier_eq]; exact ⟨hp.2,hpy⟩
        have hn := hnonpos (a • p.1+b • p.2) (hcl hp.1 hp.2 ha.le hb.le hab)
        have hpos' : 0 < f (a • p.1+b • p.2) := by
          simpa only [chordDefect,hboundary p.1 hxfront,hboundary p.2 hyfront,
            mul_zero,sub_zero] using hpos
        exact (not_lt_of_ge hn) hpos'
  refine ⟨hcl,?_⟩
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0,hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0,ha1]
  have hh := hdefect a b (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hab x hx y hy
  change f (a • x+b • y)-a*f x-b*f y ≤ 0 at hh
  change f (a • x+b • y) ≤ a*f x+b*f y
  linarith

end PowerConvexity
