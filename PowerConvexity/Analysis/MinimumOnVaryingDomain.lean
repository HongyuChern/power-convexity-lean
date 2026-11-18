import PowerConvexity.Analysis.ParameterMinimum

/-! # Minimum continuity from open interiors and compact closure graphs

This form of the minimum theorem does not ask for a homeomorphism of the
domains. Density of each interior in its closure gives the upper bound;
the compact graph gives the lower bound.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology
namespace PowerConvexity
variable {T X : Type*} [TopologicalSpace T] [T2Space T]
  [TopologicalSpace X] [T2Space X]

theorem continuous_minimum_of_open_graph_compact_closure_graph
    {V : T → Set X}
    (hVo : IsOpen {p : T × X | p.2 ∈ V p.1})
    (hG : IsCompact {p : T × X | p.2 ∈ closure (V p.1)})
    (hK : ∀ t, IsCompact (closure (V t))) (hne : ∀ t, (V t).Nonempty)
    {F : T × X → ℝ}
    (hF : ContinuousOn F {p : T × X | p.2 ∈ closure (V p.1)}) :
    Continuous (fun t => sInf ((fun x => F (t,x)) '' closure (V t))) := by
  let G : Set (T × X) := {p | p.2 ∈ closure (V p.1)}
  let m : T → ℝ := fun t => sInf ((fun x => F (t,x)) '' closure (V t))
  have hFt (t : T) : ContinuousOn (fun x => F (t,x)) (closure (V t)) :=
    hF.comp (Continuous.prodMk_right t).continuousOn (fun x hx => hx)
  have hatt (t : T) : ∃ x ∈ closure (V t), m t = F (t,x) ∧
      ∀ y ∈ closure (V t), F (t,x) ≤ F (t,y) :=
    (hK t).exists_sInf_image_eq_and_le ((hne t).mono subset_closure) (hFt t)
  have hminle (t : T) (x : X) (hx : x ∈ closure (V t)) : m t ≤ F (t,x) := by
    obtain ⟨y,_,he,hh⟩ := hatt t
    rw [he]
    exact hh x hx
  change Continuous m
  rw [continuous_iff_continuousAt]
  intro t
  rw [ContinuousAt,tendsto_order]
  constructor
  · intro a ha
    let B := Prod.fst '' (G ∩ F ⁻¹' Iic a)
    have hbad : IsCompact (G ∩ F ⁻¹' Iic a) :=
      hG.of_isClosed_subset (hF.preimage_isClosed_of_isClosed hG.isClosed isClosed_Iic)
        inter_subset_left
    have hB : IsClosed B := (hbad.image continuous_fst).isClosed
    have htB : t ∉ B := by
      rintro ⟨⟨s,x⟩,hp,hs⟩
      change s = t at hs
      subst s
      exact (not_le_of_gt ha) ((hminle t x hp.1).trans hp.2)
    filter_upwards [hB.isOpen_compl.mem_nhds htB] with s hs
    obtain ⟨x,hx,he,_⟩ := hatt s
    rw [he]
    by_contra hh
    exact hs ⟨(s,x),⟨hx,le_of_not_gt hh⟩,rfl⟩
  · intro b hb
    have hex : ∃ y ∈ V t, F (t,y) < b := by
      by_contra hh
      have hge : ∀ y ∈ V t, b ≤ F (t,y) :=
        fun y hy => le_of_not_gt (fun hlt => hh ⟨y,hy,hlt⟩)
      obtain ⟨x,hx,he,_⟩ := hatt t
      have hbx : b ≤ F (t,x) := le_on_closure hge continuousOn_const (hFt t) hx
      rw [← he] at hbx
      exact (not_le_of_gt hb) hbx
    obtain ⟨y,hy,hyb⟩ := hex
    have hc : Continuous (fun s : T => (s,y)) := by fun_prop
    have hVnear : ∀ᶠ s in 𝓝 t, y ∈ V s :=
      hc.continuousAt.tendsto.eventually (hVo.mem_nhds hy)
    have hGnear : ∀ᶠ s in 𝓝 t, (s,y) ∈ G :=
      hVnear.mono (fun _ hs => subset_closure hs)
    have htend : Tendsto (fun s : T => (s,y)) (𝓝 t) (𝓝[G] (t,y)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hc.continuousAt.tendsto,hGnear⟩
    have hlt : ∀ᶠ s in 𝓝 t, F (s,y) < b :=
      ((hF (t,y) (subset_closure hy)).tendsto.comp htend).eventually (gt_mem_nhds hyb)
    filter_upwards [hVnear,hlt] with s hs hsb
    exact (hminle s y (subset_closure hs)).trans_lt hsb

end PowerConvexity
