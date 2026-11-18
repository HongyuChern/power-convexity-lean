import PowerConvexity.Analysis.MinkowskiParameterGeometry

/-! # Actual boundary graphs and persistence of a boundary neighborhood

The open total Minkowski domain uses an explicit local decomposition and does
not require a common centered interior ball. Compactness is obtained on the
real parameter interval [0,1], with the actual frontier in each fiber.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open Set Filter Metric
open scoped Topology Pointwise
namespace PowerConvexity

theorem compact_parameter_graph_eventually_subset_open
    {P X : Type*} [TopologicalSpace P] [TopologicalSpace X] [T2Space P]
    {K : Set (P × X)} (hK : IsCompact K) {W : Set X} (hW : IsOpen W)
    {s : P} (hs : ∀ x : X, (s,x) ∈ K → x ∈ W) :
    ∀ᶠ t in 𝓝 s, ∀ x : X, (t,x) ∈ K → x ∈ W := by
  let B := K ∩ (Prod.snd ⁻¹' W)ᶜ
  have hB : IsCompact B := hK.inter_right (hW.preimage continuous_snd).isClosed_compl
  have hclosed : IsClosed (Prod.fst '' B) := (hB.image continuous_fst).isClosed
  have hsnot : s ∉ Prod.fst '' B := by
    rintro ⟨⟨t,x⟩,⟨hKtx,hWx⟩,hts⟩
    change t = s at hts
    subst t
    exact hWx (hs x hKtx)
  filter_upwards [hclosed.isOpen_compl.mem_nhds hsnot] with t ht
  intro x htx
  by_contra hxW
  exact ht ⟨(t,x),⟨htx,hxW⟩,rfl⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem minkowskiDomain_real_parameterGraph_isOpen
    {A B : Set E} (hA : IsOpen A) (hB : IsOpen B) :
    IsOpen {p : ℝ × E | p.2 ∈ minkowskiDomain p.1 A B} := by
  rw [isOpen_iff_mem_nhds]
  rintro ⟨s,x⟩ ⟨a,ha,b,hb,hrep⟩
  change x = s • a+(1-s) • b at hrep
  by_cases hs : s ≠ 0
  · let g : ℝ × E → E := fun p => p.1⁻¹ • (p.2-(1-p.1) • b)
    have hg : ContinuousAt g (s,x) :=
      (continuousAt_fst.inv₀ hs).smul
        (continuousAt_snd.sub ((continuousAt_const.sub continuousAt_fst).smul continuousAt_const))
    have hg0 : g (s,x) = a := by
      dsimp only [g]
      rw [hrep,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hs,one_smul]
    have hga : Tendsto g (𝓝 (s,x)) (𝓝 a) := by simpa only [hg0] using hg.tendsto
    have hne : ∀ᶠ p : ℝ × E in 𝓝 (s,x), p.1 ≠ 0 :=
      continuousAt_fst.tendsto.eventually (eventually_ne_nhds hs)
    filter_upwards [hga.eventually (hA.mem_nhds ha),hne] with p hp hp0
    refine ⟨g p,hp,b,hb,?_⟩
    dsimp only [g]
    rw [smul_smul,mul_inv_cancel₀ hp0,one_smul,sub_add_cancel]
  · have hs0 : s = 0 := not_ne_iff.mp hs
    subst s
    have hxb : x = b := by simpa only [zero_smul,sub_zero,one_smul,zero_add] using hrep
    let g : ℝ × E → E := fun p => (1-p.1)⁻¹ • (p.2-p.1 • a)
    have hg : ContinuousAt g (0,x) :=
      ((continuousAt_const.sub continuousAt_fst).inv₀ (by norm_num)).smul
        (continuousAt_snd.sub (continuousAt_fst.smul continuousAt_const))
    have hg0 : g (0,x) = b := by simp only [g,sub_zero,inv_one,zero_smul,one_smul,hxb]
    have hgb : Tendsto g (𝓝 (0,x)) (𝓝 b) := by simpa only [hg0] using hg.tendsto
    have hne : ∀ᶠ p : ℝ × E in 𝓝 (0,x), 1-p.1 ≠ 0 :=
      (continuousAt_const.sub continuousAt_fst).tendsto.eventually
        (eventually_ne_nhds (by norm_num : (1 : ℝ)-0 ≠ 0))
    filter_upwards [hgb.eventually (hB.mem_nhds hb),hne] with p hp hp1
    refine ⟨a,ha,g p,hp,?_⟩
    dsimp only [g]
    rw [smul_smul,mul_inv_cancel₀ hp1,one_smul]
    abel

theorem minkowskiDomain_real_closure_parameterGraph_isCompact
    {A B : Set E} (hA : IsCompact (closure A)) (hB : IsCompact (closure B)) :
    IsCompact {p : ℝ × E | p.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2 ∈ closure (minkowskiDomain p.1 A B)} := by
  let I := Icc (0 : ℝ) 1
  let K : Set (I × E) := {p | p.2 ∈ closure (minkowskiDomain p.1 A B)}
  let j : I × E → ℝ × E := fun p => ((p.1 : ℝ),p.2)
  have hj : Continuous j := by fun_prop
  have hK : IsCompact K := minkowskiDomain_closure_parameterGraph_isCompact hA hB
  have he : j '' K = {p : ℝ × E | p.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2 ∈ closure (minkowskiDomain p.1 A B)} := by
    ext p
    constructor
    · rintro ⟨⟨t,x⟩,hx,rfl⟩
      exact ⟨t.2,hx⟩
    · rintro ⟨ht,hx⟩
      exact ⟨(⟨p.1,ht⟩,p.2),hx,rfl⟩
  rw [← he]
  exact hK.image hj

theorem minkowskiDomain_real_frontier_parameterGraph_isCompact
    {A B : Set E} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : IsCompact (closure A)) (hB : IsCompact (closure B)) :
    IsCompact {p : ℝ × E | p.1 ∈ Icc (0 : ℝ) 1 ∧
      p.2 ∈ frontier (minkowskiDomain p.1 A B)} := by
  have hC := minkowskiDomain_real_closure_parameterGraph_isCompact hA hB
  have hO := minkowskiDomain_real_parameterGraph_isOpen hAo hBo
  have hV (t : ℝ) : IsOpen (minkowskiDomain t A B) :=
    hO.preimage (continuous_const.prodMk continuous_id)
  have he : {p : ℝ × E | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ frontier (minkowskiDomain p.1 A B)} =
      {p : ℝ × E | p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ closure (minkowskiDomain p.1 A B)} ∩
      {p : ℝ × E | p.2 ∈ minkowskiDomain p.1 A B}ᶜ := by
    ext p
    simp only [mem_setOf_eq,mem_inter_iff,mem_compl_iff,(hV p.1).frontier_eq,mem_diff,and_assoc]
  rw [he]
  exact hC.of_isClosed_subset (hC.isClosed.inter hO.isClosed_compl) inter_subset_left

end PowerConvexity
