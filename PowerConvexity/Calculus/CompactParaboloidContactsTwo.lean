import PowerConvexity.Calculus.ParaboloidVertexMapTwo
import PowerConvexity.Calculus.ClassicalBoundaryNormalTwo

/-! # Actual compact lower contact sets and vertex coverage.
The set is defined by global minima on the same closed domain. Compactness
and existence are proved, and interior contacts recover their actual
vertices through the actual gradient. The interior-location condition
in the final theorem is explicit; it is not an elliptic estimate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Set Metric Filter InnerProductSpace
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus CHS.Analysis
local notation "E" => DeGiorgi.AmbientSpace (2+2)

def lowerParaboloidContactsTwo (a : ℝ) (w : E → ℝ) (D V : Set E) : Set E :=
  {x | x ∈ D ∧ ∃ c ∈ V,
    IsMinOn (fun z => w z+translatedBallPotential (a/2) 0 c z) D x}

theorem lowerParaboloidContactsTwo_isCompact
    {a : ℝ} {w : E → ℝ} {D V : Set E}
    (hD : IsCompact D) (hV : IsCompact V) (hw : ContinuousOn w D) :
    IsCompact (lowerParaboloidContactsTwo a w D V) := by
  letI : CompactSpace D := isCompact_iff_compactSpace.mp hD
  letI : CompactSpace V := isCompact_iff_compactSpace.mp hV
  let P : Set (D × V) := {p | ∀ z : D,
    w p.1+translatedBallPotential (a/2) 0 (p.2 : E) (p.1 : E) ≤
      w z+translatedBallPotential (a/2) 0 (p.2 : E) (z : E)}
  have hc : Continuous (fun x : D => w x) := hw.restrict
  have hP : IsClosed P := by
    rw [show P = ⋂ z : D, {p : D × V |
      w p.1+translatedBallPotential (a/2) 0 (p.2 : E) (p.1 : E) ≤
        w z+translatedBallPotential (a/2) 0 (p.2 : E) (z : E)} by
      ext p
      simp only [P,mem_iInter,mem_setOf_eq]]
    apply isClosed_iInter
    intro z
    apply isClosed_le
    · dsimp only [translatedBallPotential,quadraticBallPotential]
      exact (hc.comp continuous_fst).add (continuous_const.mul
        ((((continuous_subtype_val.comp continuous_fst).sub
          (continuous_subtype_val.comp continuous_snd)).norm.pow 2).sub continuous_const))
    · dsimp only [translatedBallPotential,quadraticBallPotential]
      fun_prop
  have he : (fun p : D × V => (p.1 : E)) '' P = lowerParaboloidContactsTwo a w D V := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      refine ⟨p.1.2,p.2,p.2.2,?_⟩
      intro z hz
      exact hp ⟨z,hz⟩
    · rintro ⟨hx,c,hc,hm⟩
      exact ⟨(⟨x,hx⟩,⟨c,hc⟩),fun z => hm z.2,rfl⟩
  rw [← he]
  exact hP.isCompact.image (continuous_subtype_val.comp continuous_fst)

theorem lowerParaboloidContactsTwo_exists_for_vertex
    {a : ℝ} {w : E → ℝ} {D V : Set E}
    (hD : IsCompact D) (hDn : D.Nonempty) (hw : ContinuousOn w D)
    {c : E} (hc : c ∈ V) :
    ∃ x ∈ lowerParaboloidContactsTwo a w D V,
      IsMinOn (fun z => w z+translatedBallPotential (a/2) 0 c z) D x := by
  obtain ⟨x,hx,hm⟩ := hD.exists_isMinOn hDn
    (hw.add (translatedBallPotential_contDiff (a/2) 0 c 0).continuous.continuousOn)
  exact ⟨x,⟨hx,c,hc,hm⟩,hm⟩

theorem paraboloidVertexMapTwo_eq_vertex_of_lower_contact
    {a : ℝ} (ha : a ≠ 0) {w : E → ℝ} {x c : E}
    (hw : DifferentiableAt ℝ w x)
    (hm : IsLocalMin (fun z => w z+translatedBallPotential (a/2) 0 c z) x) :
    paraboloidVertexMapTwo a w x = c := by
  have hq := (translatedBallPotential_contDiff (a/2) 0 c 1).differentiable (by norm_num)
  have hz := hm.fderiv_eq_zero
  rw [fderiv_fun_add hw hq.differentiableAt] at hz
  have hgrad : gradient w x = -a • (x-c) := by
    apply (toDual ℝ E).injective
    ext v
    have hh := congrArg (fun L : E →L[ℝ] ℝ => L v) hz
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,
      translatedBallPotential_fderiv_apply] at hh
    simp only [gradient,LinearIsometryEquiv.apply_symm_apply,map_smul,
      ContinuousLinearMap.smul_apply,toDual_apply_apply,smul_eq_mul]
    linarith only [hh]
  rw [paraboloidVertexMapTwo,hgrad,smul_smul]
  simp only [mul_neg,inv_mul_cancel₀ ha,neg_smul,one_smul]
  module

theorem lowerParaboloidContactsTwo_vertex_coverage
    {a : ℝ} (ha : a ≠ 0) {w : E → ℝ} {D V : Set E}
    (hD : IsCompact D) (hDn : D.Nonempty) (hw : ContinuousOn w D)
    (hinterior : lowerParaboloidContactsTwo a w D V ⊆ interior D)
    (hreg : ∀ x ∈ lowerParaboloidContactsTwo a w D V, DifferentiableAt ℝ w x) :
    V ⊆ paraboloidVertexMapTwo a w '' lowerParaboloidContactsTwo a w D V := by
  intro c hc
  obtain ⟨x,hx,hm⟩ := lowerParaboloidContactsTwo_exists_for_vertex hD hDn hw hc
  refine ⟨x,hx,?_⟩
  exact paraboloidVertexMapTwo_eq_vertex_of_lower_contact ha (hreg x hx)
    (hm.isLocalMin (mem_interior_iff_mem_nhds.mp (hinterior hx)))

end PowerConvexity
