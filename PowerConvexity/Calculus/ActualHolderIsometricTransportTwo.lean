import PowerConvexity.Calculus.ActualHolderLoadIsometricTransportTwo
import PowerConvexity.Calculus.ActualClosureJetIsometricTransportTwo
import PowerConvexity.Calculus.ActualHolderC2JetLiftTwo
import PowerConvexity.Calculus.ActualHolderResponseLiftTwo

/-! # Bounded two-sided transport of the actual complete C2 Holder jet spaces

The value map is literal composition with the same ambient real isometry.
True closure derivatives are transported by the chain rule. Their exact
operator norms and Holder differences give a contraction in both directions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
  holderResponseJetSeminormedGroup
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_holder_jet_isometric_lift_two
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) :
    ∃ q : actualHolderC2JetSpaceTwo V alpha,
      (∀ x : closure V, actualHolderC2JetSpaceTwo_value V alpha q x=
        actualHolderC2JetSpaceTwo_value U alpha p (actualIsometricClosureMapTwo U V T hUV x)) ∧
      ‖q‖ ≤ ‖p‖ := by
  let u := actualClosureExtensionTwo U p.1.1
  have hreg := actualHolderC2JetSpaceTwo_regular U hU alpha p
  have hu : ContDiffOn ℝ 2 u U := hreg.1
  let J := Classical.choose hreg.2
  have hJ := Classical.choose_spec hreg.2
  let Hv : C(closure U,E →L[ℝ] E →L[ℝ] ℝ) := actualHolderLoadSpaceTwo_value _ _ alpha p.1.2.2
  have hJD (x : E) (hx : x ∈ closure U) : J.derivative x=p.1.2.1 ⟨x,hx⟩ :=
    (congrFun hJ.1 x).trans (actualClosureExtensionTwo_apply U p.1.2.1 hx)
  have hJH (x : E) (hx : x ∈ closure U) : J.hessian x=Hv ⟨x,hx⟩ :=
    (congrFun hJ.2 x).trans (actualClosureExtensionTwo_apply U Hv hx)
  have hbounds (x : E) (hx : x ∈ closure U) :
      |u x| ≤ ‖p‖ ∧ ‖J.derivative x‖ ≤ ‖p‖ ∧ ‖J.hessian x‖ ≤ ‖p‖ := by
    constructor
    · rw [show u x=p.1.1 ⟨x,hx⟩ from actualClosureExtensionTwo_apply U p.1.1 hx]
      exact (p.1.1.norm_coe_le_norm ⟨x,hx⟩).trans (actualHolderC2JetSpaceTwo_norm_bounds U alpha p).1
    constructor
    · rw [hJD x hx]
      exact (p.1.2.1.norm_coe_le_norm ⟨x,hx⟩).trans (actualHolderC2JetSpaceTwo_norm_bounds U alpha p).2.1
    · rw [hJH x hx]
      exact ((Hv.norm_coe_le_norm ⟨x,hx⟩).trans
        (actualHolderLoadSpaceTwo_value_norm_le _ _ alpha p.1.2.2)).trans
        (actualHolderC2JetSpaceTwo_norm_bounds U alpha p).2.2
  have hholder (x : E) (hx : x ∈ closure U) (y : E) (hy : y ∈ closure U) :
      ‖J.hessian x-J.hessian y‖ ≤ ‖p‖*‖x-y‖^alpha := by
    have hh := actualHolderC2JetSpaceTwo_hessian_holder U alpha p ⟨x,hx⟩ ⟨y,hy⟩
    have he : J.hessian x-J.hessian y=Hv ⟨x,hx⟩-Hv ⟨y,hy⟩ :=
      congrArg₂ (fun a b : E →L[ℝ] E →L[ℝ] ℝ => a-b) (hJH x hx) (hJH y hy)
    exact (congrArg norm he).trans_le (by
      simpa only [Subtype.dist_eq,dist_eq_norm] using hh)
  have hmap : MapsTo T V U := by intro x hx; rwa [← hUV] at hx
  have hmapc : MapsTo T (closure V) (closure U) := hmap.closure T.continuous
  have hfront : T ⁻¹' frontier U=frontier V :=
    (T.toHomeomorph.preimage_frontier U).trans (congrArg frontier hUV)
  let JT := actualClosureC2JetIsometricTransportTwo U V T hUV hU hu J
  have huT : ContDiffOn ℝ 2 (fun x => u (T x)) V :=
    hu.comp T.toContinuousLinearEquiv.contDiff.contDiffOn hmap
  have hzero : ∀ x ∈ frontier V, u (T x)=0 := by
    intro x hx
    rw [← hfront] at hx
    exact p.2.2.2 (T x) hx
  have hb : ∀ x ∈ closure V,
      |u (T x)| ≤ ‖p‖ ∧ ‖JT.derivative x‖ ≤ ‖p‖ ∧ ‖JT.hessian x‖ ≤ ‖p‖ := by
    intro x hx
    have hh := hbounds (T x) (hmapc hx)
    refine ⟨hh.1,?_,?_⟩
    · exact (actualClosureC2JetIsometricTransportTwo_derivative_norm U V T hUV hU hu J x).trans_le hh.2.1
    · exact (actualClosureC2JetIsometricTransportTwo_hessian_norm U V T hUV hU hu J x).trans_le hh.2.2
  have hH : ∀ x ∈ closure V, ∀ y ∈ closure V,
      ‖JT.hessian x-JT.hessian y‖ ≤ ‖p‖*‖x-y‖^alpha := by
    intro x hx y hy
    have hh := hholder (T x) (hmapc hx) (T y) (hmapc hy)
    have he : ‖T x-T y‖=‖x-y‖ := by rw [← map_sub,T.norm_map]
    rw [he] at hh
    exact (actualClosureC2JetIsometricTransportTwo_hessian_difference U V T hUV hU hu J x y).trans_le hh
  have hqex := actualHolderC2JetSpaceTwo_lift V hV alpha huT JT hzero (norm_nonneg p) hb hH
  let q := Classical.choose hqex
  have hq := Classical.choose_spec hqex
  refine ⟨q,?_,hq.1.2⟩
  intro x
  have hv := congrArg (fun f : C(closure V,ℝ) => f x) hq.1.1
  change actualHolderC2JetSpaceTwo_value V alpha q x=u (T x) at hv
  exact hv.trans (actualClosureExtensionTwo_apply U p.1.1 (hmapc x.property))

theorem actual_holder_jet_isometric_pullback_exists_two
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ) :
    ∃ S : actualHolderC2JetSpaceTwo U alpha →L[ℝ] actualHolderC2JetSpaceTwo V alpha,
      (∀ p, ∀ x : closure V, actualHolderC2JetSpaceTwo_value V alpha (S p) x=
        actualHolderC2JetSpaceTwo_value U alpha p (actualIsometricClosureMapTwo U V T hUV x)) ∧
      ∀ p, ‖S p‖ ≤ ‖p‖ := by
  let P : C(closure U,ℝ) →L[ℝ] C(closure V,ℝ) :=
    ContinuousMap.compCLM ℝ ℝ (actualIsometricClosureMapTwo U V T hUV)
  let W := actualHolderC2JetSpaceTwo_value V alpha
  let Z := actualHolderC2JetSpaceTwo_value U alpha
  have hex : ∀ p : actualHolderC2JetSpaceTwo U alpha, ∃ q : actualHolderC2JetSpaceTwo V alpha,
      W q=P (Z p) ∧ ‖q‖ ≤ ‖p‖ := by
    intro p
    have he := actual_holder_jet_isometric_lift_two U V hU hV T hUV alpha p
    let q := Classical.choose he
    have hq := Classical.choose_spec he
    exact ⟨q,ContinuousMap.ext (hq.1),hq.2⟩
  choose q hq using hex
  have hinj := actualHolderC2JetSpaceTwo_value_injective V hV alpha
  let L : actualHolderC2JetSpaceTwo U alpha →ₗ[ℝ] actualHolderC2JetSpaceTwo V alpha :=
    { toFun := q
      map_add' := by
        intro p r
        apply hinj
        change W (q (p+r))=W (q p+q r)
        rw [(hq (p+r)).1]
        simp only [map_add,(hq p).1,(hq r).1]
      map_smul' := by
        intro c p
        apply hinj
        change W (q (c • p))=W (c • q p)
        rw [(hq (c • p)).1]
        simp only [map_smul,(hq p).1] }
  let S := L.mkContinuous 1 (fun p => by
    change ‖q p‖ ≤ 1*‖p‖
    simpa only [one_mul] using (hq p).2)
  refine ⟨S,?_,fun p => (hq p).2⟩
  intro p x
  change W (q p) x=Z p (actualIsometricClosureMapTwo U V T hUV x)
  exact congrArg (fun f : C(closure V,ℝ) => f x) (hq p).1

def actualHolderJetIsometricPullbackTwo
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ) :
    actualHolderC2JetSpaceTwo U alpha →L[ℝ] actualHolderC2JetSpaceTwo V alpha :=
  Classical.choose (actual_holder_jet_isometric_pullback_exists_two U V hU hV T hUV alpha)

theorem actualHolderJetIsometricPullbackTwo_apply
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) (x : closure V) :
    actualHolderC2JetSpaceTwo_value V alpha (actualHolderJetIsometricPullbackTwo U V hU hV T hUV alpha p) x=
      actualHolderC2JetSpaceTwo_value U alpha p (actualIsometricClosureMapTwo U V T hUV x) :=
  (Classical.choose_spec (actual_holder_jet_isometric_pullback_exists_two U V hU hV T hUV alpha)).1 p x

def actualHolderJetIsometricEquivTwo
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ) :
    actualHolderC2JetSpaceTwo U alpha ≃L[ℝ] actualHolderC2JetSpaceTwo V alpha := by
  let P := actualHolderJetIsometricPullbackTwo U V hU hV T hUV alpha
  let Q := actualHolderJetIsometricPullbackTwo V U hV hU T.symm (actual_isometric_preimage_symm_two U V T hUV) alpha
  have hleft : Function.LeftInverse Q P := by
    intro p
    apply actualHolderC2JetSpaceTwo_value_injective U hU alpha
    apply ContinuousMap.ext
    intro x
    change actualHolderC2JetSpaceTwo_value U alpha (Q (P p)) x=actualHolderC2JetSpaceTwo_value U alpha p x
    rw [actualHolderJetIsometricPullbackTwo_apply,actualHolderJetIsometricPullbackTwo_apply]
    congr 1
    apply Subtype.ext
    exact T.apply_symm_apply x
  have hright : Function.RightInverse Q P := by
    intro p
    apply actualHolderC2JetSpaceTwo_value_injective V hV alpha
    apply ContinuousMap.ext
    intro x
    change actualHolderC2JetSpaceTwo_value V alpha (P (Q p)) x=actualHolderC2JetSpaceTwo_value V alpha p x
    rw [actualHolderJetIsometricPullbackTwo_apply,actualHolderJetIsometricPullbackTwo_apply]
    congr 1
    apply Subtype.ext
    exact T.symm_apply_apply x
  exact ContinuousLinearEquiv.equivOfInverse P Q hleft hright

theorem actualHolderJetIsometricEquivTwo_apply
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) (x : closure V) :
    actualHolderC2JetSpaceTwo_value V alpha (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p) x=
      actualHolderC2JetSpaceTwo_value U alpha p (actualIsometricClosureMapTwo U V T hUV x) :=
  actualHolderJetIsometricPullbackTwo_apply U V hU hV T hUV alpha p x

theorem actualHolderJetIsometricEquivTwo_apply_value
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (hU : IsOpen U) (hV : IsOpen V) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (p : actualHolderC2JetSpaceTwo U alpha) {x : F} (hx : x ∈ closure V) :
    actualClosureExtensionTwo V (actualHolderJetIsometricEquivTwo U V hU hV T hUV alpha p).1.1 x=
      actualClosureExtensionTwo U p.1.1 (T x) := by
  have hm : T x ∈ closure U := (actualIsometricClosureMapTwo U V T hUV ⟨x,hx⟩).property
  rw [actualClosureExtensionTwo_apply V _ hx,actualClosureExtensionTwo_apply U _ hm]
  exact actualHolderJetIsometricEquivTwo_apply U V hU hV T hUV alpha p ⟨x,hx⟩

end PowerConvexity
