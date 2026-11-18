import PowerConvexity.Calculus.ActualClosureFunctionExtensionTwo

/-! # Complete Holder loads under the actual ambient isometry

Both operators act by literal composition on the same closed domains.
The difference quotient norm is transported using the exact distance
identity, and both bounded inverses are constructed.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem actual_isometric_preimage_symm_two
    (U : Set E) (V : Set F) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) :
    T.symm ⁻¹' V=U := by
  rw [← hUV]
  ext x
  simp only [mem_preimage,T.apply_symm_apply]

def actualIsometricClosureMapTwo
    (U : Set E) (V : Set F) (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) :
    C(closure V,closure U) := by
  have hmap : MapsTo T V U := by
    intro x hx
    rwa [← hUV] at hx
  have hclosed : MapsTo T (closure V) (closure U) := hmap.closure T.continuous
  exact ⟨fun x => ⟨T x,hclosed x.property⟩,
    (T.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem actual_holder_load_isometric_pullback_exists_two
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ) :
    ∃ S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ]
        actualHolderLoadSpaceTwo (closure V) ℝ alpha,
      (∀ f, ∀ x : closure V, actualHolderLoadSpaceTwo_value _ _ alpha (S f) x=
        actualHolderLoadSpaceTwo_value _ _ alpha f (actualIsometricClosureMapTwo U V T hUV x)) ∧
      ∀ f, ‖S f‖ ≤ ‖f‖ := by
  let P : C(closure U,ℝ) →L[ℝ] C(closure V,ℝ) :=
    ContinuousMap.compCLM ℝ ℝ (actualIsometricClosureMapTwo U V T hUV)
  let W := actualHolderLoadSpaceTwo_value (closure V) ℝ alpha
  let Z := actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
  have hex : ∀ f : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ∃ q : actualHolderLoadSpaceTwo (closure V) ℝ alpha,
        W q=P (Z f) ∧ ‖q‖ ≤ ‖f‖ := by
    intro f
    have hholder : ∀ x y : closure V,
        ‖P (Z f) x-P (Z f) y‖ ≤ ‖f‖*(dist x y)^alpha := by
      intro x y
      have hh := actualHolderLoadSpaceTwo_holder_bound (closure U) ℝ alpha f
        (actualIsometricClosureMapTwo U V T hUV x) (actualIsometricClosureMapTwo U V T hUV y)
      simpa only [P,Z,ContinuousMap.compCLM_apply,ContinuousMap.coe_comp,Function.comp_apply,
        actualIsometricClosureMapTwo,ContinuousMap.coe_mk,Subtype.dist_eq,T.dist_map] using hh
    have hnorm : ‖P (Z f)‖ ≤ ‖f‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
      intro x
      change ‖Z f (actualIsometricClosureMapTwo U V T hUV x)‖ ≤ ‖f‖
      exact ((Z f).norm_coe_le_norm (actualIsometricClosureMapTwo U V T hUV x)).trans
        (actualHolderLoadSpaceTwo_value_norm_le _ _ alpha f)
    have hqex := actualHolderLoadSpaceTwo_lift (closure V) ℝ alpha (P (Z f)) (norm_nonneg f) hholder
    let q := Classical.choose hqex
    have hq := Classical.choose_spec hqex
    exact ⟨q,hq.1.1,hq.1.2.trans (max_le hnorm le_rfl)⟩
  choose q hq using hex
  have hinj := actualHolderLoadSpaceTwo_value_injective (closure V) ℝ alpha
  let L : actualHolderLoadSpaceTwo (closure U) ℝ alpha →ₗ[ℝ]
      actualHolderLoadSpaceTwo (closure V) ℝ alpha :=
    { toFun := q
      map_add' := by
        intro f g
        apply hinj
        change W (q (f+g))=W (q f+q g)
        rw [(hq (f+g)).1]
        simp only [map_add,(hq f).1,(hq g).1]
      map_smul' := by
        intro c f
        apply hinj
        change W (q (c • f))=W (c • q f)
        rw [(hq (c • f)).1]
        simp only [map_smul,(hq f).1] }
  let S := L.mkContinuous 1 (fun f => by
    change ‖q f‖ ≤ 1*‖f‖
    simpa only [one_mul] using (hq f).2)
  refine ⟨S,?_,fun f => (hq f).2⟩
  intro f x
  change W (q f) x=Z f (actualIsometricClosureMapTwo U V T hUV x)
  exact congrArg (fun g : C(closure V,ℝ) => g x) (hq f).1

def actualHolderLoadIsometricPullbackTwo
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ) :
    actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ]
      actualHolderLoadSpaceTwo (closure V) ℝ alpha :=
  Classical.choose (actual_holder_load_isometric_pullback_exists_two U V T hUV alpha)

theorem actualHolderLoadIsometricPullbackTwo_apply
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (f : actualHolderLoadSpaceTwo (closure U) ℝ alpha) (x : closure V) :
    actualHolderLoadSpaceTwo_value _ _ alpha (actualHolderLoadIsometricPullbackTwo U V T hUV alpha f) x=
      actualHolderLoadSpaceTwo_value _ _ alpha f (actualIsometricClosureMapTwo U V T hUV x) :=
  (Classical.choose_spec (actual_holder_load_isometric_pullback_exists_two U V T hUV alpha)).1 f x

def actualHolderLoadIsometricEquivTwo
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ) :
    actualHolderLoadSpaceTwo (closure U) ℝ alpha ≃L[ℝ]
      actualHolderLoadSpaceTwo (closure V) ℝ alpha := by
  let P := actualHolderLoadIsometricPullbackTwo U V T hUV alpha
  let Q := actualHolderLoadIsometricPullbackTwo V U T.symm (actual_isometric_preimage_symm_two U V T hUV) alpha
  have hleft : Function.LeftInverse Q P := by
    intro f
    apply actualHolderLoadSpaceTwo_value_injective (closure U) ℝ alpha
    apply ContinuousMap.ext
    intro x
    change actualHolderLoadSpaceTwo_value _ _ alpha (Q (P f)) x=actualHolderLoadSpaceTwo_value _ _ alpha f x
    rw [actualHolderLoadIsometricPullbackTwo_apply,actualHolderLoadIsometricPullbackTwo_apply]
    congr 1
    apply Subtype.ext
    exact T.apply_symm_apply x
  have hright : Function.RightInverse Q P := by
    intro f
    apply actualHolderLoadSpaceTwo_value_injective (closure V) ℝ alpha
    apply ContinuousMap.ext
    intro x
    change actualHolderLoadSpaceTwo_value _ _ alpha (P (Q f)) x=actualHolderLoadSpaceTwo_value _ _ alpha f x
    rw [actualHolderLoadIsometricPullbackTwo_apply,actualHolderLoadIsometricPullbackTwo_apply]
    congr 1
    apply Subtype.ext
    exact T.symm_apply_apply x
  exact ContinuousLinearEquiv.equivOfInverse P Q hleft hright

theorem actualHolderLoadIsometricEquivTwo_apply
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (f : actualHolderLoadSpaceTwo (closure U) ℝ alpha) (x : closure V) :
    actualHolderLoadSpaceTwo_value _ _ alpha (actualHolderLoadIsometricEquivTwo U V T hUV alpha f) x=
      actualHolderLoadSpaceTwo_value _ _ alpha f (actualIsometricClosureMapTwo U V T hUV x) :=
  actualHolderLoadIsometricPullbackTwo_apply U V T hUV alpha f x

theorem actualHolderLoadIsometricEquivTwo_apply_value
    (U : Set E) (V : Set F) [CompactSpace (closure U)] [CompactSpace (closure V)]
    (T : F ≃ₗᵢ[ℝ] E) (hUV : T ⁻¹' U=V) (alpha : ℝ)
    (f : actualHolderLoadSpaceTwo (closure U) ℝ alpha) {x : F} (hx : x ∈ closure V) :
    actualClosureExtensionTwo V (actualHolderLoadSpaceTwo_value _ _ alpha
      (actualHolderLoadIsometricEquivTwo U V T hUV alpha f)) x=
      actualClosureExtensionTwo U (actualHolderLoadSpaceTwo_value _ _ alpha f) (T x) := by
  have hm : T x ∈ closure U := (actualIsometricClosureMapTwo U V T hUV ⟨x,hx⟩).property
  rw [actualClosureExtensionTwo_apply V _ hx,actualClosureExtensionTwo_apply U _ hm]
  exact actualHolderLoadIsometricEquivTwo_apply U V T hUV alpha f ⟨x,hx⟩

end PowerConvexity
