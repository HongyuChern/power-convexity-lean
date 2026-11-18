import PowerConvexity.Calculus.ActualHolderC2JetLiftTwo

/-! # Bounded upgrade of the same actual C0 response into the complete C2 Holder space

The actual closure-jet estimate is an explicit hypothesis. This theorem does
not obtain that estimate from a C0 bound. It proves that once the estimate is
available, the unique lifted operator is linear, bounded, and has exactly the
same values as the original continuous response.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option synthInstance.maxSize 1024
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace PowerConvexity
open CHS.Calculus
attribute [local instance] atjInstance1 atjInstance2 atjInstance3 atjInstance4 atjInstance5 atjInstance6
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (U : Set E) [CompactSpace (closure U)]
local instance holderResponseJetSeminormedGroup (alpha : ℝ) :
    SeminormedAddCommGroup (actualHolderC2JetSpaceTwo U alpha) :=
  (inferInstance : NormedAddCommGroup (actualHolderC2JetSpaceTwo U alpha)).toSeminormedAddCommGroup

theorem actual_holder_response_bounded_lift_two (hU : IsOpen U) (alpha : ℝ)
    (T : C(closure U,ℝ) →L[ℝ] C(closure U,ℝ)) {C : ℝ} (hC : 0 ≤ C) (hT : ‖T‖ ≤ C)
    (hzero : ∀ f : C(closure U,ℝ), ∀ (x : E) (hx : x ∈ frontier U),
      T f ⟨x,frontier_subset_closure hx⟩=0)
    (hregular : ∀ f : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ContDiffOn ℝ 2 (actualClosureExtensionTwo U (T (actualHolderLoadSpaceTwo_value _ _ alpha f))) U)
    (hjet : ∀ f : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ∃ J : ClosureC2Jet (actualClosureExtensionTwo U (T (actualHolderLoadSpaceTwo_value _ _ alpha f))) U,
        (∀ x ∈ closure U, ‖J.derivative x‖ ≤ C*‖f‖ ∧ ‖J.hessian x‖ ≤ C*‖f‖) ∧
        ∀ x ∈ closure U, ∀ y ∈ closure U, ‖J.hessian x-J.hessian y‖ ≤ C*‖f‖*‖x-y‖^alpha) :
    ∃! S : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] actualHolderC2JetSpaceTwo U alpha,
      (actualHolderC2JetSpaceTwo_value U alpha).comp S=
        T.comp (actualHolderLoadSpaceTwo_value (closure U) ℝ alpha) ∧ ‖S‖ ≤ C := by
  classical
  let V := actualHolderLoadSpaceTwo_value (closure U) ℝ alpha
  let W := actualHolderC2JetSpaceTwo_value U alpha
  have hsolve : ∀ f : actualHolderLoadSpaceTwo (closure U) ℝ alpha,
      ∃ p : actualHolderC2JetSpaceTwo U alpha, W p=T (V f) ∧ ‖p‖ ≤ C*‖f‖ := by
    intro f
    obtain ⟨J,hb,hh⟩ := hjet f
    have hCf : 0 ≤ C*‖f‖ := mul_nonneg hC (norm_nonneg f)
    have hvalue : ∀ x ∈ closure U, |actualClosureExtensionTwo U (T (V f)) x| ≤ C*‖f‖ := by
      intro x hx
      rw [actualClosureExtensionTwo_apply U _ hx]
      change ‖T (V f) ⟨x,hx⟩‖ ≤ C*‖f‖
      exact ((T (V f)).norm_coe_le_norm ⟨x,hx⟩).trans
        ((T.le_opNorm (V f)).trans (mul_le_mul hT (actualHolderLoadSpaceTwo_value_norm_le _ _ alpha f)
          (norm_nonneg _) hC))
    obtain ⟨p,hp,_⟩ := actualHolderC2JetSpaceTwo_lift U hU alpha (hregular f) J
      (fun x hx => by rw [actualClosureExtensionTwo_apply U _ (frontier_subset_closure hx)]; exact hzero _ x hx)
      hCf (fun x hx => ⟨hvalue x hx,(hb x hx).1,(hb x hx).2⟩) hh
    refine ⟨p,?_,hp.2⟩
    apply hp.1.trans
    apply ContinuousMap.ext
    intro x
    exact actualClosureExtensionTwo_apply U _ x.property
  choose p hp using hsolve
  have hinj := actualHolderC2JetSpaceTwo_value_injective U hU alpha
  let L : actualHolderLoadSpaceTwo (closure U) ℝ alpha →ₗ[ℝ] actualHolderC2JetSpaceTwo U alpha :=
    { toFun := p
      map_add' := by
        intro f g
        apply hinj
        change W (p (f+g))=W (p f+p g)
        rw [(hp (f+g)).1]
        simp only [map_add,(hp f).1,(hp g).1]
      map_smul' := by
        intro c f
        apply hinj
        change W (p (c • f))=W (c • p f)
        rw [(hp (c • f)).1]
        simp only [map_smul,(hp f).1] }
  have hbound (f : actualHolderLoadSpaceTwo (closure U) ℝ alpha) : ‖L f‖ ≤ C*‖f‖ := (hp f).2
  let S := L.mkContinuous C hbound
  have hSv : W.comp S=T.comp V := by
    ext f x
    exact congrArg (fun g : C(closure U,ℝ) => g x) (hp f).1
  refine ⟨S,⟨hSv,L.mkContinuous_norm_le hC hbound⟩,?_⟩
  intro S' hS'
  apply ContinuousLinearMap.ext
  intro f
  apply hinj
  have hleft := congrArg (fun Q : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] C(closure U,ℝ) => Q f) hS'.1
  have hright := congrArg (fun Q : actualHolderLoadSpaceTwo (closure U) ℝ alpha →L[ℝ] C(closure U,ℝ) => Q f) hSv
  exact hleft.trans hright.symm

end PowerConvexity
