import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-! # Derivatives of an actual continuous-linear conjugacy -/
set_option autoImplicit false
noncomputable section
namespace PowerConvexity
variable {X Y V W : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem actual_derivative_intertwine_of_linear_conjugacy
    (P : X →L[ℝ] Y) (Q : V →L[ℝ] W) (f : X → V) (g : Y → W)
    (p : X) (L : X →L[ℝ] V) (K : Y →L[ℝ] W)
    (hf : HasFDerivAt f L p) (hg : HasFDerivAt g K (P p))
    (he : ∀ x, g (P x)=Q (f x)) : K.comp P=Q.comp L := by
  have hleft : HasFDerivAt (fun x => g (P x)) (K.comp P) p := hg.comp p P.hasFDerivAt
  have hright : HasFDerivAt (fun x => Q (f x)) (Q.comp L) p := Q.hasFDerivAt.comp p hf
  rw [show (fun x => g (P x))=(fun x => Q (f x)) from funext he] at hleft
  exact hleft.unique hright

end PowerConvexity
