import PowerConvexity.Calculus.ConstantDensityGradient
import PowerConvexity.Calculus.ModifiedSecondDerivatives

/-! # Algebraic corrections in the four modified Schur residuals -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PowerConvexity
open CHS.SchurContractionCore
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two inverse matrices are kept in their correct order. This identity
removes the unmodified second derivative once its PDE product is supplied. -/
theorem contracted_modified_residual
    (W R T : Matrix ι ι ℂ) (X Y P Q : ι → Matrix ι ι ℂ)
    (S : ι → ι → Matrix ι ι ℂ) (L₀ L₁ : Matrix ι ι ℂ)
    (hbase : L₀ = contract W (fun p q => X q * R * Y p))
    (hcorrection : L₁ = L₀ + contract W S) :
    L₁ - contract W (fun p q => (X q + P q) * T * (Y p + Q p)) =
      contract W (fun p q => X q * (R-T) * Y p + S p q -
        P q * T * Y p - X q * T * Q p - P q * T * Q p) := by
  rw [hcorrection, hbase, ← contract_add, ← contract_sub]
  congr 1
  funext p q
  noncomm_ring

noncomputable def modificationAz (h : ℂ) (g : ι → ℂ) (A B : Matrix ι ι ℂ)
    (p : ι) : Matrix ι ι ℂ := fun i j =>
  h * star (g j) * B i p + h * g i * A p j

noncomputable def modificationAbar (h : ℂ) (g : ι → ℂ) (A B : Matrix ι ι ℂ)
    (q : ι) : Matrix ι ι ℂ := fun i j =>
  h * star (g j) * A i q + h * g i * star (B q j)

noncomputable def modificationBbar (h : ℂ) (g : ι → ℂ) (A : Matrix ι ι ℂ)
    (q : ι) : Matrix ι ι ℂ := fun i j =>
  h * g j * A i q + h * g i * A j q

/-- The seven algebraic terms of `2_2_12` after the two constant-density
third-derivative contractions vanish. -/
noncomputable def modificationASecond (h : ℂ) (g : ι → ℂ) (A B : Matrix ι ι ℂ)
    (p q : ι) : Matrix ι ι ℂ := fun i j =>
  h * B i p * star (B j q) + h * A i q * A p j +
    h^2 * g p * star (g j) * A i q +
    2*h^2 * g i * star (g j) * A p q +
    h^2 * g i * g p * star (B q j) +
    h^2 * star (g j) * star (g q) * B i p +
    h^2 * g i * star (g q) * A p j

/-- The seven algebraic terms following `2_2_15`, with no fourth derivatives. -/
noncomputable def modificationBSecond (h : ℂ) (g : ι → ℂ) (A B : Matrix ι ι ℂ)
    (p q : ι) : Matrix ι ι ℂ := fun i j =>
  h * A i q * B j p + h * A j q * B i p +
    h^2 * g p * g j * A i q + h^2 * g i * g p * A j q +
    2*h^2 * g i * g j * A p q +
    h^2 * g j * star (g q) * B i p + h^2 * g i * star (g q) * B j p

end PowerConvexity
