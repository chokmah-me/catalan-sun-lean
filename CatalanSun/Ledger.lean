/-
  CatalanSun/Ledger.lean

  P4 targets from Sun arXiv:2609.04176v1 asymptotic ledger (§§8–9):
  * raw quadratic coefficient `4ρ − 2ρ²` at `ρ = 1/20` equals `39/200`
  * large-prime gain `Δ_{>B} = (2/3)ρ + (1/2)ρ²` at `ρ = 1/20` equals `83/2400`
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Exact ledger identities (P4)

Rational arithmetic from the paper's final coefficient ledger. Independent of
the residual-matrix construction.
-/

namespace CatalanSun.Ledger

/-- Paper parameter ratio `ρ = S/B`, specialized at `1/20`. -/
def rho : ℚ := 1 / 20

/-- Raw quadratic coefficient from Stirling / Cauchy–tail baseline (eq. 9.4). -/
def rawQuadratic (ρ : ℚ) : ℚ := 4 * ρ - 2 * ρ ^ 2

/-- Exact large-prime improvement `Δ_{>B}` (eq. 8.4). -/
def deltaLarge (ρ : ℚ) : ℚ := (2 / 3) * ρ + (1 / 2) * ρ ^ 2

/-- Equation (9.4) at `ρ = 1/20`: `4ρ − 2ρ² = 39/200`. -/
theorem rawQuadratic_at_one_twentieth : rawQuadratic (1 / 20) = 39 / 200 := by
  unfold rawQuadratic
  norm_num

/-- Equation (8.5): at `ρ = 1/20`, `Δ_{>B} = 83/2400`. -/
theorem deltaLarge_at_one_twentieth : deltaLarge (1 / 20) = 83 / 2400 := by
  unfold deltaLarge
  norm_num

/-- Same identities via the named constant `rho`. -/
theorem rawQuadratic_rho : rawQuadratic rho = 39 / 200 := by
  simpa [rho] using rawQuadratic_at_one_twentieth

theorem deltaLarge_rho : deltaLarge rho = 83 / 2400 := by
  simpa [rho] using deltaLarge_at_one_twentieth

/-- Algebraic identity underlying (8.4), independent of the specialization. -/
theorem deltaLarge_eq (ρ : ℚ) : deltaLarge ρ = (2 * ρ) / 3 + ρ ^ 2 / 2 := by
  unfold deltaLarge
  ring

/-- Algebraic identity underlying (9.4). -/
theorem rawQuadratic_eq (ρ : ℚ) : rawQuadratic ρ = 2 * ρ * (2 - ρ) := by
  unfold rawQuadratic
  ring

end CatalanSun.Ledger
