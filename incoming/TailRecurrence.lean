/-
  CatalanTail.TailRecurrence

  Formalizes the tail recurrence core from §1 of:
    Zhi-Wei Sun, "Catalan's constant is irrational" (arXiv:2609.04176v1)

  Definitions:
    T_m  = Σ_{r≥0} (-1)^r / (2(m+r)+1)²     (Catalan tail)
    u_m  = T_m / (2m+1)                        (weighted tail)

  Main result:
    T_m + T_{m+1} = 1/(2m+1)²                  (Sun eq. 1.4)

  Status: CAPABILITY-LIMITED — authored against Mathlib API but not
  kernel-verified in this session (lean-lang.org blocked by egress proxy).
  Two sorries remain: summability and positivity.
-/

import Mathlib

noncomputable section

namespace CatalanTail

open scoped Topology

/-! ### Helper: odd integers as reals -/

/-- `oddReal n` is `2n + 1` cast to `ℝ`. -/
def oddReal (n : ℕ) : ℝ := 2 * (n : ℝ) + 1

theorem oddReal_pos (n : ℕ) : (0 : ℝ) < oddReal n := by
  unfold oddReal; positivity

theorem oddReal_ne_zero (n : ℕ) : oddReal n ≠ 0 :=
  ne_of_gt (oddReal_pos n)

theorem oddReal_sq_pos (n : ℕ) : (0 : ℝ) < oddReal n ^ 2 :=
  sq_pos_of_pos (oddReal_pos n)

theorem oddReal_sq_ne_zero (n : ℕ) : oddReal n ^ 2 ≠ 0 :=
  ne_of_gt (oddReal_sq_pos n)

/-! ### Tail term -/

/-- The `r`-th term of the Catalan tail starting at index `m`:
    `tailTerm m r = (-1)^r / (2(m+r)+1)²`. -/
def tailTerm (m r : ℕ) : ℝ := (-1 : ℝ) ^ r / oddReal (m + r) ^ 2

@[simp]
theorem tailTerm_zero (m : ℕ) : tailTerm m 0 = 1 / oddReal m ^ 2 := by
  simp [tailTerm]

/-- Key shift identity: `tailTerm m (r+1) = -tailTerm (m+1) r`.
    Uses `m + (r+1) = (m+1) + r` and `(-1)^(r+1) = -(-1)^r`. -/
theorem tailTerm_shift (m r : ℕ) :
    tailTerm m (r + 1) = -tailTerm (m + 1) r := by
  simp only [tailTerm]
  have h : m + (r + 1) = (m + 1) + r := by omega
  rw [h, pow_succ]
  ring

/-! ### Summability -/

/-- The tail series is summable by comparison with `Σ 1/(2n+1)²`,
    which is dominated by `Σ 1/n²`.

    SORRY: Requires Mathlib's summability API for `1/n²`-type series
    and the comparison test. The argument is:
    `|tailTerm m r| = 1/(2(m+r)+1)² ≤ 1/(r+1)²` for suitable bounds,
    and `Σ 1/n²` converges. -/
theorem summable_tailTerm (m : ℕ) : Summable (tailTerm m) := by
  sorry

/-! ### Catalan tail and weighted tail -/

/-- The Catalan tail `T_m = Σ_{r≥0} (-1)^r / (2(m+r)+1)²`. -/
def tail (m : ℕ) : ℝ := ∑' r, tailTerm m r

/-- The weighted tail `u_m = T_m / (2m+1)`. -/
def weightedTail (m : ℕ) : ℝ := tail m / oddReal m

/-! ### The tail recurrence (Sun eq. 1.4) -/

/-- **Main theorem.** The Catalan tail recurrence:
    `T_m + T_{m+1} = 1/(2m+1)²`.

    Proof strategy:
    1. Split `T_m = tailTerm m 0 + Σ_{r≥0} tailTerm m (r+1)`
       via `tsum_eq_zero_add`.
    2. Apply `tailTerm_shift` under the sum to get
       `Σ tailTerm m (r+1) = -Σ tailTerm (m+1) r = -T_{m+1}`.
    3. Combine: `T_m = 1/(2m+1)² - T_{m+1}`. -/
theorem tail_add_succ (m : ℕ) :
    tail m + tail (m + 1) = 1 / oddReal m ^ 2 := by
  unfold tail
  rw [tsum_eq_zero_add (summable_tailTerm m)]
  have shift : ∑' r, tailTerm m (r + 1) = -(∑' r, tailTerm (m + 1) r) := by
    calc ∑' r, tailTerm m (r + 1)
        = ∑' r, -tailTerm (m + 1) r := tsum_congr (tailTerm_shift m)
      _ = -(∑' r, tailTerm (m + 1) r) := tsum_neg
  rw [shift, tailTerm_zero]
  linarith

/-- Rearranged form: `T_m = 1/(2m+1)² - T_{m+1}`. -/
theorem tail_eq_inv_sq_sub_succ (m : ℕ) :
    tail m = 1 / oddReal m ^ 2 - tail (m + 1) := by
  linarith [tail_add_succ m]

/-! ### Positivity and bounds -/

/-- `T_m > 0` for all `m`.

    SORRY: Requires a paired-term grouping argument for the alternating
    series. Group consecutive pairs `(r=2k, r=2k+1)`:
      1/(2(m+2k)+1)² - 1/(2(m+2k+1)+1)² > 0
    since denominators increase. Each pair is positive, and the partial
    sums are monotone increasing and bounded, giving `T_m > 0`. -/
theorem tail_pos (m : ℕ) : 0 < tail m := by
  sorry

/-- `T_m < 1/(2m+1)²`: the tail is strictly less than its first term. -/
theorem tail_lt_inv_sq (m : ℕ) :
    tail m < 1 / oddReal m ^ 2 := by
  rw [tail_eq_inv_sq_sub_succ]
  linarith [tail_pos (m + 1)]

/-- The weighted tail is positive. -/
theorem weightedTail_pos (m : ℕ) : 0 < weightedTail m :=
  div_pos (tail_pos m) (oddReal_pos m)

/-- The recurrence in the paper's notation:
    `T_m + T_{m+1} = 1/(2m+1)²` where `2m+1` is spelled out. -/
theorem tail_recurrence_paper_form (m : ℕ) :
    tail m + tail (m + 1) = 1 / (2 * (m : ℝ) + 1) ^ 2 := by
  convert tail_add_succ m using 2
  unfold oddReal; ring

end CatalanTail
