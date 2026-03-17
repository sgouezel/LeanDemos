import Mathlib

/-!
# Karlsson's proof of the existence of an asymptotic vector for semicontractions
-/

noncomputable section
namespace KarlssonEng

open Filter Function Metric
open scoped Topology

variable {α β : Type*} [MetricSpace α] [MetricSpace β]

lemma exists_high_score (u : ℕ → ℝ) (hu : Tendsto u atTop atTop) (N : ℕ) :
    ∃ n ≥ N, ∀ m ≤ n, u m ≤ u n := by
  sorry

/-- A semicontraction between two metric spaces is a map that does not increase distances. -/
def semicontraction (f : α → β) : Prop :=
  ∀ x y, dist (f x) (f y) ≤ dist x y

namespace semicontraction

lemma comp {γ : Type*} [MetricSpace γ] {g : β → γ} {f : α → β}
    (hg : semicontraction g) (hf : semicontraction f) :
    semicontraction (g ∘ f) :=
  sorry

lemma iterate {f : α → α} (h : semicontraction f) (n : ℕ) :
    semicontraction (f ^[n]) := by
  sorry

variable {E : Type*} [NormedAddCommGroup E]
  {f : E → E} (h : semicontraction f)
include h

/-- A convenient notation for the distance between `0` and `f^n 0`. -/
local notation "u" => (fun n ↦ dist (f^[n] 0) 0)

lemma u_subadditive : Subadditive u := by
  sorry

/-- `h.l` is such that `h.u n` grows like `n * h.l`. -/
def l := h.u_subadditive.lim

lemma tendsto_lim : Tendsto (fun n ↦ u n / n) atTop (𝓝 h.l) := by
  sorry

lemma l_nonneg : 0 ≤ h.l :=
  sorry

lemma tendsto_sub_atTop {w : ℝ} (hw : w < h.l) :
    Tendsto (fun (n : ℕ) ↦ u n - n * w) atTop atTop := by
  sorry

variable
  [InnerProductSpace ℝ E]

lemma exists_dual_up_to_of_lt {w : ℝ} (hw : w < h.l) (N : ℕ) :
    ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ - i * w := by
  sorry

variable [FiniteDimensional ℝ E]

lemma exists_dual : ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i, v (f^[i] 0) ≤ -i * h.l := by
  sorry
  -- We start from an increasing sequence `w_n` tending to `h.l`
  -- For each `n`, we can choose an element of the dual with norm at most `1`
  -- such that `y (f^[i] 0) ≤ - i w_n` for every `i ≤ n`, by the previous lemma
  -- Let us extract a converging subsequence `y_{φ n}`, tending to a limit `v`.
  -- we will see that this limit works.
  -- we have fixed `i`, we need to check that `v (f^[i] 0) ≤ -i h.l`.
  -- For this, we pass to the limit in the inequalities
  -- on `y_n (f^[i] 0)`.

open scoped RealInnerProductSpace

-- we convert the existence of a good linear form to the existence of
-- a good vector, as we are in a Euclidean space.
lemma exists_asymp_vector :
    ∃ (v : E), ‖v‖ ≤ 1 ∧ ∀ (i : ℕ), (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫ := by
  sorry

/-- A semicontraction on a finite-dimensional Euclidean vector space admits an asymptotic
translation vector. -/
theorem exists_tendsto_div :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / (n : ℝ)) • (f^[n] 0)) atTop (𝓝 v) := by
  sorry

omit h [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Beware: if one is not careful about the statements, one can give a correct trivial
proof of a stupid result. -/
lemma wrong_exists_tendsto_div' :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / n) • (f^[n] 0)) atTop (𝓝 v) :=
  sorry

end semicontraction

end KarlssonEng
