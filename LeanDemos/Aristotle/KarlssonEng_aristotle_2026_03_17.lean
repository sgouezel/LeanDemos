/-
This file was edited by Aristotle (https://aristotle.harmonic.fun).

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 3d494fdf-05d8-4d42-a503-8760d6b7e520

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma exists_high_score (u : ℕ → ℝ) (hu : Tendsto u atTop atTop) (N : ℕ) :
    ∃ n ≥ N, ∀ m ≤ n, u m ≤ u n

- lemma comp {γ : Type*} [MetricSpace γ] {g : β → γ} {f : α → β}
    (hg : semicontraction g) (hf : semicontraction f) :
    semicontraction (g ∘ f)

- lemma iterate {f : α → α} (h : semicontraction f) (n : ℕ) :
    semicontraction (f ^[n])

- lemma u_subadditive : Subadditive u

- lemma tendsto_lim : Tendsto (fun n ↦ u n / n) atTop (𝓝 h.l)

- lemma l_nonneg : 0 ≤ h.l

- lemma tendsto_sub_atTop {w : ℝ} (hw : w < h.l) :
    Tendsto (fun (n : ℕ) ↦ u n - n * w) atTop atTop

- lemma exists_dual_up_to_of_lt {w : ℝ} (hw : w < h.l) (N : ℕ) :
    ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ - i * w

- lemma exists_dual : ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i, v (f^[i] 0) ≤ -i * h.l

- lemma exists_asymp_vector :
    ∃ (v : E), ‖v‖ ≤ 1 ∧ ∀ (i : ℕ), (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫

- theorem exists_tendsto_div :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / (n : ℝ)) • (f^[n] 0)) atTop (𝓝 v)

- lemma wrong_exists_tendsto_div' :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / n) • (f^[n] 0)) atTop (𝓝 v)
-/

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
  -- Since $u$ tends to infinity, there exists some $M$ such that $u(M)$ is the maximum value of $u$ up to $M$.
  obtain ⟨M, hM⟩ : ∃ M, ∀ m ≤ M, u m ≤ u M := by
    exact ⟨ 0, fun m hm => by aesop ⟩;
  induction' N with N ih;
  · exact ⟨ M, Nat.zero_le _, hM ⟩;
  · obtain ⟨ n, hn₁, hn₂ ⟩ := ih;
    -- Since $u$ tends to infinity, there exists some $k > n$ such that $u k > u n$.
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k > n, u k > u n := by
      exact Filter.eventually_atTop.mp ( hu.eventually_gt_atTop ( u n ) ) |> fun ⟨ k, hk ⟩ => ⟨ k + n + 1, by linarith, hk _ <| by linarith ⟩;
    -- Let $m$ be the smallest index greater than $n$ such that $u m > u n$.
    obtain ⟨m, hm₁, hm₂⟩ : ∃ m > n, u m > u n ∧ ∀ l > n, l < m → u l ≤ u n := by
      exact ⟨ Nat.find ( ⟨ k, hk₁, hk₂ ⟩ : ∃ m > n, u m > u n ), Nat.find_spec ( ⟨ k, hk₁, hk₂ ⟩ : ∃ m > n, u m > u n ) |>.1, Nat.find_spec ( ⟨ k, hk₁, hk₂ ⟩ : ∃ m > n, u m > u n ) |>.2, by aesop ⟩;
    use m;
    grind

/-- A semicontraction between two metric spaces is a map that does not increase distances. -/
def semicontraction (f : α → β) : Prop :=
  ∀ x y, dist (f x) (f y) ≤ dist x y

namespace semicontraction

lemma comp {γ : Type*} [MetricSpace γ] {g : β → γ} {f : α → β}
    (hg : semicontraction g) (hf : semicontraction f) :
    semicontraction (g ∘ f) :=
  by
    -- By definition of semicontraction, we need to show that for all x y in α, dist (g (f x)) (g (f y)) ≤ dist x y.
    intros x y
    have h1 : dist (g (f x)) (g (f y)) ≤ dist (f x) (f y) := by
      -- Apply the semicontraction property of $g$ to the points $f(x)$ and $f(y)$.
      apply hg
    have h2 : dist (f x) (f y) ≤ dist x y := by
      -- By definition of semicontraction, we have dist (f x) (f y) ≤ dist x y.
      apply hf
    exact le_trans h1 h2

lemma iterate {f : α → α} (h : semicontraction f) (n : ℕ) :
    semicontraction (f ^[n]) := by
  -- By induction on $n$, we can show that $f^[n]$ is a semicontraction.
  induction' n with n ih;
  · -- The identity function is a semicontraction because the distance between any two points is preserved.
    simp [KarlssonEng.semicontraction];
  · -- By the properties of semicontractions, the composition of two semicontractions is also a semicontraction.
    have h_comp : ∀ {g : α → α} {h : α → α}, semicontraction g → semicontraction h → semicontraction (g ∘ h) := by
      -- By the properties of semicontractions, the composition of two semicontractions is also a semicontraction. This follows directly from the definition of semicontraction.
      intros g h hg hh
      apply KarlssonEng.semicontraction.comp hg hh;
    -- By the properties of semicontractions, the composition of two semicontractions is also a semicontraction. Therefore, we can apply the induction hypothesis and the fact that $f$ is a semicontraction.
    apply h_comp ih h

variable {E : Type*} [NormedAddCommGroup E]
  {f : E → E} (h : semicontraction f)

include h

/-- A convenient notation for the distance between `0` and `f^n 0`. -/
local notation "u" => (fun n ↦ dist (f^[n] 0) 0)

lemma u_subadditive : Subadditive u := by
  -- By the semicontraction property, we have dist(f^[m+n] 0, 0) ≤ dist(f^[m] 0, 0) + dist(f^[n] 0, 0).
  have h_subadd : ∀ m n, dist (f^[m+n] 0) 0 ≤ dist (f^[m] 0) 0 + dist (f^[n] 0) 0 := by
    intro m n; rw [ Function.iterate_add_apply ] ; exact (by
    -- By the semicontraction property, we have dist(f^[m] (f^[n] 0), f^[m] 0) ≤ dist(f^[n] 0, 0).
    have h_semicontraction : dist (f^[m] (f^[n] 0)) (f^[m] 0) ≤ dist (f^[n] 0) 0 := by
      induction' m with m ih generalizing n <;> simp_all +decide [ Function.iterate_succ_apply', dist_comm ];
      exact le_trans ( h _ _ ) ( ih _ );
    exact le_trans ( dist_triangle _ _ _ ) ( by linarith ));
  exact fun m n => h_subadd m n

/-- `h.l` is such that `h.u n` grows like `n * h.l`. -/
def l := h.u_subadditive.lim

lemma tendsto_lim : Tendsto (fun n ↦ u n / n) atTop (𝓝 h.l) := by
  convert h.u_subadditive.tendsto_lim using 1;
  -- By Fekete's lemma, since the sequence is subadditive and bounded below, it converges to its infimum.
  apply Iff.intro;
  · exact?;
  · intro h_fekete
    have h_bdd_below : BddBelow (Set.range (fun n => dist (f^[n] 0) 0 / (n : ℝ))) := by
      exact ⟨ 0, Set.forall_mem_range.2 fun n => div_nonneg ( dist_nonneg ) ( Nat.cast_nonneg _ ) ⟩;
    convert h_fekete h_bdd_below using 1

lemma l_nonneg : 0 ≤ h.l :=
  by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds h.tendsto_lim;
    -- Since distances are non-negative, dividing by a positive integer preserves the non-negativity.
    intros x
    apply div_nonneg (dist_nonneg) (Nat.cast_nonneg x)

lemma tendsto_sub_atTop {w : ℝ} (hw : w < h.l) :
    Tendsto (fun (n : ℕ) ↦ u n - n * w) atTop atTop := by
  have h_seq : Filter.Tendsto (fun n => ((fun n => dist (f^[n] 0) 0) n - n * w) / n) Filter.atTop (nhds (h.l - w)) := by
    have h_seq : Filter.Tendsto (fun n => ((fun n => dist (f^[n] 0) 0) n) / n) Filter.atTop (nhds h.l) := by
      exact?;
    simpa [ sub_div ] using h_seq.sub ( tendsto_const_nhds.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; simp +decide [ hn ] ) );
  have h_seq : Filter.Tendsto (fun n => ((fun n => dist (f^[n] 0) 0) n - n * w) / n * n) Filter.atTop Filter.atTop := by
    apply Filter.Tendsto.pos_mul_atTop;
    exacts [ sub_pos.mpr hw, h_seq, tendsto_natCast_atTop_atTop ];
  exact h_seq.congr' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; rw [ div_mul_cancel₀ _ ( Nat.cast_ne_zero.mpr hn ) ] )

variable
  [InnerProductSpace ℝ E]

lemma exists_dual_up_to_of_lt {w : ℝ} (hw : w < h.l) (N : ℕ) :
    ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ - i * w := by
  -- Assume $w \ge 0$. Then $l > w \ge 0$, so $l > 0$.
  by_cases hw_nonneg : w ≥ 0;
  · -- Let $a_n = u_n - n w$. By `tendsto_sub_atTop`, $a_n \to \infty$.
    set a : ℕ → ℝ := fun n => (dist (f^[n] 0) 0) - n * w
    have ha_tendsto : Filter.Tendsto a Filter.atTop Filter.atTop := by
      convert KarlssonEng.semicontraction.tendsto_sub_atTop _ hw using 1;
    -- Apply `exists_high_score` to $a_n$ with a large enough start index (larger than $N$ and large enough such that $u_n > 0$) to find $n$ such that $a_m \le a_n$ for all $m \le n$.
    obtain ⟨n, hn₁, hn₂⟩ : ∃ n ≥ N + 1, ∀ m ≤ n, a m ≤ a n ∧ 0 < dist (f^[n] 0) 0 := by
      -- Since $a$ tends to infinity, there exists some $M$ such that for all $m \geq M$, $a m$ is positive.
      obtain ⟨M, hM⟩ : ∃ M, ∀ m ≥ M, 0 < a m := by
        exact Filter.eventually_atTop.mp ( ha_tendsto.eventually_gt_atTop 0 );
      -- Apply `exists_high_score` with $N + M + 1$ as the start index.
      obtain ⟨n, hn₁, hn₂⟩ : ∃ n ≥ N + M + 1, ∀ m ≤ n, a m ≤ a n := by
        have := exists_high_score a ha_tendsto ( N + M + 1 ) ; aesop;
      exact ⟨ n, by linarith, fun m hm => ⟨ hn₂ m hm, by have := hM n ( by linarith ) ; exact lt_of_not_ge fun h => this.not_ge <| sub_nonpos_of_le <| by nlinarith ⟩ ⟩;
    -- Define $v \in E^*$ by $v(x) = -\frac{\langle x, f^n 0 \rangle}{u_n}$. Then $\|v\| = 1$.
    obtain ⟨v, hv⟩ : ∃ v : E →L[ℝ] ℝ, ‖v‖ ≤ 1 ∧ ∀ x, v x = - (inner ℝ x (f^[n] 0)) / dist (f^[n] 0) 0 := by
      refine' ⟨ _, _, _ ⟩;
      refine' ( innerSL ℝ ( f^[n] 0 ) |> ContinuousLinearMap.smulRight <| -1 / Dist.dist ( f^[n] 0 ) 0 );
      · refine' ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => _;
        simp +decide [ div_eq_inv_mul, norm_smul ];
        exact div_le_of_le_mul₀ ( norm_nonneg _ ) ( norm_nonneg _ ) ( by simpa [ mul_comm ] using abs_real_inner_le_norm ( f^[n] 0 ) x );
      · simp +decide [ div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm, innerSL_apply ];
        exact fun x => Or.inl ( real_inner_comm _ _ );
    refine' ⟨ v, hv.1, fun i hi => _ ⟩;
    -- Using the polarization identity, we have $2 \langle f^i 0, f^n 0 \rangle = u_i^2 + u_n^2 - \|f^i 0 - f^n 0\|^2 \ge u_i^2 + u_n^2 - u_{n-i}^2$.
    have h_polarization : 2 * inner ℝ (f^[i] 0) (f^[n] 0) ≥ (dist (f^[i] 0) 0)^2 + (dist (f^[n] 0) 0)^2 - (dist (f^[n-i] 0) 0)^2 := by
      have h_polarization : ‖f^[i] 0 - f^[n] 0‖^2 ≤ ‖f^[n-i] 0‖^2 := by
        have h_dist : dist (f^[i] 0) (f^[n] 0) ≤ dist (f^[0] 0) (f^[n-i] 0) := by
          convert h.iterate i ( f^[0] 0 ) ( f^[n-i] 0 ) using 1 ; simp +decide [ ← Function.iterate_add_apply, Nat.add_sub_of_le ( by linarith : i ≤ n ) ];
        simpa [ dist_eq_norm ] using pow_le_pow_left₀ ( dist_nonneg ) h_dist 2;
      simp_all +decide [ dist_eq_norm, norm_sub_sq_real ];
      linarith;
    -- From the high score property, $a_{n-i} \le a_n \implies u_{n-i} - (n-i) w \le u_n - n w \implies \delta = u_n - u_{n-i} \ge i w$.
    have h_delta : dist (f^[n] 0) 0 - dist (f^[n-i] 0) 0 ≥ i * w := by
      simp +zetaDelta at *;
      have := hn₂ ( n - i ) ( Nat.sub_le _ _ ) ; rw [ Nat.cast_sub ( by linarith ) ] at *; linarith;
    -- From subadditivity, $u_n \le u_{n-i} + u_i \implies \delta \le u_i$.
    have h_delta_le : dist (f^[n] 0) 0 - dist (f^[n-i] 0) 0 ≤ dist (f^[i] 0) 0 := by
      have h_subadd : dist (f^[n] 0) 0 ≤ dist (f^[n-i] 0) 0 + dist (f^[i] 0) 0 := by
        rw [ show f^[n] 0 = f^[n-i] ( f^[i] 0 ) by rw [ ← Function.iterate_add_apply, Nat.sub_add_cancel ( by linarith ) ] ];
        have h_subadd : ∀ m : ℕ, dist (f^[m] (f^[i] 0)) (f^[m] 0) ≤ dist (f^[i] 0) 0 := by
          intro m; induction' m with m ih <;> simp_all +decide [ Function.iterate_succ_apply', dist_triangle ] ;
          exact le_trans ( h _ _ ) ih;
        exact le_trans ( dist_triangle _ _ _ ) ( by linarith [ h_subadd ( n - i ) ] );
      linarith;
    rw [ hv.2, div_le_iff₀ ] <;> nlinarith [ hn₂ n le_rfl, show ( 0 : ℝ ) ≤ i * w by positivity ];
  · exact ⟨ 0, by norm_num, fun i hi => by simpa using by nlinarith ⟩

variable [FiniteDimensional ℝ E]

lemma exists_dual : ∃ (v : StrongDual ℝ E), ‖v‖ ≤ 1 ∧ ∀ i, v (f^[i] 0) ≤ -i * h.l := by
  -- By the properties of the supremum, there exists a vector $v$ such that $v(f^n(0)) \leq -n \cdot h.l$ for all $n$. Use the lemma `exists_dual_up_to_of_lt` with $w = h.l$.
  have h_sup : ∀ N : ℕ, ∃ v : StrongDual ℝ E, ‖v‖ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ -i * h.l := by
    intro N
    by_contra h_contra
    push_neg at h_contra
    have h_seq : ∀ k : ℕ, ∃ v : StrongDual ℝ E, ‖v‖ ≤ 1 ∧ ∀ i ≤ N, v (f^[i] 0) ≤ -i * (h.l - 1 / (k + 1)) := by
      intro k
      generalize_proofs at *;
      have := h.exists_dual_up_to_of_lt ( show h.l - 1 / ( k + 1 ) < h.l from sub_lt_self _ <| by positivity ) N
      generalize_proofs at *;
      exact this
    generalize_proofs at *;
    choose v hv using h_seq
    have h_compact : IsCompact (Metric.closedBall (0 : StrongDual ℝ E) 1) := by
      exact ProperSpace.isCompact_closedBall _ _
    generalize_proofs at *; (
    -- By the properties of the sequence $v_k$, we can extract a convergent subsequence.
    obtain ⟨w, hw⟩ : ∃ w : StrongDual ℝ E, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ Filter.Tendsto (fun k => v (subseq k)) Filter.atTop (nhds w) := by
      have := h_compact.isSeqCompact fun k => show v k ∈ Metric.closedBall 0 1 from by simpa using hv k |>.1; ; aesop;
    generalize_proofs at *; (
    obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hw
    have h_lim : ∀ i ≤ N, w (f^[i] 0) ≤ -i * h.l := by
      intro i hi
      have h_lim_i : Filter.Tendsto (fun k => v (subseq k) (f^[i] 0)) Filter.atTop (nhds (w (f^[i] 0))) := by
        exact Filter.Tendsto.comp ( Continuous.tendsto ( show Continuous fun x : StrongDual ℝ E => x ( f^[i] 0 ) from by continuity ) _ ) hsubseq₂
      generalize_proofs at *; (
      exact le_of_tendsto_of_tendsto' h_lim_i ( by simpa using tendsto_const_nhds.neg.mul ( tendsto_const_nhds.sub ( tendsto_one_div_add_atTop_nhds_zero_nat.comp hsubseq₁.tendsto_atTop ) ) ) fun k => hv ( subseq k ) |>.2 i hi |> le_trans <| by ring_nf; norm_num;)
    generalize_proofs at *; (
    exact absurd ( h_contra w ( by exact le_of_tendsto' ( hsubseq₂.norm ) fun k => hv ( subseq k ) |>.1 ) ) ( by push_neg; exact h_lim ))));
  -- Since the unit ball is compact in the weak* topology, we can extract a convergent subsequence from the sequence of functionals.
  obtain ⟨v, hv⟩ : ∃ v : StrongDual ℝ E, ∃ (s : ℕ → ℕ), StrictMono s ∧ Filter.Tendsto (fun n => (h_sup (s n)).choose) Filter.atTop (nhds v) := by
    have h_compact : IsCompact (Metric.closedBall (0 : StrongDual ℝ E) 1) := by
      exact ProperSpace.isCompact_closedBall _ _
    generalize_proofs at *; (
    have := h_compact.isSeqCompact fun n => show ( h_sup n |> Exists.choose ) ∈ Metric.closedBall 0 1 from by simpa using ( h_sup n |> Exists.choose_spec |> And.left ) ; ; aesop;);
  obtain ⟨ s, hs₁, hs₂ ⟩ := hv;
  refine' ⟨ v, _, _ ⟩;
  · exact le_of_tendsto' ( hs₂.norm ) fun n => ( h_sup ( s n ) |> Exists.choose_spec |> And.left );
  · intro i
    have h_lim : Filter.Tendsto (fun n => (h_sup (s n)).choose (f^[i] 0)) Filter.atTop (nhds (v (f^[i] 0))) := by
      exact Filter.Tendsto.comp ( Continuous.tendsto ( show Continuous fun x : StrongDual ℝ E => x ( f^[i] 0 ) from by continuity ) _ ) hs₂;
    exact le_of_tendsto h_lim ( Filter.eventually_atTop.mpr ⟨ i, fun n hn => ( h_sup ( s n ) |> Exists.choose_spec |> And.right ) i ( hn.trans ( hs₁.id_le _ ) ) ⟩ )

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
  -- Let $v$ be the linear form obtained from the previous lemma.
  obtain ⟨v, hv_norm, hv⟩ : ∃ v : StrongDual ℝ E, ‖v‖ ≤ 1 ∧ ∀ i, v (f^[i] 0) ≤ -i * h.l := by
    exact?;
  -- By the Riesz representation theorem, there exists a unique vector $v$ such that $v(x) = \langle v, x \rangle$ for all $x \in E$.
  obtain ⟨v', hv'_riesz⟩ : ∃ v' : E, ∀ x : E, v x = inner ℝ v' x := by
    exact ⟨ ( LinearIsometryEquiv.symm ( InnerProductSpace.toDual ℝ E ) ) v, fun x => by simp +decide ⟩;
  refine' ⟨ -v', _, _ ⟩ <;> simp_all +decide [ norm_neg ];
  · convert hv_norm using 1
    have : ‖v‖ = ‖(innerSL ℝ v')‖ := by
      congr ; ext ; aesop
    rw [this];
    exact?;
  · exact fun i => by linarith [ hv i ] ;

/-- A semicontraction on a finite-dimensional Euclidean vector space admits an asymptotic
translation vector. -/
theorem exists_tendsto_div :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / (n : ℝ)) • (f^[n] 0)) atTop (𝓝 v) := by
  by_contra! h_contra;
  -- By the definition of subadditivity, the sequence $(u_n / n)$ converges to $l$.
  have h_conv : Filter.Tendsto (fun n : ℕ => (dist (f^[n] 0) 0) / (n : ℝ)) Filter.atTop (nhds (h.l)) := by
    exact?;
  -- Let $v$ be the asymptotic translation vector.
  obtain ⟨v, hv⟩ : ∃ v : E, ‖v‖ ≤ 1 ∧ ∀ i : ℕ, (i : ℝ) * h.l ≤ ⟪v, (f^[i] 0)⟫ := by
    convert exists_asymp_vector h using 1;
  -- By the properties of the inner product and the definition of $v$, we have that $\|f^n(0) - n \cdot l \cdot v\|^2 \leq \|f^n(0)\|^2 - n^2 \cdot l^2$.
  have h_norm_sq : ∀ n : ℕ, ‖f^[n] 0 - (n : ℝ) • (h.l • v)‖^2 ≤ ‖f^[n] 0‖^2 - (n : ℝ)^2 * h.l^2 := by
    intro n
    have h_inner : ⟪f^[n] 0, (n : ℝ) • (h.l • v)⟫ ≥ (n : ℝ)^2 * h.l^2 := by
      simp_all +decide [ inner_smul_left, inner_smul_right ];
      rw [ real_inner_comm ] ; nlinarith [ hv.2 n, show ( 0 : ℝ ) ≤ n * h.l by exact mul_nonneg ( Nat.cast_nonneg _ ) ( show ( 0 : ℝ ) ≤ h.l by exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_conv fun n => by positivity ) ] ;
    rw [ @norm_sub_sq ℝ ];
    simp_all +decide [ norm_smul, inner_smul_right ];
    rw [ abs_of_nonneg ( show 0 ≤ h.l by exact le_of_tendsto_of_tendsto' tendsto_const_nhds h_conv fun n => by positivity ) ] ; nlinarith [ show ( n : ℝ ) ^ 2 * h.l ^ 2 ≥ 0 by positivity, show ( n : ℝ ) ^ 2 * h.l ^ 2 * ‖v‖ ^ 2 ≤ ( n : ℝ ) ^ 2 * h.l ^ 2 by exact mul_le_of_le_one_right ( by positivity ) ( pow_le_one₀ ( by positivity ) hv.1 ) ] ;
  -- Dividing both sides of the inequality by $n^2$, we get $\left\|\frac{f^n(0)}{n} - l \cdot v\right\|^2 \leq \left(\frac{\|f^n(0)\|}{n}\right)^2 - l^2$.
  have h_div : ∀ n : ℕ, n ≠ 0 → ‖(1 / (n : ℝ)) • f^[n] 0 - h.l • v‖^2 ≤ ((dist (f^[n] 0) 0) / (n : ℝ))^2 - h.l^2 := by
    intro n hn_ne; specialize h_norm_sq n; simp_all +decide [ div_eq_inv_mul, norm_smul, mul_pow ] ;
    convert mul_le_mul_of_nonneg_left h_norm_sq ( inv_nonneg.2 ( sq_nonneg ( n : ℝ ) ) ) using 1 ; ring;
    · rw [ show ( n : ℝ ) ⁻¹ • f^[n] 0 - h.l • v = ( n : ℝ ) ⁻¹ • ( f^[n] 0 - ( n : ℝ ) • h.l • v ) by simp +decide [ hn_ne, smul_sub, smul_smul ], norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg ( by positivity : ( 0 : ℝ ) ≤ n ) ] ; ring;
    · field_simp;
  -- Taking the limit as $n \to \infty$, we get $\left\|\frac{f^n(0)}{n} - l \cdot v\right\|^2 \leq l^2 - l^2 = 0$.
  have h_lim : Filter.Tendsto (fun n : ℕ => ‖(1 / (n : ℝ)) • f^[n] 0 - h.l • v‖^2) Filter.atTop (nhds 0) := by
    have h_lim : Filter.Tendsto (fun n : ℕ => ((dist (f^[n] 0) 0) / (n : ℝ))^2 - h.l^2) Filter.atTop (nhds 0) := by
      convert Filter.Tendsto.sub ( h_conv.pow 2 ) tendsto_const_nhds using 2 ; ring;
    exact squeeze_zero_norm' ( by filter_upwards [ Filter.eventually_ne_atTop 0 ] with n hn; simpa using h_div n hn ) h_lim;
  -- Since the square of the norm tends to zero, the norm itself must tend to zero.
  have h_norm_zero : Filter.Tendsto (fun n : ℕ => ‖(1 / (n : ℝ)) • f^[n] 0 - h.l • v‖) Filter.atTop (nhds 0) := by
    simpa [ Real.sqrt_sq_eq_abs ] using h_lim.sqrt;
  exact h_contra ( h.l • v ) ( tendsto_iff_norm_sub_tendsto_zero.mpr h_norm_zero )

omit h [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Beware: if one is not careful about the statements, one can give a correct trivial
proof of a stupid result. -/
lemma wrong_exists_tendsto_div' :
    ∃ (v : E), Tendsto (fun (n : ℕ) ↦ (1 / n) • (f^[n] 0)) atTop (𝓝 v) :=
  by
    by_contra! h;
    -- Apply the contradiction assumption to find the contradiction.
    apply h 0 (by
    refine' tendsto_const_nhds.congr' _;
    filter_upwards [ Filter.eventually_gt_atTop 1 ] with n hn using by rw [ Nat.succ_div ] ; aesop;)

end semicontraction

end KarlssonEng
