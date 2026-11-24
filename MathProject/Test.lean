import MathProject.Basic

/-!
# Test: a continuous function on a closed interval attains its maximum

A nonstandard proof built on `Ultra` from `Basic.lean`, with the index set `ℕ` and a free
ultrafilter `U`:

1. At stage `n`, sample `[a, b]` at the `n + 2` equally spaced points `grid a b n k`.
   For a nonstandard `N` (stage `[n ↦ n]`) this is a hyperfine grid.
2. At each stage the grid is finite, so `f` has a largest value there; collecting the chosen
   points gives the nonstandard maximiser `X = ⟦n ↦ gridMax n⟧ᵤ`.
3. `X` is limited, so it has a standard part `c ∈ [a, b]`.
4. Every standard `y ∈ [a, b]` is infinitely close to a grid point `Y`, and `f Y ≤ f X`.
   By continuity, `f y ≈ f Y` and `f X ≈ f c`; taking standard parts gives `f y ≤ f c`.
-/

open Set Filter Topology

noncomputable section

namespace Ultra

variable {I : Type} {U : Ultrafilter I}

/-! ## Statements index by index (Łoś for application and `<`) -/

/-- Application of classes of functions to classes of points is computed index by index. -/
theorem app_ofFun {α β : Type} (f : I → α → β) (g : I → α) :
    app (ofFun (U := U) f) (ofFun g) = ofFun (fun i ↦ f i (g i)) := by
  apply Quotient.sound
  show ∀ᶠ i in (U : Filter I), _
  exact Eventually.of_forall fun _ _ _ ↦ rfl

/-- A class of propositions has standard part `True` exactly when the propositions hold for
`U`-almost every index. -/
theorem std_ofFun_iff (P : I → Prop) :
    std (ofFun (U := U) P) ↔ ∀ᶠ i in (U : Filter I), P i := by
  by_cases h : ∀ᶠ i in (U : Filter I), P i
  · have e : ofFun (U := U) P = lift True := by
      apply Quotient.sound
      show ∀ᶠ i in (U : Filter I), _
      filter_upwards [h] with i hi
      intro _ _
      exact eq_true hi
    rw [e, show std (lift (U := U) True) = True from liftFin.symm_apply_apply True]
    exact iff_of_true trivial h
  · have h' : ∀ᶠ i in (U : Filter I), ¬ P i := Ultrafilter.eventually_not.mpr h
    have e : ofFun (U := U) P = lift False := by
      apply Quotient.sound
      show ∀ᶠ i in (U : Filter I), _
      filter_upwards [h'] with i hi
      intro _ _
      exact eq_false hi
    rw [e, show std (lift (U := U) False) = False from liftFin.symm_apply_apply False]
    exact iff_of_false id h

/-- Łoś for `<`: `[f] < [g]` holds exactly when `f i < g i` for `U`-almost every `i`. -/
theorem ofFun_lt_ofFun {α : Type} [LT α] (f g : I → α) :
    (ofFun (U := U) f) < ofFun g ↔ ∀ᶠ i in (U : Filter I), f i < g i := by
  show std (app (app (lift (LT.lt : α → α → Prop)) (ofFun f)) (ofFun g)) ↔ _
  rw [show (lift (U := U) (LT.lt : α → α → Prop)) = ofFun (fun _ ↦ LT.lt) from rfl,
    app_ofFun, app_ofFun]
  exact std_ofFun_iff _

/-- Applying a standard function `f` to `[x]` gives `[f ∘ x]`. -/
theorem app_lift_ofFun {α β : Type} (f : α → β) (x : I → α) :
    app (lift (U := U) f) (ofFun x) = ofFun (f ∘ x) :=
  app_ofFun _ _

/-! ## Standard part -/

/-- `x` is infinitely close to the real number `c`: it lies strictly between `c - ε` and
`c + ε` for every standard `ε > 0`. -/
def IsSt (x : Ultra U ℝ) (c : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → lift (c - ε) < x ∧ x < lift (c + ε)

/-- For a class `[x]`, being infinitely close to `c` is convergence of `x` to `c` along `U`. -/
theorem isSt_ofFun_iff (x : I → ℝ) (c : ℝ) :
    IsSt (ofFun (U := U) x) c ↔ Tendsto x (U : Filter I) (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  refine forall₂_congr fun ε _ ↦ ?_
  change (ofFun (fun _ ↦ c - ε) < ofFun x ∧ ofFun x < ofFun (fun _ ↦ c + ε)) ↔ _
  rw [ofFun_lt_ofFun, ofFun_lt_ofFun, ← eventually_and]
  refine eventually_congr (Eventually.of_forall fun i ↦ ?_)
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- Every element of `∗[a, b]` has a standard part in `[a, b]` (compactness of `[a, b]`). -/
theorem exists_isSt_of_mem_Icc {a b : ℝ} (x : I → ℝ) (hx : ∀ i, x i ∈ Icc a b) :
    ∃ c ∈ Icc a b, IsSt (ofFun (U := U) x) c := by
  obtain ⟨c, hc, hle⟩ := isCompact_Icc.ultrafilter_le_nhds (U.map x)
    (le_principal_iff.mpr (Filter.mem_map.mpr (Eventually.of_forall hx)))
  exact ⟨c, hc, (isSt_ofFun_iff x c).mpr hle⟩

/-- Continuity, nonstandard form: if `x ≈ c` inside `s` and `f` is continuous at `c` within
`s`, then `f x ≈ f c`. -/
theorem isSt_comp {s : Set ℝ} {f : ℝ → ℝ} {c : ℝ} (hf : ContinuousWithinAt f s c)
    (x : I → ℝ) (hx : ∀ i, x i ∈ s) (h : IsSt (ofFun (U := U) x) c) :
    IsSt (app (lift f) (ofFun (U := U) x)) (f c) := by
  rw [app_lift_ofFun, isSt_ofFun_iff] at *
  exact hf.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨h, Eventually.of_forall hx⟩)

/-- Standard parts preserve `≤`: if `y ≤ x` for `U`-almost every index, `x ≈ r` and `y ≈ s`,
then `s ≤ r`. -/
theorem isSt_le {x y : I → ℝ} {r s : ℝ} (hx : IsSt (ofFun (U := U) x) r)
    (hy : IsSt (ofFun (U := U) y) s) (hle : ∀ᶠ i in (U : Filter I), y i ≤ x i) : s ≤ r := by
  rw [isSt_ofFun_iff] at hx hy
  exact le_of_tendsto_of_tendsto hy hx hle

end Ultra

/-! ## The grid and the hyperfinite maximiser -/

open Ultra

variable {a b y : ℝ}

/-- The `k`-th of the `n + 2` equally spaced points `a = t₀ < ⋯ < t_{n+1} = b`. -/
def grid (a b : ℝ) (n k : ℕ) : ℝ := a + k * ((b - a) / (n + 1))

theorem grid_mem (hab : a ≤ b) {n k : ℕ} (hk : k ≤ n + 1) : grid a b n k ∈ Icc a b := by
  have h0 : 0 ≤ (b - a) / (n + 1) := div_nonneg (by linarith) (by positivity)
  have hk' : (k : ℝ) ≤ n + 1 := by exact_mod_cast hk
  have hfull : ((n : ℝ) + 1) * ((b - a) / (n + 1)) = b - a := by field_simp
  refine ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg k) h0), ?_⟩
  have := mul_le_mul_of_nonneg_right hk' h0
  unfold grid
  linarith

/-- At stage `n`, the grid is finite, so `f` attains a largest value on it. -/
theorem exists_grid_max (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    ∃ k ∈ Finset.range (n + 2), ∀ j ∈ Finset.range (n + 2),
      f (grid a b n j) ≤ f (grid a b n k) :=
  Finset.exists_max_image _ _ ⟨0, by simp⟩

/-- At stage `n`, a grid point where `f` is largest. -/
def gridMax (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  grid a b n (exists_grid_max f a b n).choose

theorem gridMax_mem (f : ℝ → ℝ) (hab : a ≤ b) (n : ℕ) : gridMax f a b n ∈ Icc a b :=
  grid_mem hab (Nat.lt_succ_iff.mp (Finset.mem_range.mp (exists_grid_max f a b n).choose_spec.1))

/-- At stage `n`, the index of a grid point at most one step below `y`. -/
def near (a b y : ℝ) (n : ℕ) : ℕ := ⌊(y - a) / (b - a) * (n + 1)⌋₊

theorem near_le (hab : a < b) (hy : y ∈ Icc a b) (n : ℕ) : near a b y n ≤ n + 1 := by
  have h1 : (y - a) / (b - a) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith [hy.2])
  have : (y - a) / (b - a) * (n + 1) ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    exact mul_le_of_le_one_left (by positivity) h1
  exact (Nat.floor_le_floor this).trans (Nat.floor_natCast _).le

theorem near_close (hab : a < b) (hy : y ∈ Icc a b) (n : ℕ) :
    |grid a b n (near a b y n) - y| ≤ (b - a) / (n + 1) := by
  unfold grid near
  set t := (y - a) / (b - a) * (n + 1) with ht
  have hba : b - a ≠ 0 := by linarith
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have t0 : 0 ≤ t := mul_nonneg (div_nonneg (by linarith [hy.1]) (by linarith)) (by positivity)
  have h1 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le t0
  have h2 : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
  have hd : 0 < (b - a) / (n + 1) := div_pos (by linarith) (by positivity)
  have key : a + t * ((b - a) / (n + 1)) = y := by rw [ht]; field_simp; ring
  rw [abs_le]
  constructor <;>
    nlinarith [mul_le_mul_of_nonneg_right h1 hd.le, mul_lt_mul_of_pos_right h2 hd]

/-- The grid points near `y` converge to `y` along any free ultrafilter. -/
theorem tendsto_near (hab : a < b) (hy : y ∈ Icc a b) {U : Ultrafilter ℕ}
    (hU : (U : Filter ℕ) ≤ cofinite) :
    Tendsto (fun n ↦ grid a b n (near a b y n)) (U : Filter ℕ) (𝓝 y) := by
  have hd : Tendsto (fun n : ℕ ↦ (b - a) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    refine ((tendsto_const_div_atTop_nhds_zero_nat (b - a)).comp
      (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp [Function.comp]
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    (hd.mono_left (hU.trans Nat.cofinite_eq_atTop.le))
  rw [Real.dist_eq]
  exact near_close hab hy n

/-! ## The theorem -/

/-- A continuous function on a closed interval attains its maximum. -/
theorem exists_max_on_Icc {f : ℝ → ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b)) :
    ∃ c ∈ Icc a b, ∀ y ∈ Icc a b, f y ≤ f c := by
  let U := hyperfilter ℕ
  have hU : (U : Filter ℕ) ≤ cofinite := hyperfilter_le_cofinite
  -- the nonstandard maximiser on the hyperfine grid, and its standard part `c`
  obtain ⟨c, hc, hX⟩ := exists_isSt_of_mem_Icc (U := U) _ (gridMax_mem f hab.le)
  refine ⟨c, hc, fun y hy ↦ ?_⟩
  -- the grid point `Y ≈ y`
  have hY : IsSt (ofFun (U := U) fun n ↦ grid a b n (near a b y n)) y :=
    (isSt_ofFun_iff _ _).mpr (tendsto_near hab hy hU)
  -- continuity: `f X ≈ f c` and `f Y ≈ f y`
  have hfX := isSt_comp (hf c hc) _ (gridMax_mem f hab.le) hX
  have hfY := isSt_comp (hf y hy) _ (fun n ↦ grid_mem hab.le (near_le hab hy n)) hY
  rw [app_lift_ofFun] at hfX hfY
  -- at every stage, `f Y ≤ f X` because `X` maximises `f` on the grid
  exact isSt_le hfX hfY (Eventually.of_forall fun n ↦
    (exists_grid_max f a b n).choose_spec.2 _
      (Finset.mem_range.mpr (Nat.lt_succ_of_le (near_le hab hy n))))

end
