import DeletedPrimes.Basic

/-!
# Dense dyadic blocks (the scales of §5)

- **From the dimension** ((5.4)): if `0 ≤ σ < α(S)` and `η > 0`, there are infinitely many `j` with
  `#(S ∩ [2^j, 2^{j+1})) ≥ 2^{j(σ−η)}` (`frequently_dense_block`).
- **From a Mertens law** (Proposition 4.1): if `∑_{p∈S, p≤x} log p / p^α ∼ m log x` with `m > 0`, then for every
  `δ, ε > 0` and every large `X` some dyadic block `[2^j, 2^{j+1})` with `X ≤ 2^j ≤ X^{1+δ}` has at least
  `2^{j(α−ε)}` elements of `S` (`good_scale`); and `k` such blocks can be found at once near prescribed scales
  `X^{λ_1}, …, X^{λ_k}`, in increasing order (`good_scales`). Also `π_S(x) ≥ x^{α−ε}` for every large `x`
  (`primeCount_ge`).
-/

open Real Filter Topology

namespace DeletedPrimes

noncomputable section

open Classical

/-- `#(S ∩ [Y, 2Y))`. -/
def blockCount (S : Set ℕ) (Y : ℕ) : ℕ := ((Finset.Ico Y (2 * Y)).filter (· ∈ S)).card

/-- `π_S(x) = #(S ∩ [1, x])`. -/
def primeCount (S : Set ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S)).card

/-- The Mertens sum `∑_{p ∈ S, p ≤ x} log p / p^α`. -/
def mertensSum (S : Set ℕ) (α x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S), Real.log p / (p : ℝ) ^ α

/-- The Mertens law with constant `m`: `∑_{p ∈ S, p ≤ x} log p / p^α = m log x + o(log x)`. -/
def MertensLaw (S : Set ℕ) (α m : ℝ) : Prop :=
  Tendsto (fun x => mertensSum S α x / Real.log x) atTop (𝓝 m)

/-- `(2^j)^a = (2^a)^j`. -/
theorem two_pow_rpow (j : ℕ) (a : ℝ) : ((2 : ℝ) ^ j) ^ a = ((2 : ℝ) ^ a) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

/-- (5.4): below the dimension, dense dyadic blocks occur infinitely often. -/
theorem frequently_dense_block {S : Set ℕ} {σ η : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < dim S) (hη : 0 < η) :
    ∃ᶠ j : ℕ in atTop, ((2 : ℝ) ^ j) ^ (σ - η) ≤ blockCount S (2 ^ j) := by
  set f : ℕ → ℝ := S.indicator fun n : ℕ => (n : ℝ) ^ (-σ) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n =>
    Set.indicator_nonneg (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _) n
  have hpart : ∀ N, ∑ n ∈ Finset.range (2 ^ N), f n =
      f 0 + ∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [← Finset.sum_range_add_sum_Ico f (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)), ih,
        Finset.sum_range_succ, pow_succ', add_assoc]
  have hblock : ∀ j, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n ≤
      (blockCount S (2 ^ j) : ℝ) * ((2 : ℝ) ^ j) ^ (-σ) := by
    intro j
    have h1 : ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n =
        ∑ n ∈ (Finset.Ico (2 ^ j) (2 * 2 ^ j)).filter (· ∈ S), (n : ℝ) ^ (-σ) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hf, Set.indicator_apply]
    rw [h1]
    have h2 := Finset.sum_le_card_nsmul ((Finset.Ico (2 ^ j) (2 * 2 ^ j)).filter (· ∈ S))
      (fun n : ℕ => (n : ℝ) ^ (-σ)) (((2 : ℝ) ^ j) ^ (-σ)) ?_
    · rw [nsmul_eq_mul] at h2
      exact h2
    · intro n hn
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      exact_mod_cast hn.1.1
  by_contra hfreq
  rw [Filter.not_frequently] at hfreq
  have hB0 : ∀ j, 0 ≤ ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n :=
    fun j => Finset.sum_nonneg fun n _ => hf0 n
  have hBev : ∀ᶠ j in atTop, ‖∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n‖ ≤ ((2 : ℝ) ^ (-η)) ^ j := by
    filter_upwards [hfreq] with j hj
    push Not at hj
    rw [Real.norm_eq_abs, abs_of_nonneg (hB0 j)]
    calc ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n
        ≤ (blockCount S (2 ^ j) : ℝ) * ((2 : ℝ) ^ j) ^ (-σ) := hblock j
      _ ≤ ((2 : ℝ) ^ j) ^ (σ - η) * ((2 : ℝ) ^ j) ^ (-σ) := by
          apply mul_le_mul_of_nonneg_right hj.le (by positivity)
      _ = ((2 : ℝ) ^ j) ^ (-η) := by
          rw [← Real.rpow_add (by positivity)]; ring_nf
      _ = ((2 : ℝ) ^ (-η)) ^ j := two_pow_rpow j (-η)
  have hr0 : 0 ≤ (2 : ℝ) ^ (-η) := by positivity
  have hr1 : (2 : ℝ) ^ (-η) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hBsum : Summable fun j => ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n :=
    Summable.of_norm_bounded_eventually_nat (summable_geometric_of_lt_one hr0 hr1) hBev
  have hfsum : Summable f := by
    refine summable_of_sum_range_le hf0
      (c := f 0 + ∑' j, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n) fun N => ?_
    calc ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range (2 ^ N), f n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr Nat.lt_two_pow_self.le) (fun n _ _ => hf0 n)
      _ = f 0 + ∑ j ∈ Finset.range N, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n := hpart N
      _ ≤ f 0 + ∑' j, ∑ n ∈ Finset.Ico (2 ^ j) (2 * 2 ^ j), f n := by
          gcongr
          exact hBsum.sum_le_tsum _ (fun j _ => hB0 j)
  have hmem : σ ∈ {σ : ℝ | 0 ≤ σ ∧ Summable (S.indicator fun n : ℕ => (n : ℝ) ^ (-σ))} :=
    ⟨hσ0, hfsum⟩
  have hle : dim S ≤ σ := csInf_le ⟨0, fun _ h => h.1⟩ hmem
  linarith

/-! ### Helpers for the Mertens-law arguments -/

theorem mertensSum_sub (S : Set ℕ) (α : ℝ) {a b : ℝ} (hab : a ≤ b) :
    mertensSum S α b - mertensSum S α a =
      ∑ p ∈ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S),
        Real.log p / (p : ℝ) ^ α := by
  have hsub : (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S) ⊆ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans (Nat.floor_le_floor hab)⟩, hp.2⟩
  unfold mertensSum
  rw [← Finset.sum_sdiff hsub]
  ring

theorem mem_mertens_sdiff {S : Set ℕ} {a b : ℝ} (ha : 0 ≤ a) {p : ℕ}
    (hp : p ∈ (Finset.Icc 1 ⌊b⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊a⌋₊).filter (· ∈ S)) :
    p ∈ S ∧ 1 ≤ p ∧ a < p ∧ (p : ℝ) ≤ b := by
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hp
  have h5 : ⌊a⌋₊ < p := by
    by_contra h
    push Not at h
    exact h4 ⟨⟨h1, h⟩, h3⟩
  exact ⟨h3, h1, (Nat.floor_lt ha).mp h5, (Nat.le_floor_iff' (by omega)).mp h2⟩

theorem tendsto_mertens_comp {S : Set ℕ} {α m : ℝ} (hM : MertensLaw S α m) {u : ℝ → ℝ} {c : ℝ}
    (hu : Tendsto u atTop atTop)
    (hlog : Tendsto (fun x => Real.log (u x) / Real.log x) atTop (𝓝 c)) :
    Tendsto (fun x => mertensSum S α (u x) / Real.log x) atTop (𝓝 (m * c)) := by
  have h1 : Tendsto (fun x => mertensSum S α (u x) / Real.log (u x)) atTop (𝓝 m) := hM.comp hu
  refine (h1.mul hlog).congr' ?_
  filter_upwards [hu.eventually_gt_atTop 1] with x hx
  have : Real.log (u x) ≠ 0 := (Real.log_pos hx).ne'
  rw [div_mul_div_comm, mul_comm (mertensSum S α (u x)), mul_div_mul_left _ _ this]

theorem tendsto_log_rpow_div (b : ℝ) :
    Tendsto (fun x : ℝ => Real.log (x ^ b) / Real.log x) atTop (𝓝 b) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  rw [Real.log_rpow (by linarith), mul_div_assoc, div_self (Real.log_pos hx).ne', mul_one]

theorem tendsto_log_two_mul_div :
    Tendsto (fun x : ℝ => Real.log (2 * x) / Real.log x) atTop (𝓝 1) := by
  have h : Tendsto (fun x : ℝ => Real.log 2 * (Real.log x)⁻¹ + 1) atTop (𝓝 (Real.log 2 * 0 + 1)) :=
    (Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul _).add_const 1
  rw [mul_zero, zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with x hx
  have hl : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  rw [Real.log_mul (by norm_num) (by linarith)]
  field_simp

theorem log_two_bounds {p : ℕ} (hp : p ≠ 0) :
    2 ^ Nat.log 2 p ≤ p ∧ p < 2 * 2 ^ Nat.log 2 p := by
  refine ⟨Nat.pow_log_le_self 2 hp, ?_⟩
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  rwa [pow_succ'] at this

theorem term_le {α : ℝ} (hα : 0 ≤ α) {p j : ℕ} (h1 : 2 ^ j ≤ p) (h2 : p < 2 * 2 ^ j) :
    Real.log p / (p : ℝ) ^ α ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α := by
  have h1' : (2 : ℝ) ^ j ≤ p := by exact_mod_cast h1
  have h2' : (p : ℝ) ≤ 2 ^ (j + 1) := by rw [pow_succ']; exact_mod_cast h2.le
  have hp : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) h1'
  apply div_le_div₀ (mul_nonneg (by positivity) (Real.log_nonneg (by norm_num))) _ (by positivity)
    (Real.rpow_le_rpow (by positivity) h1' hα)
  calc Real.log p ≤ Real.log (2 ^ (j + 1)) := Real.log_le_log hp h2'
    _ = ((j : ℝ) + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring

/-- Proposition 4.1(1): a dense dyadic block in every polynomial range `[X, X^{1+δ}]`. -/
theorem good_scale {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop, ∃ j : ℕ, X ≤ 2 ^ j ∧ (2 : ℝ) ^ j ≤ X ^ (1 + δ) ∧
      ((2 : ℝ) ^ j) ^ (α - ε) ≤ blockCount S (2 ^ j) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-ε) := by positivity
  have hr1 : (2 : ℝ) ^ (-ε) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ht0 : ∀ j : ℕ, 0 ≤ Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) :=
    fun j => mul_nonneg hl2 (by positivity)
  have htsum : Summable fun j : ℕ => Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) := by
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * ((2 : ℝ) ^ (-ε)) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1)
    have h2 := summable_geometric_of_lt_one hr0 hr1
    refine ((h1.add h2).mul_left (Real.log 2)).congr fun j => ?_
    simp only [pow_one]
    ring
  set T := ∑' j : ℕ, Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) with hT
  have hT0 : 0 ≤ T := tsum_nonneg ht0
  have hinc : Tendsto (fun X => (mertensSum S α (X ^ (1 + δ)) - mertensSum S α (2 * X)) /
      Real.log X) atTop (𝓝 (m * (1 + δ) - m * 1)) := by
    have hA := tendsto_mertens_comp hM (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 + δ))
      (tendsto_log_rpow_div (1 + δ))
    have hB := tendsto_mertens_comp hM (tendsto_id.const_mul_atTop two_pos)
      tendsto_log_two_mul_div
    exact (hA.sub hB).congr fun X => (sub_div _ _ _).symm
  have hpos : m * δ / 2 < m * (1 + δ) - m * 1 := by nlinarith
  filter_upwards [hinc.eventually (lt_mem_nhds hpos),
    Real.tendsto_log_atTop.eventually_gt_atTop (2 * T / (m * δ)), eventually_gt_atTop 1,
    (tendsto_rpow_atTop hδ).eventually_ge_atTop 2] with X hX1 hX2 hX3 hX4
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX3
  have h2X : 2 * X ≤ X ^ (1 + δ) := by
    rw [Real.rpow_add hX0, Real.rpow_one]; nlinarith
  have hlow : m * δ / 2 * Real.log X < mertensSum S α (X ^ (1 + δ)) - mertensSum S α (2 * X) := by
    rwa [lt_div_iff₀ hlog] at hX1
  have hTlt : T < m * δ / 2 * Real.log X := by
    rw [div_lt_iff₀ (by positivity)] at hX2
    linarith
  by_contra hcon
  push Not at hcon
  set D := (Finset.Icc 1 ⌊X ^ (1 + δ)⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊2 * X⌋₊).filter (· ∈ S)
    with hD
  have hup : mertensSum S α (X ^ (1 + δ)) - mertensSum S α (2 * X) ≤ T := by
    rw [mertensSum_sub S α h2X, ← Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem (Nat.log 2) hp)]
    calc _ ≤ ∑ j ∈ D.image (Nat.log 2),
          Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨p₀, hp₀, hpj⟩ := Finset.mem_image.mp hj
          obtain ⟨-, hp₀1, hp₀2, hp₀3⟩ := mem_mertens_sdiff (by positivity) hp₀
          obtain ⟨hlo, hhi⟩ := log_two_bounds (by omega : p₀ ≠ 0)
          rw [hpj] at hlo hhi
          have hlo' : (2 : ℝ) ^ j ≤ p₀ := by exact_mod_cast hlo
          have hhi' : (p₀ : ℝ) < 2 * 2 ^ j := by exact_mod_cast hhi
          have hXj : X ≤ 2 ^ j := by linarith
          have hjX : (2 : ℝ) ^ j ≤ X ^ (1 + δ) := hlo'.trans hp₀3
          have hbc := hcon j hXj hjX
          have hfib : ∀ p ∈ D.filter (fun p => Nat.log 2 p = j),
              Real.log p / (p : ℝ) ^ α ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α := by
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨-, hp1, -, -⟩ := mem_mertens_sdiff (by positivity) hp.1
            obtain ⟨h1, h2⟩ := log_two_bounds (by omega : p ≠ 0)
            rw [hp.2] at h1 h2
            exact term_le hα.le h1 h2
          have hcard : (D.filter (fun p => Nat.log 2 p = j)).card ≤ blockCount S (2 ^ j) := by
            apply Finset.card_le_card
            intro p hp
            rw [Finset.mem_filter] at hp
            obtain ⟨hpS, hp1, -, -⟩ := mem_mertens_sdiff (by positivity) hp.1
            obtain ⟨h1, h2⟩ := log_two_bounds (by omega : p ≠ 0)
            rw [hp.2] at h1 h2
            simp only [Finset.mem_filter, Finset.mem_Ico]
            exact ⟨⟨h1, h2⟩, hpS⟩
          have hc0 : 0 ≤ ((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α :=
            div_nonneg (mul_nonneg (by positivity) hl2) (by positivity)
          calc ∑ p ∈ D.filter (fun p => Nat.log 2 p = j), Real.log p / (p : ℝ) ^ α
              ≤ (D.filter (fun p => Nat.log 2 p = j)).card •
                  (((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α) :=
                Finset.sum_le_card_nsmul _ _ _ hfib
            _ ≤ (blockCount S (2 ^ j) : ℝ) * (((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α) := by
                rw [nsmul_eq_mul]
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
            _ ≤ ((2 : ℝ) ^ j) ^ (α - ε) * (((j : ℝ) + 1) * Real.log 2 / ((2 : ℝ) ^ j) ^ α) :=
                mul_le_mul_of_nonneg_right hbc.le hc0
            _ = Real.log 2 * (((j : ℝ) + 1) * ((2 : ℝ) ^ (-ε)) ^ j) := by
                have hA : 0 < ((2 : ℝ) ^ j) ^ α := by positivity
                have hE : 0 < ((2 : ℝ) ^ j) ^ ε := by positivity
                rw [← two_pow_rpow, Real.rpow_sub (by positivity), Real.rpow_neg (by positivity)]
                field_simp
      _ ≤ T := htsum.sum_le_tsum _ (fun j _ => ht0 j)
  linarith

/-- `k` dense dyadic blocks at once, near the scales `X^{λ_i}`, strictly increasing when the `λ_i` are separated:
`λ_i (1+δ) < λ_{i'}` for `i < i'`. -/
theorem good_scales {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) {k : ℕ} (lam : Fin k → ℝ)
    (hlam : ∀ i, 0 < lam i) (hsep : ∀ i i' : Fin k, i < i' → lam i * (1 + δ) < lam i') :
    ∀ᶠ X : ℝ in atTop, ∃ j : Fin k → ℕ, StrictMono j ∧ ∀ i,
      X ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) ∧
      ((2 : ℝ) ^ j i) ^ (α - ε) ≤ blockCount S (2 ^ j i) := by
  have hg := good_scale hα hm hM hδ hε
  have hall : ∀ i : Fin k, ∀ᶠ X : ℝ in atTop, ∃ j : ℕ, X ^ lam i ≤ 2 ^ j ∧
      (2 : ℝ) ^ j ≤ (X ^ lam i) ^ (1 + δ) ∧ ((2 : ℝ) ^ j) ^ (α - ε) ≤ blockCount S (2 ^ j) :=
    fun i => (tendsto_rpow_atTop (hlam i)).eventually hg
  filter_upwards [Filter.eventually_all.mpr hall, eventually_gt_atTop 1] with X hX hX1
  choose j hj using hX
  have hX0 : 0 ≤ X := by linarith
  have hj' : ∀ i, X ^ lam i ≤ 2 ^ j i ∧ (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) ∧
      ((2 : ℝ) ^ j i) ^ (α - ε) ≤ blockCount S (2 ^ j i) := by
    intro i
    obtain ⟨h1, h2, h3⟩ := hj i
    refine ⟨h1, ?_, h3⟩
    rwa [Real.rpow_mul hX0]
  refine ⟨j, fun i i' hii' => ?_, hj'⟩
  have h1 : (2 : ℝ) ^ j i < 2 ^ j i' := by
    calc (2 : ℝ) ^ j i ≤ X ^ (lam i * (1 + δ)) := (hj' i).2.1
      _ < X ^ lam i' := Real.rpow_lt_rpow_of_exponent_lt hX1 (hsep i i' hii')
      _ ≤ 2 ^ j i' := (hj' i').1
  exact (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h1

/-- Proposition 4.1(3): `π_S(x) ≥ x^{α−ε}` for every large `x`. -/
theorem primeCount_ge {S : Set ℕ} {α m : ℝ} (hα : 0 < α) (hm : 0 < m)
    (hM : MertensLaw S α m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x ^ (α - ε) ≤ primeCount S x := by
  set ε' : ℝ := min (1 / 2) (ε / (2 * α)) with hε'
  have hε'0 : 0 < ε' := lt_min (by norm_num) (by positivity)
  have hε'1 : ε' ≤ 1 / 2 := min_le_left _ _
  have hε'2 : ε' ≤ ε / (2 * α) := min_le_right _ _
  have hαε : α * ε' ≤ ε / 2 := by
    calc α * ε' ≤ α * (ε / (2 * α)) := mul_le_mul_of_nonneg_left hε'2 hα.le
      _ = ε / 2 := by field_simp
  set β : ℝ := α * (1 - ε') with hβ
  have hβgap : 0 < β - (α - ε) := by rw [hβ]; nlinarith
  have hinc : Tendsto (fun x => (mertensSum S α x - mertensSum S α (x ^ (1 - ε'))) / Real.log x)
      atTop (𝓝 (m - m * (1 - ε'))) := by
    have hB := tendsto_mertens_comp hM (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε'))
      (tendsto_log_rpow_div (1 - ε'))
    exact (hM.sub hB).congr fun x => (sub_div _ _ _).symm
  have hpos : m * ε' / 2 < m - m * (1 - ε') := by nlinarith
  have hpow : Tendsto (fun x : ℝ => x ^ (β - (α - ε))) atTop atTop := tendsto_rpow_atTop hβgap
  filter_upwards [hinc.eventually (lt_mem_nhds hpos), hpow.eventually_ge_atTop (2 / (m * ε')),
    eventually_gt_atTop 1] with x hx1 hx2 hx3
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx3
  have hle : x ^ (1 - ε') ≤ x := by
    calc x ^ (1 - ε') ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx3.le (by linarith)
      _ = x := Real.rpow_one x
  set D := (Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S) \ (Finset.Icc 1 ⌊x ^ (1 - ε')⌋₊).filter (· ∈ S)
    with hD
  have hlow : m * ε' / 2 * Real.log x < mertensSum S α x - mertensSum S α (x ^ (1 - ε')) := by
    rwa [lt_div_iff₀ hlog] at hx1
  have hxβ : 0 < x ^ β := by positivity
  have hup : mertensSum S α x - mertensSum S α (x ^ (1 - ε')) ≤
      (D.card : ℝ) * (Real.log x / x ^ β) := by
    rw [mertensSum_sub S α hle, ← nsmul_eq_mul]
    apply Finset.sum_le_card_nsmul
    intro p hp
    obtain ⟨-, hp1, hp2, hp3⟩ := mem_mertens_sdiff (by positivity) hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp1
    apply div_le_div₀ hlog.le (Real.log_le_log hp0 hp3) hxβ
    calc x ^ β = (x ^ (1 - ε')) ^ α := by rw [← Real.rpow_mul hx0.le, mul_comm]
      _ ≤ (p : ℝ) ^ α := Real.rpow_le_rpow (by positivity) hp2.le hα.le
  have hcard : m * ε' / 2 * x ^ β ≤ D.card := by
    have h1 : m * ε' / 2 * Real.log x < D.card * (Real.log x / x ^ β) := hlow.trans_le hup
    have h2 : (m * ε' / 2 * x ^ β) * Real.log x < D.card * Real.log x := by
      have := mul_lt_mul_of_pos_right h1 hxβ
      calc (m * ε' / 2 * x ^ β) * Real.log x = m * ε' / 2 * Real.log x * x ^ β := by ring
        _ < D.card * (Real.log x / x ^ β) * x ^ β := this
        _ = D.card * Real.log x := by field_simp
    exact (lt_of_mul_lt_mul_right h2 hlog.le).le
  have hsplit : x ^ β = x ^ (β - (α - ε)) * x ^ (α - ε) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hmain : x ^ (α - ε) ≤ m * ε' / 2 * x ^ β := by
    rw [hsplit]
    have hxa : 0 < x ^ (α - ε) := by positivity
    have : 1 ≤ m * ε' / 2 * x ^ (β - (α - ε)) := by
      rw [div_le_iff₀ (by positivity)] at hx2
      nlinarith
    nlinarith
  have hDle : D.card ≤ primeCount S x := by
    unfold primeCount
    exact Finset.card_le_card Finset.sdiff_subset
  calc x ^ (α - ε) ≤ m * ε' / 2 * x ^ β := hmain
    _ ≤ D.card := hcard
    _ ≤ primeCount S x := by exact_mod_cast hDle

end

end DeletedPrimes
