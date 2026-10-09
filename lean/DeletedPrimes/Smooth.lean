import DeletedPrimes.Basic

/-!
# Theorem 5 (smooth deletions): from the count bound to `θ(S) ≥ α/2`

The analytic part of §3 (Lemmas 3.1–3.3 and Plancherel's identity at a resolving height) proves the count bound
(1.3), `#(S ∩ (X, 2X]) ≪ X^{2σ} (log X)²` for every `σ > max(θ, δ)`, for each admissible `θ`; it enters here as a
hypothesis. Proved here:
- a smooth count `π_S(x) = c₀ li_α(x) + O(x^δ)` with `δ < α` gives `#(S ∩ (X, 2X]) ≫ X^α / log X`
  (`smooth_lower`);
- the comparison: (1.3) and that lower bound give `α ≤ 2σ` for every `σ > max(θ, δ)`, hence `θ(S) ≥ α/2` when
  `δ < α/2` (`smooth_half_le`).
-/

open Real Filter Topology

namespace DeletedPrimes

noncomputable section

open Classical

/-- `li_α(x) = ∫_2^x u^{α−1} / log u du`. -/
def liAlpha (α x : ℝ) : ℝ := ∫ u in (2 : ℝ)..x, u ^ (α - 1) / Real.log u

/-- `π_S(x) = #(S ∩ [1, x])`. -/
def piS (S : Set ℕ) (x : ℝ) : ℕ := ((Finset.Icc 1 ⌊x⌋₊).filter (· ∈ S)).card

/-- `#(S ∩ (X, 2X])`. -/
def intervalCount (S : Set ℕ) (X : ℝ) : ℕ := ((Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊).filter (· ∈ S)).card

/-- `π_S(2X) = π_S(X) + #(S ∩ (X, 2X])` for `X ≥ 1`. -/
theorem piS_two_mul {S : Set ℕ} {X : ℝ} (hX : 1 ≤ X) :
    piS S (2 * X) = piS S X + intervalCount S X := by
  have h1 : 1 ≤ ⌊X⌋₊ := (Nat.one_le_floor_iff X).mpr hX
  have h2 : ⌊X⌋₊ ≤ ⌊2 * X⌋₊ := Nat.floor_le_floor (by linarith)
  have hU : Finset.Icc 1 ⌊2 * X⌋₊ = Finset.Icc 1 ⌊X⌋₊ ∪ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ := by
    ext n; simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]; omega
  have hD : Disjoint (Finset.Icc 1 ⌊X⌋₊) (Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊) := by
    rw [Finset.disjoint_left]
    intro n hn hn'
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hn'
    omega
  unfold piS intervalCount
  rw [hU, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hD)]

/-- The integrand of `li_α` is interval integrable on `[a, b] ⊆ [2, ∞)`. -/
theorem intervalIntegrable_liAlpha_integrand (α : ℝ) {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun u : ℝ => u ^ (α - 1) / Real.log u) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  have hpos : ∀ u ∈ Set.uIcc a b, 2 ≤ u := by
    intro u hu
    rcases Set.mem_uIcc.mp hu with h | h <;> linarith [h.1]
  apply ContinuousOn.div
  · exact continuousOn_id.rpow_const (fun u hu => Or.inl (by simp only [id]; linarith [hpos u hu]))
  · exact continuousOn_id.log (fun u hu => by simp only [id]; linarith [hpos u hu])
  · intro u hu; exact (Real.log_pos (by linarith [hpos u hu])).ne'

/-- `li_α(2X) − li_α(X) ≥ 2^{α−2} X^α / log X` for `X ≥ 2` and `α ≤ 1`. -/
theorem liAlpha_two_mul_sub {α X : ℝ} (hα1 : α ≤ 1) (hX : 2 ≤ X) :
    2 ^ (α - 2) * X ^ α / Real.log X ≤ liAlpha α (2 * X) - liAlpha α X := by
  have hX0 : 0 < X := by linarith
  have hdiff : liAlpha α (2 * X) - liAlpha α X = ∫ u in X..2 * X, u ^ (α - 1) / Real.log u :=
    intervalIntegral.integral_interval_sub_left
      (intervalIntegrable_liAlpha_integrand α le_rfl (by linarith))
      (intervalIntegrable_liAlpha_integrand α le_rfl hX)
  rw [hdiff]
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hL2 : Real.log (2 * X) ≤ 2 * Real.log X := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 2 ≤ Real.log X := Real.log_le_log (by norm_num) hX
    linarith
  have hL2pos : 0 < Real.log (2 * X) := Real.log_pos (by linarith)
  have hmono : ∫ _u in X..2 * X, (2 * X) ^ (α - 1) / Real.log (2 * X)
      ≤ ∫ u in X..2 * X, u ^ (α - 1) / Real.log u := by
    apply intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
      (intervalIntegrable_liAlpha_integrand α hX (by linarith))
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    exact div_le_div₀ (by positivity) (Real.rpow_le_rpow_of_nonpos hu0 hu.2 (by linarith))
      (Real.log_pos (by linarith [hu.1])) (Real.log_le_log hu0 hu.2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  have e1 : (2 * X) ^ (α - 1) = 2 ^ (α - 1) * X ^ (α - 1) := Real.mul_rpow (by norm_num) hX0.le
  have e2 : X ^ α = X * X ^ (α - 1) := by
    conv_lhs => rw [show α = 1 + (α - 1) by ring]
    rw [Real.rpow_add hX0, Real.rpow_one]
  have e3 : (2 : ℝ) ^ (α - 2) = 2 ^ (α - 1) / 2 := by
    rw [show α - 2 = (α - 1) - 1 by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
  have hA : 0 < (2 : ℝ) ^ (α - 1) * X ^ α := by positivity
  calc 2 ^ (α - 2) * X ^ α / Real.log X = (2 ^ (α - 1) * X ^ α) / (2 * Real.log X) := by
        rw [e3]; field_simp
    _ ≤ (2 ^ (α - 1) * X ^ α) / Real.log (2 * X) := div_le_div_of_nonneg_left hA.le hL2pos hL2
    _ = (2 * X - X) * ((2 * X) ^ (α - 1) / Real.log (2 * X)) := by
        rw [e1, e2]; field_simp; ring

/-- A smooth count with `δ < α` puts `≫ X^α / log X` elements of `S` in `(X, 2X]`. -/
theorem smooth_lower {S : Set ℕ} {α δ c₀ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδα : δ < α)
    (hc₀ : 0 < c₀) (hπ : ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → |(piS S x : ℝ) - c₀ * liAlpha α x| ≤ C * x ^ δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, c * X ^ α / Real.log X ≤ intervalCount S X := by
  obtain ⟨C, hC⟩ := hπ
  have hC0 : 0 ≤ C := by
    have h := hC 2 le_rfl
    have h2 : (0 : ℝ) < 2 ^ δ := by positivity
    by_contra hneg
    push Not at hneg
    have : C * 2 ^ δ < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [abs_nonneg ((piS S 2 : ℝ) - c₀ * liAlpha α 2)]
  set c := c₀ * 2 ^ (α - 2) / 2 with hcdef
  have hc : 0 < c := by positivity
  set C' := C * (2 ^ δ + 1) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  set ε := c / (C' + 1) with hεdef
  have hεpos : 0 < ε := by positivity
  have hCε : C' * ε ≤ c := by
    rw [hεdef, mul_div_assoc', div_le_iff₀ (by linarith)]
    nlinarith
  have hlog := (isLittleO_log_rpow_atTop (sub_pos.mpr hδα)).bound hεpos
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with X hlX hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rw [Real.norm_of_nonneg hL.le, Real.norm_of_nonneg (by positivity)] at hlX
  have hN : (intervalCount S X : ℝ) = piS S (2 * X) - piS S X := by
    rw [piS_two_mul (S := S) (by linarith : (1 : ℝ) ≤ X)]; push_cast; ring
  have h1 := hC (2 * X) (by linarith)
  have h2 := hC X hX
  rw [abs_le] at h1 h2
  have h3 := liAlpha_two_mul_sub hα1.le hX
  have e : (2 * X) ^ δ = 2 ^ δ * X ^ δ := Real.mul_rpow (by norm_num) hX0.le
  have h3' : 2 * (c * X ^ α / Real.log X) ≤ c₀ * (liAlpha α (2 * X) - liAlpha α X) := by
    have := mul_le_mul_of_nonneg_left h3 hc₀.le
    calc 2 * (c * X ^ α / Real.log X) = c₀ * (2 ^ (α - 2) * X ^ α / Real.log X) := by
          rw [hcdef]; field_simp
      _ ≤ _ := this
  have hC'e : C' * X ^ δ = C * (2 * X) ^ δ + C * X ^ δ := by rw [hC', e]; ring
  have h4 : 2 * (c * X ^ α / Real.log X) - C' * X ^ δ ≤ (intervalCount S X : ℝ) := by
    rw [hN, hC'e]
    linarith [h1.1, h2.2]
  have e3 : X ^ δ * X ^ (α - δ) = X ^ α := by rw [← Real.rpow_add hX0]; ring_nf
  have h5 : C' * X ^ δ * Real.log X ≤ c * X ^ α := by
    calc C' * X ^ δ * Real.log X ≤ C' * X ^ δ * (ε * X ^ (α - δ)) :=
          mul_le_mul_of_nonneg_left hlX (by positivity)
      _ = (C' * ε) * (X ^ δ * X ^ (α - δ)) := by ring
      _ = (C' * ε) * X ^ α := by rw [e3]
      _ ≤ c * X ^ α := mul_le_mul_of_nonneg_right hCε (by positivity)
  have h6 : C' * X ^ δ ≤ c * X ^ α / Real.log X := by rw [le_div_iff₀ hL]; exact h5
  linarith

/-- **Theorem 5**, last step. `hcount` is the count bound (1.3) proved in §3 for every admissible `θ`. -/
theorem smooth_half_le {S : Set ℕ} {α δ : ℝ} (hδα : δ < α / 2)
    (hcount : ∀ θ σ : ℝ, 0 ≤ θ → IsRegular S θ → max θ δ < σ →
      ∃ C : ℝ, ∀ X : ℝ, 2 ≤ X → (intervalCount S X : ℝ) ≤ C * X ^ (2 * σ) * Real.log X ^ 2)
    (hlower : ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, c * X ^ α / Real.log X ≤ intervalCount S X) :
    α / 2 ≤ theta S := by
  obtain ⟨c, hc, hev⟩ := hlower
  refine le_csInf ⟨1, theta_set_one_mem S⟩ fun θ hθ => ?_
  obtain ⟨hθ0, hθreg⟩ := hθ
  by_contra hlt
  push Not at hlt
  have hmax : max θ δ < α / 2 := max_lt hlt hδα
  set σ := (max θ δ + α / 2) / 2 with hσ
  have hσ1 : max θ δ < σ := by rw [hσ]; linarith
  have hσ2 : 2 * σ < α := by rw [hσ]; linarith
  obtain ⟨C, hC⟩ := hcount θ σ hθ0 hθreg hσ1
  set ε := (α - 2 * σ) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hlog : ∀ᶠ X : ℝ in atTop, ‖Real.log X ^ (3 : ℝ)‖ ≤ 1 * ‖X ^ ε‖ :=
    (isLittleO_log_rpow_rpow_atTop 3 hε0).bound one_pos
  have key : ∀ᶠ X : ℝ in atTop, c * X ^ α ≤ |C| * X ^ (2 * σ + ε) := by
    filter_upwards [hev, hlog, eventually_ge_atTop (2 : ℝ)] with X h1 h2 h3
    have hX0 : 0 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos (by linarith)
    have h4 := hC X h3
    have hL3 : Real.log X ^ 3 ≤ X ^ ε := by
      have e1 : Real.log X ^ (3 : ℝ) = Real.log X ^ (3 : ℕ) := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [e1, Real.norm_of_nonneg (by positivity), one_mul, Real.norm_of_nonneg (by positivity)] at h2
      exact h2
    have h5 : c * X ^ α ≤ C * X ^ (2 * σ) * Real.log X ^ 3 := by
      have h' : c * X ^ α / Real.log X ≤ C * X ^ (2 * σ) * Real.log X ^ 2 := le_trans h1 h4
      rw [div_le_iff₀ hL] at h'
      calc c * X ^ α ≤ C * X ^ (2 * σ) * Real.log X ^ 2 * Real.log X := h'
        _ = C * X ^ (2 * σ) * Real.log X ^ 3 := by ring
    have h6 : C * X ^ (2 * σ) * Real.log X ^ 3 ≤ |C| * X ^ (2 * σ) * Real.log X ^ 3 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    have h7 : |C| * X ^ (2 * σ) * Real.log X ^ 3 ≤ |C| * X ^ (2 * σ) * X ^ ε :=
      mul_le_mul_of_nonneg_left hL3 (by positivity)
    rw [Real.rpow_add hX0, ← mul_assoc]
    linarith
  have := le_of_frequently_rpow_le hc key.frequently
  rw [hε] at this
  linarith

end

end DeletedPrimes
