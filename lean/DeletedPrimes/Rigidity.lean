import Mathlib

/-!
# Lemma 5.2 (composite window rigidity) and the arithmetic of the frame

**Lemma 5.2.** Let `T₁, …, T_k` be sets of primes, `T_i ⊆ [Y_i, ∞)`, and let the test moduli be the products
`q = q₁⋯q_k`, `q_i ∈ T_i` (in Lean: the tuples `f ∈ ∏ T_i`, with modulus `∏ f i`; the product map is injective when
the `T_i` are disjoint, `prod_injOn`). Let `J ≥ 1`, and let `n` be an integer with `|n| > J` such that every
`n + j`, `|j| ≤ J`, has absolute value `< Y_i^{L_i + 1}` for each `i`. Then for every `I ⊆ {1, …, k}` the number of
moduli dividing some `n + j`, `0 < |j| ≤ J`, is at most `(∏_{i∈I} #T_i)·(⌊2J/Y_I⌋ + 1)·∏_{i∉I} L_i`,
`Y_I = ∏_{i∈I} Y_i` (`window_rigidity`). The case `k = 1`, `I = ∅` is the prime-factor count of the prime test.

**The frame.** The arithmetic facts used in Steps 3, 4 and 6 of §5, for moduli `q ≥ 1` and harmonics `m = ±1`:
an exact resonance `k/d = m/q` forces `q ∣ d` (`resonance_dvd`); otherwise `|k/d − m/q| ≥ 1/(dq)` (`sep_of_ne`);
distinct fractions `m/q ≠ m'/q'` are `1/(qq')`-separated (`sep_of_pair_ne`); at most one `k` has
`|kq − md| < q/2` (`near_unique`), and if `q ∤ md` it gives a witness `j = kq − md ≠ 0` with `q ∣ md + j`
(`near_witness`). The bound `L = ⌊log N/log Y⌋` satisfies `N < Y^{L+1}` (`lt_pow_floor_log`).
-/

open Real

namespace DeletedPrimes

open Classical

/-- A nonzero integer `N` with `|N| < Y^{L+1}` (`Y ≥ 2`) is divisible by at most `L` primes `≥ Y` of a finset. -/
theorem card_primes_dvd_le {T : Finset ℕ} {Y L : ℕ} {N : ℤ} (hY2 : 2 ≤ Y) (hN : N ≠ 0)
    (hNb : N.natAbs < Y ^ (L + 1)) (hp : ∀ q ∈ T, q.Prime) (hY : ∀ q ∈ T, Y ≤ q)
    (hd : ∀ q ∈ T, (q : ℤ) ∣ N) : T.card ≤ L := by
  have hpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hprod : (∏ q ∈ T, q) ∣ N.natAbs :=
    Finset.prod_primes_dvd N.natAbs (fun q hq => (hp q hq).prime)
      (fun q hq => Int.natCast_dvd.mp (hd q hq))
  have h1 : Y ^ T.card ≤ ∏ q ∈ T, q := by
    have := Finset.pow_card_le_prod T (fun q => q) Y hY
    simpa using this
  have hle : Y ^ T.card ≤ N.natAbs := le_trans h1 (Nat.le_of_dvd hpos hprod)
  have hlt : Y ^ T.card < Y ^ (L + 1) := lt_of_le_of_lt hle hNb
  have := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  omega

/-- `N < Y^{⌊log N / log Y⌋ + 1}` for `N ≥ 1`, `Y ≥ 2`. -/
theorem lt_pow_floor_log {N Y : ℕ} (hN : 1 ≤ N) (hY : 2 ≤ Y) :
    N < Y ^ (⌊Real.log N / Real.log Y⌋₊ + 1) := by
  set L := ⌊Real.log N / Real.log Y⌋₊
  have hYr : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogY : 0 < Real.log Y := Real.log_pos hYr
  have h1 : Real.log N / Real.log Y < (L : ℝ) + 1 := Nat.lt_floor_add_one _
  have h2 : Real.log N < ((L : ℝ) + 1) * Real.log Y := (div_lt_iff₀ hlogY).mp h1
  have h3 : Real.log N < Real.log ((Y : ℝ) ^ (L + 1)) := by
    rw [Real.log_pow]; push_cast; exact h2
  have h4 : (N : ℝ) < (Y : ℝ) ^ (L + 1) :=
    (Real.log_lt_log_iff hNr (by positivity)).mp h3
  exact_mod_cast h4

/-- The product map `f ↦ ∏ f i` is injective on `∏ T_i` when the `T_i` are pairwise disjoint sets of primes. -/
theorem prod_injOn {k : ℕ} (T : Fin k → Finset ℕ) (hp : ∀ i, ∀ q ∈ T i, q.Prime)
    (hdisj : Pairwise fun i i' => Disjoint (T i) (T i')) :
    Set.InjOn (fun f : Fin k → ℕ => ∏ i, f i) (Fintype.piFinset T : Set (Fin k → ℕ)) := by
  intro f hf f' hf' heq
  simp only [Finset.mem_coe, Fintype.mem_piFinset] at hf hf'
  simp only at heq
  funext i
  have hpi : (f i).Prime := hp i _ (hf i)
  have hdvd : f i ∣ ∏ i, f' i := heq ▸ Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  obtain ⟨i', -, hi'⟩ := (Prime.dvd_finsetProd_iff hpi.prime f').mp hdvd
  have heq' : f i = f' i' := (Nat.prime_dvd_prime_iff_eq hpi (hp i' _ (hf' i'))).mp hi'
  have hii' : i = i' := by
    by_contra hne
    have hd := hdisj hne
    have h1 : f i ∈ T i := hf i
    have h2 : f i ∈ T i' := heq' ▸ hf' i'
    exact Finset.disjoint_left.mp hd h1 h2
  subst hii'
  exact heq'

/-- The integers `j ∈ [-J, J]` with `q ∣ n + j` number at most `2J/q + 1`. -/
theorem card_window_dvd_le (n : ℤ) (J q : ℕ) (hq : 0 < q) :
    ((Finset.Icc (-(J : ℤ)) J).filter (fun j => (q : ℤ) ∣ n + j)).card ≤ 2 * J / q + 1 := by
  set S := (Finset.Icc (-(J : ℤ)) J).filter (fun j => (q : ℤ) ∣ n + j)
  have hqz : (0 : ℤ) < q := by exact_mod_cast hq
  have hmap : Set.MapsTo (fun j : ℤ => ((j + J) / q).toNat) (S : Set ℤ)
      (Finset.range (2 * J / q + 1) : Set ℕ) := by
    intro j hj
    simp only [S, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hj
    simp only [Finset.coe_range, Set.mem_Iio]
    have h1 : (j + J) / (q : ℤ) ≤ (2 * J : ℤ) / (q : ℤ) :=
      Int.ediv_le_ediv hqz (by omega)
    have h2 : ((2 * J : ℤ) / (q : ℤ)) = ((2 * J / q : ℕ) : ℤ) := by push_cast; rfl
    have h3 : 0 ≤ (j + J) / (q : ℤ) := Int.ediv_nonneg (by omega) hqz.le
    omega
  have hinj : Set.InjOn (fun j : ℤ => ((j + J) / q).toNat) (S : Set ℤ) := by
    intro a ha b hb hab
    simp only [S, Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at ha hb
    simp only at hab
    have ha0 : 0 ≤ (a + J) / (q : ℤ) := Int.ediv_nonneg (by omega) hqz.le
    have hb0 : 0 ≤ (b + J) / (q : ℤ) := Int.ediv_nonneg (by omega) hqz.le
    have hdiv : (a + J) / (q : ℤ) = (b + J) / (q : ℤ) := by omega
    have hmod : (a + J) % (q : ℤ) = (b + J) % (q : ℤ) := by
      have : (a + J) ≡ (b + J) [ZMOD q] := by
        rw [Int.modEq_iff_dvd]
        have := dvd_sub hb.2 ha.2
        have e : n + b - (n + a) = b + J - (a + J) := by ring
        rw [e] at this; exact this
      exact this
    have ea := Int.mul_ediv_add_emod (a + J) q
    have eb := Int.mul_ediv_add_emod (b + J) q
    rw [hdiv, hmod] at ea
    omega
  calc S.card ≤ (Finset.range (2 * J / q + 1)).card := Finset.card_le_card_of_injOn _ hmap hinj
    _ = 2 * J / q + 1 := Finset.card_range _

/-- **Lemma 5.2 (composite window rigidity).** -/
theorem window_rigidity {k : ℕ} (T : Fin k → Finset ℕ) (Y L : Fin k → ℕ)
    (hp : ∀ i, ∀ q ∈ T i, q.Prime) (hY : ∀ i, ∀ q ∈ T i, Y i ≤ q) (hY2 : ∀ i, 2 ≤ Y i)
    (n : ℤ) (J : ℕ) (hnJ : (J : ℤ) < |n|)
    (hL : ∀ i, ∀ j : ℤ, |j| ≤ J → (n + j).natAbs < Y i ^ (L i + 1)) (I : Finset (Fin k)) :
    ((Fintype.piFinset T).filter
        fun f : Fin k → ℕ => ∃ j : ℤ, j ≠ 0 ∧ |j| ≤ J ∧ ((∏ i, f i : ℕ) : ℤ) ∣ n + j).card
      ≤ (∏ i ∈ I, (T i).card) * (2 * J / ∏ i ∈ I, Y i + 1) * ∏ i ∈ Iᶜ, L i := by
  set YI := ∏ i ∈ I, Y i with hYI_def
  have hYI : 0 < YI := Finset.prod_pos (fun i _ => by have := hY2 i; omega)
  -- the `I`-parts
  set G : Finset (Fin k → ℕ) := Fintype.piFinset (fun i => if i ∈ I then T i else {0}) with hG_def
  -- admissible shifts for an `I`-part
  set JS : (Fin k → ℕ) → Finset ℤ := fun g =>
    (Finset.Icc (-(J : ℤ)) J).filter (fun j => ((∏ i ∈ I, g i : ℕ) : ℤ) ∣ n + j) with hJS_def
  -- the `Iᶜ`-parts compatible with a shift
  set H : ℤ → Finset (Fin k → ℕ) := fun j =>
    Fintype.piFinset (fun i => if i ∈ I then {0} else (T i).filter (fun p => (p : ℤ) ∣ n + j))
    with hH_def
  have hsub : ((Fintype.piFinset T).filter
        fun f : Fin k → ℕ => ∃ j : ℤ, j ≠ 0 ∧ |j| ≤ J ∧ ((∏ i, f i : ℕ) : ℤ) ∣ n + j) ⊆
      G.biUnion (fun g => (JS g).biUnion (fun j => (H j).image (fun h => g + h))) := by
    intro f hf
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hf
    obtain ⟨hfT, j, -, hj, hdvd⟩ := hf
    rw [Finset.mem_biUnion]
    refine ⟨fun i => if i ∈ I then f i else 0, ?_, ?_⟩
    · rw [hG_def, Fintype.mem_piFinset]
      intro i
      by_cases hi : i ∈ I <;> simp [hi, hfT i]
    rw [Finset.mem_biUnion]
    refine ⟨j, ?_, ?_⟩
    · rw [hJS_def]
      simp only [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨(abs_le.mp hj), ?_⟩
      have e : (∏ i ∈ I, (if i ∈ I then f i else 0)) = ∏ i ∈ I, f i :=
        Finset.prod_congr rfl (fun i hi => by simp [hi])
      rw [e]
      refine dvd_trans ?_ hdvd
      exact Int.natCast_dvd_natCast.mpr (Finset.prod_dvd_prod_of_subset I Finset.univ f
        (Finset.subset_univ I))
    rw [Finset.mem_image]
    refine ⟨fun i => if i ∈ I then 0 else f i, ?_, ?_⟩
    · rw [hH_def, Fintype.mem_piFinset]
      intro i
      by_cases hi : i ∈ I
      · simp [hi]
      · simp only [hi, ite_false, Finset.mem_filter]
        refine ⟨hfT i, dvd_trans ?_ hdvd⟩
        exact Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem f (Finset.mem_univ i))
    · funext i
      by_cases hi : i ∈ I <;> simp [hi]
  have hH : ∀ j : ℤ, |j| ≤ J → (H j).card ≤ ∏ i ∈ Iᶜ, L i := by
    intro j hj
    have hnj : n + j ≠ 0 := by
      intro h
      have : n = -j := by linarith
      rw [this, abs_neg] at hnJ
      linarith
    rw [hH_def]
    simp only
    rw [Fintype.card_piFinset, ← Finset.prod_mul_prod_compl I]
    have e1 : ∏ i ∈ I, (if i ∈ I then ({0} : Finset ℕ) else
        (T i).filter (fun p => (p : ℤ) ∣ n + j)).card = 1 :=
      Finset.prod_eq_one (fun i hi => by simp [hi])
    rw [e1, one_mul]
    apply Finset.prod_le_prod
    intro i hi
    rw [Finset.mem_compl] at hi
    simp only [hi, ite_false]
    apply card_primes_dvd_le (hY2 i) hnj (hL i j hj)
    · intro p hp'; exact hp i p (Finset.mem_filter.mp hp').1
    · intro p hp'; exact hY i p (Finset.mem_filter.mp hp').1
    · intro p hp'; exact (Finset.mem_filter.mp hp').2
  have hJS : ∀ g ∈ G, (JS g).card ≤ 2 * J / YI + 1 := by
    intro g hg
    rw [hG_def, Fintype.mem_piFinset] at hg
    have hge : YI ≤ ∏ i ∈ I, g i := by
      apply Finset.prod_le_prod
      intro i hi
      have := hg i
      simp only [hi, ite_true] at this
      exact hY i _ this
    calc (JS g).card ≤ 2 * J / (∏ i ∈ I, g i) + 1 :=
          card_window_dvd_le n J _ (lt_of_lt_of_le hYI hge)
      _ ≤ 2 * J / YI + 1 := by
          gcongr
  have hGcard : G.card = ∏ i ∈ I, (T i).card := by
    rw [hG_def, Fintype.card_piFinset, ← Finset.prod_mul_prod_compl I]
    have e1 : ∏ i ∈ Iᶜ, (if i ∈ I then T i else ({0} : Finset ℕ)).card = 1 :=
      Finset.prod_eq_one (fun i hi => by rw [Finset.mem_compl] at hi; simp [hi])
    rw [e1, mul_one]
    exact Finset.prod_congr rfl (fun i hi => by simp [hi])
  calc _ ≤ (G.biUnion (fun g => (JS g).biUnion (fun j => (H j).image (fun h => g + h)))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ g ∈ G, ((JS g).biUnion (fun j => (H j).image (fun h => g + h))).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ g ∈ G, ∑ j ∈ JS g, ((H j).image (fun h => g + h)).card :=
        Finset.sum_le_sum (fun g _ => Finset.card_biUnion_le)
    _ ≤ ∑ g ∈ G, ∑ j ∈ JS g, ∏ i ∈ Iᶜ, L i := by
        apply Finset.sum_le_sum
        intro g _
        apply Finset.sum_le_sum
        intro j hj
        rw [hJS_def] at hj
        simp only [Finset.mem_filter, Finset.mem_Icc] at hj
        exact Finset.card_image_le.trans (hH j (abs_le.mpr hj.1))
    _ = ∑ g ∈ G, (JS g).card * ∏ i ∈ Iᶜ, L i := by
        simp only [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ g ∈ G, (2 * J / YI + 1) * ∏ i ∈ Iᶜ, L i := by
        apply Finset.sum_le_sum
        intro g hg
        exact Nat.mul_le_mul_right _ (hJS g hg)
    _ = G.card * ((2 * J / YI + 1) * ∏ i ∈ Iᶜ, L i) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ = (∏ i ∈ I, (T i).card) * (2 * J / YI + 1) * ∏ i ∈ Iᶜ, L i := by
        rw [hGcard, mul_assoc]

/-- Step 3: an exact resonance `kq = md` with `m = ±1` forces `q ∣ d`. -/
theorem resonance_dvd {k d q m : ℤ} (hm : m = 1 ∨ m = -1) (h : k * q = m * d) : q ∣ d := by
  rcases hm with rfl | rfl
  · exact ⟨k, by linarith⟩
  · exact ⟨-k, by linarith⟩

/-- Steps 3 and 4: a non-resonant pair is `1/(dq)`-separated. -/
theorem sep_of_ne {k d q m : ℤ} (hd : 0 < d) (hq : 0 < q) (h : k * q ≠ m * d) :
    1 / ((d : ℝ) * q) ≤ |(k : ℝ) / d - (m : ℝ) / q| := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hne : k * q - d * m ≠ 0 := by
    intro h'; apply h; linarith
  have h1 : (1 : ℝ) ≤ |(k : ℝ) * q - d * m| := by
    have := Int.one_le_abs hne
    exact_mod_cast this
  rw [div_sub_div _ _ hd'.ne' hq'.ne', abs_div, abs_of_pos (mul_pos hd' hq')]
  gcongr

/-- Step 6: distinct pairs `(q, m) ≠ (q', m')`, `m, m' = ±1`, give fractions at distance `≥ 1/(qq')`. -/
theorem sep_of_pair_ne {q q' : ℕ} {m m' : ℤ} (hq : 0 < q) (hq' : 0 < q') (hm : m = 1 ∨ m = -1)
    (hm' : m' = 1 ∨ m' = -1) (hne : (q, m) ≠ (q', m')) :
    1 / ((q : ℝ) * q') ≤ |(m : ℝ) / q - (m' : ℝ) / q'| := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hne' : m * (q' : ℤ) - (q : ℤ) * m' ≠ 0 := by
    have hqq : q ≠ q' ∨ m ≠ m' := by
      by_contra hc
      push Not at hc
      exact hne (by rw [hc.1, hc.2])
    rcases hm with rfl | rfl <;> rcases hm' with rfl | rfl <;> omega
  have h1 : (1 : ℝ) ≤ |(m : ℝ) * q' - q * m'| := by
    have := Int.one_le_abs hne'
    exact_mod_cast this
  rw [div_sub_div _ _ hqr.ne' hqr'.ne', abs_div, abs_of_pos (mul_pos hqr hqr')]
  gcongr

/-- Lemma 5.1: at most one `k` has `|kq − a| < q/2`. -/
theorem near_unique {q k k' a : ℤ} (hq : 0 < q) (hk : 2 * |k * q - a| < q)
    (hk' : 2 * |k' * q - a| < q) : k = k' := by
  have h1 := le_abs_self (k * q - a)
  have h2 := neg_abs_le (k * q - a)
  have h3 := le_abs_self (k' * q - a)
  have h4 := neg_abs_le (k' * q - a)
  rcases lt_trichotomy k k' with h | h | h
  · have : (k' - k) * q ≥ 1 * q := mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith
  · exact h
  · have : (k - k') * q ≥ 1 * q := mul_le_mul_of_nonneg_right (by omega) hq.le
    nlinarith

/-- Lemma 5.1: if `q ∤ a`, then `j = kq − a` is a nonzero witness with `q ∣ a + j`. -/
theorem near_witness {q k a : ℤ} (ha : ¬ q ∣ a) : k * q - a ≠ 0 ∧ q ∣ a + (k * q - a) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply ha
    exact ⟨k, by linarith⟩
  · rw [show a + (k * q - a) = q * k by ring]
    exact dvd_mul_right q k

end DeletedPrimes
