# Deleting primes from the integers: how regular can the remaining integers be?

## Provenance

The mathematics, the proofs, the Lean code and the text in this repository were produced almost entirely by AI
sessions (Claude, Anthropic). A single person, who prefers to stay anonymous, chose the question, set the scope,
directed the sessions, and decided what to keep. No human expert has read the proofs. One further AI session reviewed
the paper and the Lean library and found no errors; that is not an independent human review and should not be treated
as one.

The repository is released so that anyone interested can take the ideas, check them, correct them, or carry them
further, with no obligation to the author. If you build on it, a link back to this repository is appreciated but not
required.

## Acknowledgement

The ideas in this repository come from the published work of other people. A language model has no mathematics of
its own: what it knows, it learned from the literature, and what it produced here is a recombination and extension of
results that others found. In that sense the people below are the real creators of this work, and publishing it
anonymously, with no name attached that could take credit from theirs, is the author's way of respecting that.

The paper builds most directly on:
- **Arne Beurling**, who introduced generalized primes, and **Harold Diamond and Wen-Bin Zhang**, whose monograph is
  the standard account of them.
- **Titus Hilberdink**, who defined `[α, β]`-systems, proved `max(α, β) ≥ 1/2`, and proved the rigidity theorem for
  periodic integer counts.
- **Frederik Broucke, Gregory Debruyne, Szilárd Révész and Jasson Vindas**, whose constructions of well-behaved
  Beurling systems, including systems with regular integers and irregular primes, and whose random approximation
  procedure are the starting point of Theorems 1 and 2 and Corollary 3; the adjoining step in Corollary 3(3) is
  theirs.
- **Harold Diamond, Hugh Montgomery and Ulrike Vorhauer**, for the probabilistic construction of Beurling primes with
  large oscillation.
- **Oleksiy Klurman, Alexander Mangerel, Cosmin Pohoata and Joni Teräväinen**, whose answer to Ruzsa's question is
  the `O(1)` case of the question studied here.
- **Dimitris Koukoulopoulos and Kannan Soundararajan**, whose converse Selberg–Delange theorems are the principle
  behind Theorem 9.
- **Jeffrey Lagarias**, for the rigidity of Beurling integers with the Delone property.
- **Ofir Gorodetsky, Alexander Mangerel and Brad Rodgers**, for the variance of sifted sets in short intervals.
- **Roger Baker, Glyn Harman and János Pintz**, whose theorem on prime gaps gives the examples for Theorem 5.

The classical tools (Legendre's identity, Rankin's trick, Landau's theorem, the Hardy–Littlewood–Karamata Tauberian
theorem, Perron's formula, the Borel–Carathéodory theorem, von Koch's bound) and the textbooks of Montgomery and
Vaughan, Titchmarsh, Korevaar, and Bingham, Goldie and Teugels are older debts of the same kind.

None of these people has seen this repository, contributed to it, or is responsible for anything in it. Any errors are
the author's and the AI's.

## What is checked and what is not

- **Machine-checked (Lean 4, Mathlib).** The definitions, Legendre's identity, Rankin's bounds, the composite window
  rigidity lemma, the exponent optimisation, the good-scales selection, the exponent arithmetic of Corollary 3(3), and
  every deduction from the analytic statements. `lake build` is clean and the 82 cited names depend only on Lean's
  three standard axioms. See `lean/README.md` for the exact map.
- **Not checked by anyone but the AI that wrote them.** The analytic core: Steps 1–7 of Section 5 (Theorem 6),
  Landau's and Karamata's theorems as used in Theorem 9, the Plancherel argument of Section 3, and the probabilistic
  arguments of Sections 6 and 7. These enter the Lean library as named hypotheses. A referee would concentrate here.
- **Numerical.** `scripts/controller_check.py` reproduces the figures in Section 9.2.

Treat every unformalised statement as a conjecture with a detailed proof sketch until a person with the relevant
expertise has read it.

## Contents

| Path | Content |
|---|---|
| `paper/DeletedPrimes.tex`, `paper/DeletedPrimes.pdf` | the paper (22 pages) |
| `lean/` | the Lean 4 library `DeletedPrimes`; `lean/README.md` maps every result of the paper to its Lean names |
| `scripts/controller_check.py` | the computation behind §9.2 (large dimension) |
| `LICENSE` | CC0 1.0 Universal |

## The results

`S` is a set of primes with `∑_{p∈S} 1/p < ∞`, and `N_S(x)` counts the integers up to `x` with no prime factor in
`S`. The paper compares three exponents: `α(S)`, the dimension of `S`; `θ(S)`, the exponent of `N_S(x) − a_S x`; and
`θ₂(S) ≤ θ(S)`, the same exponent measured in mean square.
- **Theorem 6.** For every `S`, `θ(S) ≥ θ₂(S) ≥ (α/2)·min(1/2, 1−α)`, so `α ≤ 4θ₂` when `α ≤ 1/2`. The proof uses
  nothing about the zeros of `ζ`. The case `k = 1` is elementary; the general case also uses Landau's and
  Karamata's theorems, through Theorem 9.
- **Theorems 1 and 2.** A random `S` (each prime kept with probability `p^{α−1}`) has, almost surely, `θ ≥ α/2`, and
  under RH `θ = θ₂ = α/2`, for every `α < 1`. So the constant 4 cannot go below 2. Corollary 3 gives
  `[α, α/2]`-systems and, by adjoining the generalized primes `p^{1/β}` as Broucke–Debruyne–Révész do, `[α, β]`-systems
  for all `1/2 < α < 1` and `α/2 ≤ β < 1/2`, a band that contains their region; Corollary 4 gives RH-violating
  systems.
- **Theorem 5.** Smooth sets have `θ ≥ α/2`.
- **Theorem 9.** If `θ₂ < α`, the deleted primes obey a Mertens law with an integer constant.
- **Corollaries 7 and 8.** The counterexample window, and dimension zero.
- **Question 10.** Is `θ ≥ α/2` when `α ≤ 1/2`?

## Build

**Paper.** Run this in `paper/`:

```bash
tectonic -X compile DeletedPrimes.tex
```

**Lean.** Run these in `lean/` (details are in `lean/README.md`):

```bash
lake build
```

```bash
lake env lean AxiomCheck.lean
```

**Script.** Run this in `scripts/`. It needs numpy and scipy, and takes about a minute and 2 GB:

```bash
python3 controller_check.py 0.9 1e8 ctrl
```

## The Lean check in detail

**Lean** (checked 2026-10-09):
- `lake build` finished with no errors and no warnings.
- There is no `sorry` in the sources.
- All 82 names the paper cites depend only on Lean's three standard axioms.

**What Lean proves outright:**
- Legendre's identity and Rankin's bounds, and `θ ≤ α`.
- The composite window rigidity lemma and the frame arithmetic.
- The exponent optimisation `κ_k(α)` for every `k`.
- The good-scales selection.
- Every deduction.
- The exponent arithmetic of Corollary 3(3): the hyperbola exponent and balance, the cross terms, the tail terms, the
  real parts of the shifted zeros, the band, and the exactness of a two-term asymptotic.

**What enters as named hypotheses** (`Frame`, `Quantization`, `LandauAtOne`, and the theorem-local ones listed in
`lean/README.md`):
- The analytic steps: the Fourier analysis of §5, Landau's and Karamata's theorems, Plancherel, the contour shifts
  under RH, and the probability of §§6–7.

**Bibliography** (checked 2026-10-09 against arXiv, zbMATH and publisher records): every entry's journal, volume,
year and pages were confirmed; the page range of [Lagarias] was corrected to 295–312 and the article number of [BDV]
added. §1 now compares Theorem 1 with the random deletions of [BDR, §5] (their error exponent is `2α/(α+2)`, from the
hyperbola method), cites Koukoulopoulos (2013) and Koukoulopoulos–Soundararajan (2020) as prior art for the principle
of Theorem 9, and cites Révész (2022) and Broucke–Vindas (2024); Karamata's theorem is cited from
Bingham–Goldie–Teugels, Theorem 1.7.1.

## Still open

- **An expert read.** The proofs need an expert reader, above all §5 (Theorem 6), ideally an analytic number
  theorist.
- **A sharper floor for large dimension.** An earlier draft, not included here, claims a better floor than Theorem 6
  for `α > 0.768` by a variant of the test. It has not been reviewed. If it survives review, the paper should mention
  it.

## Licence

Everything in this repository (the paper, the Lean code, the script and this text) is released under CC0 1.0
Universal; see `LICENSE`. You may copy, change, build on and publish any of it, for any purpose, without asking and
without attribution. A link back to this repository is appreciated but not required. The Lean library depends on
Mathlib, which is distributed separately under the Apache License 2.0 and is not included here.
