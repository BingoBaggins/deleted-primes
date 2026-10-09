#!/usr/bin/env python3
"""controller_check.py -- the computation behind Section 9.2 ("Large dimension") of paper/DeletedPrimes.tex.

An independent implementation of the deletion rule of Section 9.2 of the paper, written 2026-10-09.

Below P0 = 1000 each prime is deleted with probability p^(alpha-1). The target density
a = prod_{p in S, p < P0}(1 - 1/p) * exp(-E1((1-alpha) log P0)) is fixed in advance. For p >= P0: delete p iff
N(p-1) + 1 - a*p > 1/2, where N counts the integers free of the primes deleted so far. Design 'rand' deletes every
prime with probability p^(alpha-1) instead (baseline; there a is the realised product with the model tail).
Prints max|E| and rms E on dyadic blocks [2^j, 2^{j+1}), the fitted dimension of S, and least-squares local slopes
(local growth exponents at finite x, not asymptotic exponents).

Usage: python3 controller_check.py ALPHA X ctrl|rand      e.g.  python3 controller_check.py 0.9 1e8 ctrl
Needs numpy and scipy; X = 1e8 takes about 1 minute and 2 GB.
Results (the inequality theta >= min(alpha/2, 1/4) needs growth exponent >= 1/4 when alpha >= 1/2):
  alpha=0.9, X=1e8, ctrl: fitted dim 0.898, max|E| 26.1 at the top block, slopes max 0.148 / rms 0.137
  alpha=0.9, X=2e7, rand: fitted dim 0.903, slopes max 0.467 / rms 0.414   (alpha/2 = 0.45)
  alpha=0.9, X=1e8, rand: fitted dim 0.900, max|E| 758.1 at the top block, slopes max 0.320 / rms 0.205
  alpha=0.7, X=1e8, ctrl: fitted dim 0.683, slopes max 0.420 / rms 0.323   (no evidence against it)
  alpha=0.5, X=1e8, ctrl: the rule stops deleting (no primes of S in the top blocks), and E grows linearly
Slopes are fitted on the last six dyadic blocks and scatter between runs.
"""
# tail = sum_{p>=P0} p^(alpha-2) ~ E1((1-alpha) log P0).  For p >= P0: delete p iff N(p-1)+1-a*p > tau.
import sys, math, numpy as np
from scipy.special import exp1
alpha = float(sys.argv[1]); X = int(float(sys.argv[2])); design = sys.argv[3]  # 'ctrl' or 'rand'
P0, tau, rng = 1000, 0.5, np.random.default_rng(1)
isp = np.ones(X + 1, bool); isp[:2] = False
for i in range(2, int(X**0.5) + 1):
    if isp[i]: isp[i*i::i] = False
primes = np.nonzero(isp)[0]
free = np.ones(X + 1, bool); free[0] = False
logprod = 0.0; S = []
for p in primes[primes < P0]:
    if rng.random() < p ** (alpha - 1):
        S.append(p); free[p::p] = False; logprod += math.log(1 - 1/p)
a = math.exp(logprod - exp1((1 - alpha) * math.log(P0)))
N = int(free[1:P0].sum()); last = P0 - 1
for p in primes[primes >= P0]:
    N += int(free[last + 1:p].sum()); last = p - 1          # N = N(p-1)
    if design == 'ctrl': delete = N + 1 - a * p > tau
    else: delete = rng.random() < p ** (alpha - 1)
    if delete: S.append(p); free[p::p] = False
# final error profile (free[] is now complete up to X)
Ncum = np.cumsum(free.astype(np.int64)); x = np.arange(X + 1)
if design == 'rand':   # use the realised density (finite-X proxy) for the random baseline
    a = math.exp(sum(math.log(1 - 1/q) for q in S) - exp1((1 - alpha) * math.log(X)))
E = Ncum - a * x
S = np.array(S)
print(f"design={design} alpha={alpha} X={X:.0e} a={a:.4f} #S={len(S)} share={len(S)/len(primes):.3f}")
js = range(13, int(math.log2(X)))
cnt, mx, rms = [], [], []
for j in js:
    seg = E[2**j:2**(j+1)]; c = ((S >= 2**j) & (S < 2**(j+1))).sum()
    cnt.append(c); mx.append(np.abs(seg).max()); rms.append(np.sqrt((seg**2).mean()))
    print(f"  j={j:2d}  #S={c:7d}  max|E|={mx[-1]:9.2f}  rms={rms[-1]:8.2f}")
jj = np.array(list(js)); last6 = slice(-6, None)
dim = np.polyfit(jj[last6], np.log2(np.array(cnt[last6]) * (jj[last6] + 0.5)), 1)[0]
smax = np.polyfit(jj[last6], np.log2(mx[last6]), 1)[0]; srms = np.polyfit(jj[last6], np.log2(rms[last6]), 1)[0]
print(f"  fitted dim={dim:.3f}  local slope max|E|={smax:.3f}  rms={srms:.3f}   alpha/2={alpha/2:.3f}  N0 floor min(a/2,1/4)={min(alpha/2,.25):.3f}  ctrl-heuristic={alpha*(1-alpha)/(2-alpha):.3f}")
