# Constructive Lean 4 Kernel and Exact-Rational Certificates for Google Research Cogentic's $O(r^{1/2 - 5\times 10^{-6}})$ Log-Rank Conjecture Proof

**Author:** Lluis Eriksson (prepared with transparent AI assistance via Google Antigravity)
**Target Reference:** Google Research Cogentic (Nov. 25, 2026), *Breaking the Square-Root Barrier for the Log-Rank Conjecture* (`github.com/google-research/google-research/tree/master/cogentic_research_papers`, harness `arXiv:2609.40324`).
**Licenses:** Manuscript & figures (`paper/main.tex`, `paper/main.pdf`, `paper/figures/*.png`) under `CC-BY-4.0`; code, Lean 4 proofs, and exact certificates under `MIT`.

## Highlights
- **Zero-Dependency Constructive Lean 4.35.0 Kernel (`lean/CogenticLogRank.lean`):** 18 theorems, `0` `sorry`, `0` `axiom`, `0` `Classical.choice`, `0` warnings (`4` zero-axiom `none` + `14` `[propext, Quot.sound]`), mechanizing Eq. (1.6) pointwise Booleanity, degree-1 AM–GM barrier vs. degree-2 $\cosh$-tilt $\lambda^2$-cancellation, Eq. (1.7) variational penalty concavity/slope, scalar/eigenvalue Eq. (2.2) Bregman nonnegativity, exact $2\times 2$ commutator trace identity, inductive Lemma 2.1(1) leverage defect, universal 2D Hermite $c_2$ covariance, and every discrete combinatorial step of Proposition A.3 ($2^{11} < 3^7$, $3\cdot 29^4 < 4\cdot 27^4$, rank-split $\lfloor 3k/4\rfloor$, $750 C_0 = 178{,}500$).
- **Exact-$\mathbb{Q}$ Auditor (`LOGRANK-COGENTIC-CERT-1.0`, `src/logrank_certifier.py`):** Zero-float pure-stdlib `Fraction` verifier across four modes (including exact top-mode ordering $s_1 \ge \sigma_1$ and exact rational PSD verification $R \succeq 0$ via symmetric congruence reduction), certifying 16 canonical witnesses (`0.099–16.937 ms`)—including an exact isospectral separation between Boolean $S = J_4 - 2I_4$ ($E_3 = 3/2$, hollow slice energy $3/32$) and the exact integer-valued Eq. (1.4) Rademacher barrier $A_{\mathrm{Rad}}$ ($E_3 = 0$, hollow slice energy $0$)—and rejecting **62/62 live adversarial forgeries** with exact branch regex assertions (`66/66` pytest tests passing in `0.12 s`).

## Quick Reproduction
```bash
# Run all 5 verification gates (zero-float hygiene, Lean 4 axiom audit, 16 certs, 66 pytest, 41-file SHA-256)
python scripts/verify_all.py

# Optional: regenerate all 16 certificates, 4 exact result JSONs, and 3 300-DPI figures
python scripts/run_all_experiments.py
python scripts/make_figures.py
```
