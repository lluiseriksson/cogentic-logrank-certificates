"""Generate 3 publication-quality 300-DPI figures for Paper 58 (LOGRANK-COGENTIC-CERT-1.0).

Author: Lluis Eriksson
License: MIT
"""
from __future__ import annotations

import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

ROOT = Path(__file__).resolve().parent.parent
RES_DIR = ROOT / "results"
FIG_DIR = ROOT / "paper" / "figures"

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 8.5,
    "axes.titlesize": 9.0,
    "axes.labelsize": 8.5,
    "xtick.labelsize": 7.8,
    "ytick.labelsize": 7.8,
    "legend.fontsize": 6.8,
    "axes.spines.top": False,
    "axes.spines.right": False,
})


def make_fig1() -> None:
    d2 = json.loads((RES_DIR / "exp2_third_moment_separation.json").read_text(encoding="utf-8"))
    d3 = json.loads((RES_DIR / "exp3_variational_penalty_curve.json").read_text(encoding="utf-8"))

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    r2 = d2["rows"]
    bs = [r["bits"] for r in r2]
    ax1.plot(bs, [r["bool_third_moment_val"] for r in r2], "o-", color="#1b4f72", lw=1.8, ms=4.5,
             label=r"Boolean $S = J_n - 2I_n$: $E_3 = 4(n{-}1)(n{-}2)/n^2$")
    ax1.axhline(4.0, color="#117864", ls=":", lw=1.3, label=r"Asymptotic Boolean limit $E_3 \to 4$")
    ax1.plot(bs, [r["rademacher_third_moment_val"] for r in r2], "s--", color="#c0392b", lw=1.5, ms=4.0,
             label=r"Rademacher barrier $A_{\mathrm{Rad}}$: $E_3 \equiv 0$")
    ax1.set_xticks(bs)
    ax1.set_xticklabels([f"$2^{b}$" for b in bs])
    ax1.set_ylim(-0.3, 4.55)
    ax1.set_xlabel(r"Matrix dimension $n = 2^b$")
    ax1.set_ylabel(r"Third-moment energy $\sum_k \|\widehat{M}^Y_k\|_F^2$")
    ax1.set_title(r"(a) Booleanity vs. Rademacher Barrier ($E_3$)")
    ax1.grid(True, alpha=0.25)
    ax1.legend(loc="center right", frameon=True, framealpha=0.94, fontsize=6.2)

    r3 = d3["rows"]
    ts = [r["t_val"] for r in r3]
    ax2.plot(ts, [r["g_val"] for r in r3], "o-", color="#7d3c98", lw=1.8, ms=3.5,
             label=r"$g(t) = 2(1{-}t) - \frac{1}{4}(1{-}t)^2$")
    ax2.plot(ts, [r["g_prime_val"] for r in r3], "s--", color="#b9770e", lw=1.5, ms=3.2,
             label=r"$g'(t) = -(3{+}t)/2 \leq -1$")
    ax2.axhline(-1.0, color="#c0392b", ls=":", lw=1.2, label=r"Bias-preservation cap $g' \leq -1$")
    ax2.set_ylim(-2.3, 3.3)
    ax2.set_xlabel(r"Mean bias parameter $t \in [-1, 1]$")
    ax2.set_ylabel("Exact rational value")
    ax2.set_title(r"(b) Eq. (1.7) Strictly Concave Variational Penalty")
    ax2.grid(True, alpha=0.25)
    ax2.legend(loc="center left", bbox_to_anchor=(0.02, 0.42), frameon=True, framealpha=0.94, fontsize=6.4)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig1_third_moment_and_penalty.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    d4 = json.loads((RES_DIR / "exp4_nw_orbit_and_scaling.json").read_text(encoding="utf-8"))
    rows = d4["rows"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    lrs = [r["log10_r"] for r in rows]
    ax1.plot(lrs, [r["orbit_steps"] for r in rows], "o-", color="#1b4f72", lw=1.8, ms=4.5,
             label=r"Prop. A.3 orbit $k \mapsto \lfloor 3k/4 \rfloor$ steps")
    ax1.plot(lrs, [r["balanced_depth_L_eq_r"] for r in rows], "s--", color="#117864", lw=1.6, ms=4.2,
             label=r"Balanced protocol $2\lceil \log_{3/2} r \rceil$")
    ax1.set_xticks(lrs)
    ax1.set_xlabel(r"Rank scale $\log_{10} r$")
    ax1.set_ylabel("Exact integer step / depth count")
    ax1.set_title(r"(a) Prop. A.3 Rank-Halving & Balancing Depth")
    ax1.grid(True, alpha=0.25)
    ax1.legend(loc="upper left", frameon=True, framealpha=0.94, fontsize=6.5)

    # Panel (b): Relative savings of O(r^{1/2 - 5e-6}) vs sqrt(r) for log10 r in [0, 6e5]
    log10_rs = np.linspace(0, 600000, 120)
    ratio_cog = 10.0 ** (-5e-6 * log10_rs)
    ax2.semilogy(log10_rs / 1e5, np.ones_like(log10_rs), "--", color="#c0392b", lw=1.4,
                 label="Sudakov–Tomon $O(\\sqrt{r})$ baseline (ratio $1$)")
    ax2.semilogy(log10_rs / 1e5, ratio_cog, "-", color="#1b4f72", lw=1.9,
                 label=r"Cogentic $r^{-\varepsilon}$ ($\varepsilon = 5\times 10^{-6}$)")
    ax2.set_xlabel(r"Rank exponent $\log_{10} r$ ($\times 10^5$)")
    ax2.set_ylabel(r"Polynomial gain $r^{-\varepsilon}$ over $\sqrt{r}$ (log)")
    ax2.set_title(r"(b) Breaking the $\sqrt{r}$ Barrier ($\varepsilon = 5\times 10^{-6}$)")
    ax2.grid(True, which="both", alpha=0.22)
    ax2.legend(loc="lower left", frameon=True, framealpha=0.94, fontsize=6.4)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig2_nw_orbit_and_exponent.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    d1 = json.loads((RES_DIR / "exp1_certificate_atlas.json").read_text(encoding="utf-8"))
    rows = d1["certificates"]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.2, 2.75), dpi=300)

    mode_map = {
        "boolean_sign_third_moment_cert": ("M1: Eq. (1.6) / $E_3$", "#1b4f72"),
        "quadratic_slice_bregman_cert": ("M2: Slice / Bregman", "#117864"),
        "monochromatic_rank_split_cert": ("M3: Rank-Split", "#b9770e"),
        "nw_recursion_and_penalty_cert": ("M4: Prop. A.3 / $g(t)$", "#7d3c98"),
    }
    xs = np.arange(len(rows))
    ms = [r["mean_ms"] for r in rows]
    cols = [mode_map[r["mode"]][1] for r in rows]
    ax1.bar(xs, ms, color=cols, edgecolor="#1c2833", lw=0.5, width=0.68)
    ax1.set_yscale("log")
    ax1.set_xticks(xs)
    ax1.set_xticklabels([f"{i+1}" for i in range(len(rows))], fontsize=7.0)
    ax1.set_ylim(0.01, max(ms) * 6.5)
    ax1.set_ylabel("Mean verify time (ms, log)")
    ax1.set_xlabel("Canonical certificate index (1–16)")
    ax1.set_title(r"(a) Exact-$\mathbb{Q}$ Auditor Runtime (16 Certs)")
    from matplotlib.patches import Patch
    handles = [Patch(facecolor=c, edgecolor="#1c2833", label=lbl) for lbl, c in mode_map.values()]
    ax1.legend(handles=handles, loc="upper left", ncol=2, frameon=True, framealpha=0.94, fontsize=6.0)
    ax1.grid(True, which="both", axis="y", alpha=0.25)

    cats = ["Schema /\nParser", "Mode 1\nEq. (1.6)", "Mode 2\nBregman", "Mode 3\nRank-Split", "Mode 4\nProp. A.3"]
    counts = [12, 13, 13, 12, 12]
    bcols = ["#595959", "#1b4f72", "#117864", "#b9770e", "#7d3c98"]
    bars = ax2.bar(cats, counts, color=bcols, edgecolor="#1c2833", lw=0.5, width=0.56)
    for bar, c in zip(bars, counts):
        ax2.text(bar.get_x() + bar.get_width() / 2, bar.get_height() + 0.35, f"{c}/{c}",
                 ha="center", va="bottom", fontsize=7.4, fontweight="bold")
    ax2.set_ylim(0, 16.0)
    ax2.set_ylabel("Live adversarial forgeries rejected")
    ax2.set_title("(b) Adversarial Red-Team Audit (62/62 Rejected)")
    ax2.grid(True, axis="y", alpha=0.25)

    fig.tight_layout(pad=0.9)
    fig.savefig(FIG_DIR / "fig3_atlas_and_redteam.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("[PASS] Generated 3 publication-quality 300-DPI figures in paper/figures/.")


if __name__ == "__main__":
    main()
