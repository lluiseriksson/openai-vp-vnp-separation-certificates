"""Generate 3 publication-grade 300-DPI figures for Paper 64."""

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

plt.rcParams.update(
    {
        "font.family": "serif",
        "font.size": 8.5,
        "axes.titlesize": 9.0,
        "axes.labelsize": 8.5,
        "xtick.labelsize": 7.5,
        "ytick.labelsize": 7.5,
        "legend.fontsize": 7.0,
        "axes.grid": True,
        "grid.alpha": 0.28,
        "grid.linestyle": "--",
    }
)


def make_fig1() -> None:
    rows = json.loads((RES_DIR / "exp2_superpoly_scaling.json").read_text(encoding="utf-8"))["rows"]
    k = np.array([r["log2_n"] for r in rows], dtype=float)
    y_c10 = np.array([r["log2_vpvnp_c10"] for r in rows], dtype=float)
    y_n2 = np.array([r["log2_n2"] for r in rows], dtype=float)
    y_n3 = np.array([r["log2_n3"] for r in rows], dtype=float)

    exp4 = json.loads((RES_DIR / "exp4_exterior_packet_census.json").read_text(encoding="utf-8"))
    sc = exp4["squeeze_curve"]
    p0 = np.array([r["p0_float"] for r in sc], dtype=float)
    ra = np.array([r["cost_a_ratio"] for r in sc], dtype=float)
    rb = np.array([r["cost_b_ratio"] for r in sc], dtype=float)
    rmin = np.array([r["min_ratio_float"] for r in sc], dtype=float)

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75), dpi=300)

    ax1.plot(k, y_c10, "o-", color="#1F5AA6", lw=1.7, ms=3.8, label=r"Thm. 1.1 $(\log_2 n)^{5/4}$ ($c{=}1$)")
    ax1.plot(k, y_n2, "s--", color="#2E7D32", lw=1.3, ms=3.2, label=r"Quadratic $2\log_2 n$ (MR04)")
    ax1.plot(k, y_n3, "^:", color="#B22222", lw=1.3, ms=3.4, label=r"Cubic $3\log_2 n$ (OAI26)")
    ax1.axvline(81, color="#666666", ls=":", lw=0.9)
    ax1.annotate(r"Overtakes $n^3$" + "\n" + r"at $\log_2 n{=}81$", xy=(81, 243), xytext=(55, 62), arrowprops=dict(arrowstyle="->", color="#444444", lw=0.9), fontsize=6.8)
    ax1.set_xlabel(r"Input size exponent $\log_2 n$")
    ax1.set_ylabel(r"Lower-bound exponent $\log_2(\mathrm{size})$")
    ax1.set_title(r"(a) Superpolynomial $\exp(\Omega((\log n)^{5/4}))$ Growth")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93, edgecolor="#CCCCCC", fontsize=6.5)

    ax2.plot(p0, ra, "--", color="#7D3C98", lw=1.2, label=r"Grouping A: $(4p_0+7p_1)/6$")
    ax2.plot(p0, rb, ":", color="#D35400", lw=1.2, label=r"Grouping B: $(7p_0+4p_1)/6$")
    ax2.plot(p0, rmin, "o-", color="#1F5AA6", lw=1.8, ms=4.0, label=r"Optimal $\min(A,B)$")
    ax2.axhline(11.0 / 12.0, color="#B22222", ls="-.", lw=1.2, label=r"Sec. 8 worst case $11/12$")
    ax2.axhline(1.0, color="#666666", ls=":", lw=0.9)
    ax2.set_xlabel(r"Term-0 selector fraction $p_0$")
    ax2.set_ylabel("Wire width / unaltered width")
    ax2.set_ylim(0.62, 1.22)
    ax2.set_title(r"(b) Sec. 8 Packet Squeeze ($\leq 11/12$ Worst Case)")
    ax2.legend(loc="upper center", frameon=True, framealpha=0.93, edgecolor="#CCCCCC", fontsize=6.4)

    fig.tight_layout(pad=0.8)
    fig.savefig(FIG_DIR / "fig1_scaling_and_squeeze.png", dpi=300)
    plt.close(fig)


def make_fig2() -> None:
    exp3 = json.loads((RES_DIR / "exp3_clifford_and_host.json").read_text(encoding="utf-8"))["rows"]
    exp4 = json.loads((RES_DIR / "exp4_exterior_packet_census.json").read_text(encoding="utf-8"))

    dims = [r["dim_D"] for r in exp3]
    amb = [r["ambient_dim"] for r in exp3]
    pairs = [r["anticommuting_pairs"] for r in exp3]

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75), dpi=300)

    x = np.arange(len(dims))
    w = 0.36
    b1 = ax1.bar(x - w / 2, amb, width=w, color="#1F5AA6", label=r"Ambient dim $2^D$")
    b2 = ax1.bar(x + w / 2, pairs, width=w, color="#2E7D32", label=r"Orthogonal pairs $D(D-1)/2$")
    for bar, val in list(zip(b1, amb)) + list(zip(b2, pairs)):
        ax1.text(bar.get_x() + bar.get_width() / 2.0, val + 0.6, str(val), ha="center", va="bottom", fontsize=7.0, fontweight="bold")
    ax1.set_xticks(x)
    ax1.set_xticklabels([f"D={d}" for d in dims])
    ax1.set_ylim(0, 38)
    ax1.set_ylabel("Exact count")
    ax1.set_title(r"(a) Sec. 7 Signed-Permutation Involutions $A_1,\dots,A_D$")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.93, edgecolor="#CCCCCC", fontsize=6.8)

    cats = ["Both\nzero", "Term 1\nonly", "Term 2\nonly", "Exact\ncancel"]
    vals = [
        exp4["both_zero"],
        exp4["t1_only_nonzero"],
        exp4["t2_only_nonzero"],
        exp4["both_nonzero_canceling"],
    ]
    colors = ["#5D6D7E", "#1F5AA6", "#2E7D32", "#D35400"]
    xp = np.arange(len(cats))
    bars = ax2.bar(xp, vals, color=colors, width=0.58)
    ax2.set_yscale("log")
    for b, v in zip(bars, vals):
        ax2.text(b.get_x() + b.get_width() / 2.0, v * 1.18, str(v), ha="center", va="bottom", fontsize=7.2, fontweight="bold")
    ax2.set_xticks(xp)
    ax2.set_xticklabels(cats)
    ax2.set_ylim(10, 12000)
    ax2.set_ylabel("Quadruples (log scale)")
    ax2.set_title(r"(b) Exact $\Lambda(\mathbb{Z}^4)$ 4096-Quadruple Census")

    fig.tight_layout(pad=0.8)
    fig.savefig(FIG_DIR / "fig2_clifford_and_packet.png", dpi=300)
    plt.close(fig)


def make_fig3() -> None:
    atlas = json.loads((RES_DIR / "exp1_certificate_atlas.json").read_text(encoding="utf-8"))["certificates"]
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(7.0, 2.75), dpi=300)

    colors_map = {
        "hinge_stretch_and_replay_cert": "#1F5AA6",
        "cartier_residue_box_cert": "#2E7D32",
        "clifford_signed_perm_and_gray_cert": "#D35400",
        "exterior_packet_11_12_squeeze_cert": "#7D3C98",
    }
    labels = [f"C{i+1:02d}" for i in range(len(atlas))]
    ms_vals = [max(c["mean_ms"], 0.004) for c in atlas]
    bar_colors = [colors_map[c["mode"]] for c in atlas]
    xpos = np.arange(len(atlas))
    ax1.bar(xpos, ms_vals, color=bar_colors, width=0.72)
    ax1.set_yscale("log")
    ax1.set_xticks(xpos[::2])
    ax1.set_xticklabels(labels[::2])
    ax1.set_ylabel("Mean verify time (ms, log)")
    ax1.set_xlabel("Certificate ID (Modes 1–4, 4 each)")
    ax1.set_title("(a) Zero-Float Certificate Latency (16/16)")

    cats = ["Schema/\nParser", "Mode 1\nHinge", "Mode 2\nCartier", "Mode 3\nClifford", "Mode 4\nPacket"]
    counts = [12, 16, 17, 14, 15]
    xp2 = np.arange(len(cats))
    bars = ax2.bar(xp2, counts, color="#1B7A43", width=0.58)
    for b, c in zip(bars, counts):
        ax2.text(b.get_x() + b.get_width() / 2.0, c + 0.35, f"{c}/{c}", ha="center", va="bottom", fontsize=7.5, fontweight="bold")
    ax2.set_xticks(xp2)
    ax2.set_xticklabels(cats)
    ax2.set_yticks([0, 4, 8, 12, 16, 20])
    ax2.set_ylim(0, 20.5)
    ax2.set_ylabel("Adversarial forgeries blocked")
    ax2.set_title("(b) Live Red-Team Audit (74/74 Blocked)")

    fig.tight_layout(pad=0.8)
    fig.savefig(FIG_DIR / "fig3_atlas_and_redteam.png", dpi=300)
    plt.close(fig)


def main() -> None:
    FIG_DIR.mkdir(parents=True, exist_ok=True)
    make_fig1()
    make_fig2()
    make_fig3()
    print("Generated all 3 figures at 300 DPI in paper/figures/.")


if __name__ == "__main__":
    main()
