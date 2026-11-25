# Constructive Lean 4 Kernel and Exact Zero-Float Certificates for OpenAI's $\mathsf{VP} \neq \mathsf{VNP}$ Separation Preprint

**Author:** Lluis Eriksson  
**Protocol:** `VPVNP-CERT-1.0`  
**Licenses:** MIT (code, Lean 4 proofs, certificates) / CC-BY-4.0 (manuscript & figures)

## Overview

Independent, explicitly scoped, zero-floating-point two-layer verification companion for the discrete algebraic, wire-shortening hinge, replay–boundary contradiction, characteristic-$p$ Cartier extraction, signed-permutation Clifford involution, Gray-code windowed host, and integral exterior-algebra $\bigwedge\mathbb{Z}^4$ $11/12$ packet-crossing mechanisms of OpenAI's November 23, 2026 preprint *"VP and VNP are different"*.

- **Layer 1 (`lean/OpenAIVpVnpSeparation.lean`):** 18 standalone constructive Lean 4.35.0 sub-lemmas (`0` `sorry`, `0` custom `axiom`, `0` `Classical.choice`, `0` warnings; `2 none`, `2 [propext]`, `14 [propext, Quot.sound]`).
- **Layer 2 (`src/vpvnp_exact.py`, `src/vpvnp_certifier.py`):** Pure-stdlib Python `int`/`Fraction` zero-float auditor across 4 modes (`hinge_stretch_and_replay_cert`, `cartier_residue_box_cert`, `clifford_signed_perm_and_gray_cert`, `exterior_packet_11_12_squeeze_cert`).
- **Canonical Atlas & Red-Team Audit:** 16 canonical certificates verified (`0.023–5.445 ms`), `80/80` pytest checks (`74/74` live adversarial forgeries rejected with exact branch regexes), and full 41-file SHA-256 integrity manifest.

## Reproducibility (5-Gate Verification)

```bash
python scripts/run_all_experiments.py
python scripts/make_figures.py
python scripts/verify_all.py
```
