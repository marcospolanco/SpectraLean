#!/usr/bin/env python3
"""Regenerate docs/scaffold_map.svg from the data table below.

This is a static, single-theme snapshot (no <script>, no CSS variables,
no interactivity) so it renders directly in GitHub's Markdown viewer via
a plain <img> tag. The clickable, hoverable version lives at
docs/scaffold_map.html and carries the same data independently.

Each station carries an optional `source` naming the proposals/*.md file
whose status it tracks (None where no proposal exists -- classical core
entries and not-yet-proposed stations). scripts/check_scaffold_map_freshness.py
reconciles this table against docs/scaffold_map.html, the QA scoreboard's
generated numbers, and each cited proposal's own **Status:** line -- so
"update both by hand when a proposal's status changes" is now enforced
mechanically rather than remembered.
"""
import math

STATUS = {
    "proved":   {"label": "Proved (hard crust)", "color": "#1D6B4A", "fill": True,  "dash": None},
    "axiom":    {"label": "Admitted axiom, cited", "color": "#8A5A12", "fill": True,  "dash": None},
    "progress": {"label": "In progress",          "color": "#6A3FA0", "fill": True,  "dash": None},
    "open":     {"label": "Proposed, authorized", "color": "#4B5359", "fill": False, "dash": None},
    "gated":    {"label": "Gated on a decision",  "color": "#8A8378", "fill": False, "dash": "3,3"},
}

# Core landmarks are all "proved" by construction (the roster header says
# so); the second tuple element is the optional proposals/*.md source that
# tracks the landmark's delivery record, or None.
CORE = [
    ("Courant–Fischer", "prove-courant-fischer.md"),
    ("Cauchy Interlacing", None),
    ("Cheeger — easy direction", "prove-cheeger-easy-direction.md"),
    ("Cheeger — hard direction", "discharge-perturbation-axioms.md"),
    ("Weyl's Inequality", "discharge-perturbation-axioms.md"),
    ("Davis–Kahan sin Θ", "discharge-perturbation-axioms.md"),
    ("Thomson's Principle", "electrical-flow-routing.md"),
    # Foster's Theorem has no clean single source: spectral-graph-sparsification.md
    # mixes "Phase A DELIVERED" with "Phase B blocked" in one status line, which the
    # freshness check would classify as gated. Deliberately unlinked, and visible
    # in that check's no-source coverage list.
    ("Foster's Theorem", None),
]

SPOKES = [
    ("BERNOULLI HEIGHTS", "Probability & High-Dim Stats", [
        ("Normalized Laplacians", "proved", "mixing-time-bound.md"),
        ("Walk–Similarity Bridge", "proved", "mixing-time-bound.md"),
        ("Spectral Gap Transfer", "proved", "mixing-time-bound.md"),
        ("MCMC Mixing Time", "proved", "mixing-time-bound.md"),
        ("Subgaussian Tail Bound", "proved", "prove-subgaussian-tail-bound.md"),
        ("Finite Relative Entropy", "proved", "finite-relative-entropy.md"),
        ("Doeblin Contraction Engine", "proved", "retire-primitive-power-convergence.md"),
        ("Field-Standard TV Mixing", "proved", "total-variation-mixing-conversion.md"),
        ("Mixing-Time Object Family", "proved", "directed-uniform-mixing-time.md"),
        ("Adversarial Fence Audits", "proved", "adversarial-fences-entropy-family.md"),
        # Admitted-axiom station: the audit proposal tracking these axioms is
        # still Proposed, so linking it would misclassify; the admission itself
        # predates the proposal system's delivery records.
        ("Matrix Concentration", "axiom", None),
    ]),
    ("APPLICATION RING", "Consumers of the core", [
        ("Fiedler Partitioning", "proved", "fiedler-partitioning.md"),
        ("Fiedler-Subspace Stability", "proved", "fiedler-subspace-stability-davis-kahan.md"),
        ("Empirical Stationary Distribution", "proved", "empirical-stationary-distribution-concentration.md"),
        ("Vertex-Degree Concentration", "proved", "hoeffding-inequality-degree-concentration.md"),
        ("Ramanujan Expansion Ceiling", "proved", "ramanujan-expansion-ceiling.md"),
    ]),
    ("KURAMOTO JUNCTION", "Dynamical Systems & Control", [
        ("Perron–Frobenius", "axiom", "admit-perron-frobenius.md"),
        ("Directed Operators", "proved", "directed-graph-operators.md"),
        ("Heat Semigroup", "proved", "reversibility-and-heat-semigroup.md"),
        ("Heat — Phase C", "proved", "reversibility-and-heat-semigroup.md"),
        ("Discrete Affine Convergence", "proved", "discrete-affine-convergence.md"),
        ("Consensus & Sync.", "gated", None),
    ]),
    ("KIRCHHOFF FLATS", "Statistical Physics", [
        ("Electrical Flow", "proved", "electrical-flow-routing.md"),
        ("Effective Resistance", "proved", "electrical-structure-crust.md"),
        ("Dirichlet Energy", "proved", "electrical-structure-crust.md"),
        ("Weighted Matrix-Tree", "gated", "weighted-matrix-tree-theorem.md"),
    ]),
    ("OPEN FRONTIER", "Landmark theorems", [
        ("Alon–Boppana Bound", "proved", "alon-boppana-bound.md"),
        ("Approx. Spectral Projection", "proved", "approximate-spectral-projection.md"),
        ("Higher-Order Cheeger — easy direction", "proved", "multiway-expansion.md"),
        ("Higher-Order Cheeger — hard direction", "gated", "multiway-cheeger-hard-direction.md"),
        ("Degree Eigenvalue Sandwich", "proved", "degree-eigenvalue-sandwich.md"),
    ]),
    ("NEURIPS BAY", "ML & Graph Signal Processing", [
        ("Resolvent Calculus", "proved", "resolvent-calculus-psd.md"),
        ("Band Projectors", "proved", "spectral-band-projectors.md"),
        ("Tikhonov Filter", "proved", "tikhonov-shrinkage-filter.md"),
        ("Tikhonov — Phase 2", "proved", "hermitian-calculus-consumer-tikhonov-heat.md"),
        ("Decidable Certificates", "proved", "decidable-spectral-certificates.md"),
    ]),
    ("STOC CITY", "Theoretical CS & Algorithms", [
        ("Leverage Scores", "proved", "spectral-sparsification-via-leverage-scores.md"),
        ("Matrix Chernoff Bridge", "proved", "spectral-sparsification-via-leverage-scores.md"),
        ("Edge-Perturbation Concentration", "proved", "matrix-hoeffding-spectral-gap-estimation.md"),
        ("Swept-Fiedler-Cut Capstone", "proved", "matrix-hoeffding-spectral-gap-estimation.md"),
        ("Subspace-Stability Pipeline", "proved", "matrix-hoeffding-spectral-gap-estimation.md"),
    ]),
]

PAPER = "#F3F4EE"
INK = "#22282B"
INK_SOFT = "#4B5359"
INK_FAINT = "#7A817F"
RULE = "#9AA39A"
ACCENT = "#1F6F78"
ACCENT_SOFT = "#DCE9E7"

W, H = 2000, 2020
CX, CY = 1000, 1220
CORE_R = 116
STATION_GAP = 82
STATION_START = 260

parts = []


def esc(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def dot(x, y, status, r=7):
    s = STATUS[status]
    fill = s["color"] if s["fill"] else PAPER
    dash = f' stroke-dasharray="{s["dash"]}"' if s["dash"] else ""
    parts.append(
        f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r}" fill="{fill}" '
        f'stroke="{s["color"]}" stroke-width="2"{dash}/>'
    )


def label(x, y, text, anchor, cls="node"):
    sizes = {"node": (14, INK), "sub": (11, INK_FAINT), "title": (17, INK), "hub": (19, INK)}
    size, color = sizes[cls]
    weight = ' font-weight="700"' if cls in ("title", "hub") else ""
    parts.append(
        f'<text x="{x:.1f}" y="{y:.1f}" text-anchor="{anchor}" font-size="{size}" '
        f'fill="{color}"{weight} font-family="ui-monospace,Consolas,monospace">{esc(text)}</text>'
    )


parts.append(f'<svg viewBox="0 0 {W} {H}" xmlns="http://www.w3.org/2000/svg" role="img" '
             f'aria-label="Hub-and-spoke map of Scaffold\'s spectral graph theory core and its '
             f'seven research axes, colored by proof status">')
parts.append(f'<rect x="0" y="0" width="{W}" height="{H}" fill="{PAPER}" stroke="{RULE}" stroke-width="2"/>')

# ---- title block ----
parts.append(f'<text x="36" y="52" font-size="32" font-weight="700" fill="{INK}" '
             f'font-family="ui-sans-serif,Helvetica,Arial,sans-serif">SCAFFOLD TRANSIT MAP</text>')
parts.append(f'<text x="36" y="78" font-size="14" fill="{INK_SOFT}" '
             f'font-family="ui-monospace,Consolas,monospace">A hub-and-spoke reading of the SGT core and the seven axes it feeds, colored by proof status.</text>')
parts.append(f'<text x="36" y="102" font-size="13" fill="{INK_FAINT}" '
             f'font-family="ui-monospace,Consolas,monospace">Repo-wide: 4 explicit axioms &#183; 1380 functional theorems &#183; 6866 QA declarations &#183; 0 sorries &#8212; as of working tree, 2026-09-07</text>')

# ---- legend ----
lx = 36
ly = 132
for key in ["proved", "axiom", "progress", "open", "gated"]:
    s = STATUS[key]
    fill = s["color"] if s["fill"] else PAPER
    dash = f' stroke-dasharray="{s["dash"]}"' if s["dash"] else ""
    parts.append(f'<circle cx="{lx+6}" cy="{ly}" r="6" fill="{fill}" stroke="{s["color"]}" stroke-width="2"{dash}/>')
    parts.append(f'<text x="{lx+18}" y="{ly+4}" font-size="13" fill="{INK_SOFT}" '
                 f'font-family="ui-monospace,Consolas,monospace">{esc(s["label"])}</text>')
    lx += 22 + 8.2 * len(s["label"]) + 28

parts.append(f'<line x1="24" y1="150" x2="{W-24}" y2="150" stroke="{RULE}" stroke-width="1"/>')

# ---- SGT Core roster (a plain list, not radial -- 8 short-radius spokes
# were unreadably cramped against the map's inner ring) ----
roster_x, roster_y = 36, 186
parts.append(f'<text x="{roster_x}" y="{roster_y}" font-size="15" font-weight="700" fill="{INK}" '
             f'font-family="ui-sans-serif,Helvetica,Arial,sans-serif">SGT CORE — proved, hard crust</text>')
col_w = 300
for i, (name, _source) in enumerate(CORE):
    col, row = divmod(i, 4)
    x = roster_x + col * col_w
    y = roster_y + 30 + row * 24
    parts.append(f'<circle cx="{x+5}" cy="{y-5}" r="5" fill="{STATUS["proved"]["color"]}"/>')
    label(x + 16, y, name, "start", "node")

parts.append(f'<line x1="24" y1="{roster_y+30+4*24+14}" x2="{W-24}" y2="{roster_y+30+4*24+14}" stroke="{RULE}" stroke-width="1"/>')

# ---- hub ----
parts.append(f'<circle cx="{CX}" cy="{CY}" r="{CORE_R}" fill="{ACCENT_SOFT}" stroke="{ACCENT}" stroke-width="2.5"/>')
label(CX, CY - 4, "SGT CORE", "middle", "hub")
label(CX, CY + 18, f"{len(CORE)} proved landmarks", "middle", "sub")

# ---- spokes ----
# Angles are assigned by matching station count to how vertical the ray
# is (|sin|), not by fixed compass position: a near-horizontal ray gives
# consecutive stations almost no vertical separation, so axes with many
# stations need the more-vertical slots or their labels pile up.
n = len(SPOKES)
raw_angles = [-90 + i * (360 / n) for i in range(n)]
by_verticality = sorted(range(n), key=lambda i: -abs(math.sin(math.radians(raw_angles[i]))))
by_station_count = sorted(range(n), key=lambda i: -len(SPOKES[i][2]))
angle_for = {}
for rank, spoke_idx in enumerate(by_station_count):
    angle_for[spoke_idx] = raw_angles[by_verticality[rank]]

for i, (axis_label, axis_sub, stations) in enumerate(SPOKES):
    angle_deg = angle_for[i]
    a = math.radians(angle_deg)
    dx, dy = math.cos(a), math.sin(a)
    side = 1 if dx >= 0 else -1

    # Near-horizontal rays give consecutive stations almost no vertical
    # separation for a fixed radial gap; widen the radial gap for those
    # axes specifically so station labels keep at least ~22px of it.
    gap = max(STATION_GAP, 22 / max(abs(dy), 0.05))
    last_r = STATION_START + (len(stations) - 1) * gap + 30
    line_start_r = CORE_R + 12
    parts.append(
        f'<line x1="{CX+dx*line_start_r:.1f}" y1="{CY+dy*line_start_r:.1f}" '
        f'x2="{CX+dx*last_r:.1f}" y2="{CY+dy*last_r:.1f}" stroke="{RULE}" stroke-width="3"/>'
    )

    for j, (name, status, _source) in enumerate(stations):
        r = STATION_START + j * gap
        x, y = CX + dx * r, CY + dy * r
        dot(x, y, status)
        label(x + 13 * side, y + 5, name, "start" if side > 0 else "end")

    # Title sits at the end of the ray but is nudged vertically clear of
    # it by a fixed amount (not scaled by dx/dy) so near-horizontal rays
    # -- where consecutive stations, and therefore the title, land close
    # in y -- don't run the title into the last station's own label.
    tr = last_r + 40
    tx, ty0 = CX + dx * tr, CY + dy * tr
    vsign = -1 if dy < 0 else 1
    label(tx, ty0 + vsign * 30, axis_label, "middle", "title")
    label(tx, ty0 + vsign * 50, axis_sub, "middle", "sub")

parts.append('</svg>')

svg = "\n".join(parts)
out_path = "docs/scaffold_map.svg"
with open(out_path, "w") as f:
    f.write(svg)
print(f"wrote {out_path} ({len(svg)} bytes)")
