# Scaffold Agent Instructions

## Mission

Advance Scaffold as a disciplined, axiom-transparent Lean research substrate centered on spectral graph theory. Work radiates outward from load-bearing SGT definitions and theorem interfaces toward perturbation and concentration bridges, dynamic spectral persistence, and finally x90 applications.

## Read first

- `README.md` for purpose, maturity, and the center-out policy.
- `docs/1_STRATEGY.md` for prioritization.
- `docs/2_ARCHITECTURE.md` for the trust model and contribution contract.
- `docs/5_QA_SCOREBOARD.md` for the last recorded verification state.
- `governance/CONTRIBUTING.md` before changing public APIs.

## Priority order

1. Restore honest, comprehensive build reachability.
2. Repair invalid imports and source-layout defects.
3. Replace `True`, constant, and admitted placeholders with meaningful SGT definitions or theorem shapes.
4. Reduce the explicit trust surface and improve citation/index coverage.
5. Strengthen reusable SGT QA and bridge interfaces.
6. Advance dynamic persistence and application work only when its inner dependencies are credible.

Choose the smallest coherent milestone that unlocks the most downstream SGT progress per unit of complexity. When outer work exposes an inner defect, move inward and fix the load-bearing dependency first.

## Working rules

- Inspect `git status` before editing and preserve unrelated changes.
- Do not edit `research/archive/` except archive metadata.
- Use Mathlib types and conventions where practical.
- Public assumptions must be explicit axioms with precise citations; do not hide them behind `sorry`.
- QA may contain no `sorry` or `admit`, and must not be presented as validation of an axiom's truth.
- Do not add breadth without naming the SGT obligation or consumer it unlocks.
- Do not commit, push, publish, rewrite history, or perform broad deletion.
- Never access or modify files outside this worktree.

## Verification

Run checks proportionate to the change. The current default build is known to fail, so distinguish baseline failures from regressions.

```sh
python3 scripts/generate_qa_scoreboard.py
python3 scripts/lint_axioms.py
python3 scripts/check_citations.py
python3 scripts/check_markdown_links.py
lake build
```

For Lean changes, directly build or elaborate every changed module and its closest QA consumer; do not rely only on the umbrella target.
