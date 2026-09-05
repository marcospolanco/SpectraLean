# Repository Scripts

These scripts maintain documentation and policy metadata; they do not replace Lean compilation or mathematical review.

| Script | Purpose |
| --- | --- |
| `generate_qa_scoreboard.py` | Regenerate source-derived counts in `docs/5_QA_SCOREBOARD.md`. |
| `check_markdown_links.py` | Check repository-local links in active Markdown documentation. |
| `lint_axioms.py` | Report axiom placement and index-coverage issues, and run the degenerate-corner guard check: flag every `Scaffold/Mathlib` axiom whose signature carries a `Fintype`-carried index type or a `Measure` argument with no visible guard, unless the script's allowlist records why the corner is accepted (run it before a new axiom lands; settle the allowlist entry at admission time). Also runs the replacement-path check: every `Scaffold/Mathlib` axiom's docstring must carry a labeled `Replacement path:` note naming what would retire it. |
| `check_refutation_independence.py` | Fail if any QA declaration tagged `-- @refutes: <axiom>` has a proof term depending on the axiom it refutes ("a refutation cannot consume what it refutes"); tags must name a currently admitted axiom. Runs `#print axioms` through a generated `lake env lean` file, so it needs built oleans. |
| `check_public_reachability.py` | Fail if any module under `wip/` (the only non-public Lean directory) is reachable, directly or transitively, from the public umbrella `Scaffold.lean`, or if any `wip.*` import appears in a public module. Purely static import-graph walk. |
| `check_citations.py` | Check public axioms for the required citation-comment form. |
| `check_build_completeness.py` | Fail if any `Scaffold/**/*.lean` source has a missing or mtime-stale `.olean` artifact — run after every full `lake build` (a successful exit alone does not certify on-disk sources). |
| `check_scaffold_map_freshness.py` | Fail if the transit map's two data tables (`scripts/generate_scaffold_map_svg.py` and `docs/scaffold_map.html`) disagree with each other, with the QA scoreboard's generated numbers, or with a cited proposal's own `**Status:**` line — a delivery that changes a proposal's status header is not verified until this passes (the pre-commit hook runs it report-only). |
| `check_backlog_freshness.py` | Fail if `docs/6_SGT_BACKLOG.md`'s `**Last reviewed:**` date has fallen more than 7 days behind the latest `docs/AGENT_ACTIVITY.md` entry. A clock check, not a content check — it catches nobody-has-looked-recently, not stale prose within an otherwise-recently-touched document. |
| `check_qa_name_uniqueness.py` | Fail if any named top-level declaration appears in more than one module under `Scaffold/QA/` within the same namespace — the latent defect class behind the 2026-09-05 `edgeAdj` lattice repair (QA modules are leaf builds, so a cross-module duplicate only fails when some future module imports both). Residual duplicates are allowlisted with their exact file sets; any new collision or any drift in an allowlisted set fails until settled deliberately. Doc comments are stripped, so prose is never matched. |
| `zquota` | Query Z.ai quota and provide an automation-safe start gate. |
| `opencode-pursue` | Run or resume bounded non-interactive pursuit sessions with GLM-5.3 at high reasoning effort. |
| `isrunning` | Check whether `opencode-pursue` is running (with start time) or determine when it will run next. |
| `io.github.marcospolanco.scaffold-pursue.plist` | Per-user macOS LaunchAgent template for hourly quota-aware pursuit. |

## Autonomous OpenCode run

The project configuration defines a `scaffold` primary agent and a `pursue` command. Run the next high-leverage milestone with:

```sh
scripts/opencode-pursue --runs 1
```

Add optional direction as trailing arguments. Quote the whole direction as one
argument; it reaches the agent as `$ARGUMENTS` in the `pursue` command
template defined in `opencode.json`:

```sh
scripts/opencode-pursue \
  -- "restore the next concentration module and its closest QA consumer"
```

Each invocation creates a fresh OpenCode session by default. Pass `--resume`
to continue the exact locally recorded session, rather than whichever session
happens to be most recent. `--runs N` is the explicit budget: within that one
invocation, a successful run may continue into the next one until N runs
complete; a failed run stops immediately.

### A direction pins the invocation to one run

`--runs` may not exceed 1 alongside an operator direction; the wrapper exits 2
rather than clamping silently. Every run in a `--runs N` loop receives the same
trailing arguments, and runs 2..N resume the session created by run 1 — so a
repeated direction restates an instruction the agent has already carried out,
inviting redundant work or a completed instruction read as newly issued.

Continue a directed pursuit undirected. Run 1 records its session ID, so the
direction stays in the session history instead of being restamped onto each
prompt, and you see run 1's result before committing budget to the rest:

```sh
scripts/opencode-pursue -- "advance proposals/<name>.md, step 1 only"
scripts/opencode-pursue --runs 4 --resume
```

### Verified automatic commit

Pass `--commit` to have the wrapper commit a completed, verified pursuit
without a manual handoff. It requires the worktree to be clean before the
pursuit begins. After its final successful run, the wrapper confirms the
latest activity status is `completed`, runs the standard scoreboard, hygiene,
and Lean-build checks, and asks a separate read-only Codex CLI session to
produce one validated Conventional Commit subject. The shell wrapper—not the
model—then stages and commits the resulting changes.

```sh
scripts/opencode-pursue --runs 1 --commit
```

The commit phase fails closed and leaves the worktree uncommitted if the agent
does not report `completed`, validation fails, Codex is unavailable, or Codex
returns an invalid commit subject. Existing OpenCode permission denies for
`git commit`, `git push`, and publication remain unchanged.

### Quota gate

`opencode-pursue` runs `zquota` before every new pursuit run. If any reported
quota is at least 80% used, it reports the reset time, starts no agent, and
exits 75. The wrapper never sleeps or retries in place.

Use `zquota` by itself for a readable status, `zquota --json` for a stable
machine-readable result, or `zquota --quiet` when only its status matters.
Its statuses are `0` (ready), `10` (threshold reached), and `1` (configuration,
network, or response error). Scope a diagnostic to token limits with
`zquota --scope tokens`; set a different gate with either
`scripts/opencode-pursue --quota-threshold 70` or `ZQUOTA_THRESHOLD=70`.

`opencode-pursue` also passes `--log-file .opencode/quota-history.jsonl` on
every check, so each invocation appends one JSON-lines record (independent of
`--json`/`--quiet`) — a queryable history of quota usage over time, gitignored
since it's local operational data, not repository content.

### Hourly macOS wake-up

The checked-in [LaunchAgent template](io.github.marcospolanco.scaffold-pursue.plist)
runs one quota-aware pursuit at load and then hourly. If the quota gate is
closed, that invocation exits 75; `launchd` makes the next attempt. It avoids
an idle terminal process and survives terminal closure, crashes, and reboots.

Install it explicitly for the current user:

```sh
mkdir -p "$HOME/Library/LaunchAgents"
cp scripts/io.github.marcospolanco.scaffold-pursue.plist \
  "$HOME/Library/LaunchAgents/io.github.marcospolanco.scaffold-pursue.plist"
launchctl bootstrap "gui/$(id -u)" \
  "$HOME/Library/LaunchAgents/io.github.marcospolanco.scaffold-pursue.plist"
```

Inspect it with `launchctl print "gui/$(id -u)/io.github.marcospolanco.scaffold-pursue"`.
To stop it, run `launchctl bootout "gui/$(id -u)" \
"$HOME/Library/LaunchAgents/io.github.marcospolanco.scaffold-pursue.plist"`.

Follow the durable, versioned progress reports with:

```sh
cat docs/EXECUTION_PLAN.md
tail -f docs/AGENT_ACTIVITY.md
```

Raw stdout/stderr transcripts are written under ignored `.opencode/runs/`, and
the locally stored session ID for an optional future `--resume` is
`.opencode/pursue-session`. They are useful for diagnosis but must not be
committed.

The wrapper enables OpenCode's `--auto` mode. Explicit project denials still block external-directory access, destructive Git operations, commits, pushes, pull-request publication, `sudo`, and direct `rm -rf` commands. These rules are guardrails, not an operating-system sandbox; run autonomous agents only in a reviewed worktree.

The agent records intent before edits and compact milestone/exit summaries in
`docs/AGENT_ACTIVITY.md`. If progress stalls, it records evidence in the
activity log and execution plan rather than silently waiting indefinitely.
