# Repository Scripts

These scripts maintain documentation and policy metadata; they do not replace Lean compilation or mathematical review.

| Script | Purpose |
| --- | --- |
| `generate_qa_scoreboard.py` | Regenerate source-derived counts in `docs/5_QA_SCOREBOARD.md`. |
| `check_markdown_links.py` | Check repository-local links in active Markdown documentation. |
| `lint_axioms.py` | Report axiom placement and index-coverage issues. |
| `check_citations.py` | Check public axioms for the required citation-comment form. |
| `opencode-pursue` | Run or resume bounded non-interactive pursuit sessions with GLM-5.3 at high reasoning effort. |

## Autonomous OpenCode run

The project configuration defines a `scaffold` primary agent and a `pursue` command. Run the next high-leverage milestone with:

```sh
scripts/opencode-pursue --runs 1
```

Add optional direction as arguments:

```sh
scripts/opencode-pursue --runs 5 \
  "restore the next concentration module and its closest QA consumer"
```

The first invocation creates an OpenCode session. Later invocations resume the
exact locally recorded session, rather than whichever session happens to be
most recent. `--runs N` is the explicit budget: a successful run may continue
into the next one until N runs complete; a failed run stops immediately.

Follow the durable, versioned progress reports with:

```sh
cat docs/EXECUTION_PLAN.md
tail -f docs/AGENT_ACTIVITY.md
```

Raw stdout/stderr transcripts are written under ignored `.opencode/runs/`, and
the locally stored session ID is `.opencode/pursue-session`. They are useful
for diagnosis but must not be committed.

The wrapper enables OpenCode's `--auto` mode. Explicit project denials still block external-directory access, destructive Git operations, commits, pushes, pull-request publication, `sudo`, and direct `rm -rf` commands. These rules are guardrails, not an operating-system sandbox; run autonomous agents only in a reviewed worktree.

The agent records intent before edits and compact milestone/exit summaries in
`docs/AGENT_ACTIVITY.md`. If progress stalls, it records evidence in the
activity log and execution plan rather than silently waiting indefinitely.
