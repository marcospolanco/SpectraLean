# Repository Scripts

These scripts maintain documentation and policy metadata; they do not replace Lean compilation or mathematical review.

| Script | Purpose |
| --- | --- |
| `generate_qa_scoreboard.py` | Regenerate source-derived counts in `docs/5_QA_SCOREBOARD.md`. |
| `check_markdown_links.py` | Check repository-local links in active Markdown documentation. |
| `lint_axioms.py` | Report axiom placement and index-coverage issues. |
| `check_citations.py` | Check public axioms for the required citation-comment form. |
| `opencode-pursue` | Run the project pursuit agent non-interactively with GLM-5.3 at high reasoning effort. |

## Autonomous OpenCode run

The project configuration defines a `scaffold` primary agent and a `pursue` command. Run the next high-leverage milestone with:

```sh
scripts/opencode-pursue
```

Add optional direction as arguments:

```sh
scripts/opencode-pursue "repair build reachability before theorem work"
```

The wrapper enables OpenCode's `--auto` mode. Explicit project denials still block external-directory access, destructive Git operations, commits, pushes, pull-request publication, `sudo`, and direct `rm -rf` commands. These rules are guardrails, not an operating-system sandbox; run autonomous agents only in a reviewed worktree.
