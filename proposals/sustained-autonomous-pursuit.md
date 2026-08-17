# Proposal: Sustained Autonomous Scaffold Pursuit

**Status:** Proposed; no configuration or agent-behavior changes applied by this document.

## Goal

Run OpenCode as a long-horizon implementation agent that keeps advancing
Scaffold from the spectral graph theory (SGT) center outward, across
multiple sessions, until it consumes an explicitly allocated run budget or
reaches a hard blocker.

Broad refactors are authorized when they are the highest-leverage path—not
treated as exceptional behavior.

## Design

### 1. Persistent execution ledger and activity log

Add two durable, versioned reporting artifacts:

`docs/EXECUTION_PLAN.md` is a compact current-state ledger. It would track:

- current active milestone and rationale;
- ranked ready queue, ordered by SGT leverage;
- blocked work with exact evidence;
- last verification results; and
- next concrete action.

`docs/AGENT_ACTIVITY.md` is an append-only, human-readable activity log.
It would let an operator follow a live or unattended run without reading a
model transcript. Each entry records:

- UTC timestamp, run/session identifier, and milestone identifier;
- the intent and its SGT-leverage rationale;
- files or subsystems being investigated or changed;
- commands run, with a concise outcome and links to fuller captured output
  where relevant;
- decisions made, including why a refactor was chosen over a narrower edit;
- verification completed, remaining risk, and the immediate next action; and
- a terminal status: `in-progress`, `completed`, `blocked`, `interrupted`,
  or `superseded`.

At the beginning of each run, the agent writes an `in-progress` entry before
editing. It appends an update after each coherent milestone and always writes
a terminal entry before a normal exit. It should summarize rather than dump
chain-of-thought, credentials, environment secrets, or unbounded command
output. A failed provider response is itself reportable evidence, not a reason
to leave the operator guessing.

The runner would also maintain local, ignored raw transcripts under
`.opencode/runs/` (for example, one timestamped stdout/stderr file per
invocation) and print their paths. The Markdown activity log is the durable
repository-facing summary; raw transcripts are optional diagnostic evidence
and must not be committed.

The agent updates the ledger and activity log after every coherent milestone.
This makes continuation reliable even when OpenCode compacts context or a
provider request fails.

### 2. Explicit sustained-pursuit instructions

Update `AGENTS.md` and `.opencode/prompts/scaffold.txt` to state:

- complete the active milestone, then select the next ready high-leverage
  milestone;
- cross-module refactors are permitted when needed to repair a load-bearing
  dependency;
- prefer build reachability, real definitions, valid theorem shapes, and
  citation fidelity before expanding theory breadth;
- continue until the run budget is exhausted or a hard blocker is recorded;
  and
- do not stop merely because the task needs several files or several
  iterations.

They would also require the reporting cadence above: declare intent before
editing, update the activity log at milestone boundaries, and leave a final
operator-facing status on every exit path.

### 3. Bounded continuation runner

Extend `scripts/opencode-pursue` with a run budget:

```sh
scripts/opencode-pursue --runs 10
```

Behavior:

```text
first run:  /pursue
later runs: resume the same OpenCode session
stop:       after N runs, a hard blocker, or explicit operator interruption
```

This is safer and more legible than an unlimited loop. OpenCode's current
configuration supports tool-step limits, but not a native project
token-budget setting; repeated resumptions are the practical budget
mechanism.

### 4. Milestone boundaries

Each run should work through one or more ready milestones, in this order:

1. Build reachability and toolchain compatibility.
2. Invalid imports, source layout, and umbrella exports.
3. Placeholder definitions and meaningless statement shapes.
4. Citation/index coverage and QA alignment.
5. Reusable SGT interfaces.
6. Perturbation/concentration bridges.
7. Dynamic persistence and x90 application work.

The agent may refactor broadly within a milestone, but must record why the
work outranks nearer alternatives.

### 5. Safety and review

Keep the existing denials:

- no commits, pushes, PR publication, or external-directory access;
- no destructive Git commands or broad deletion; and
- no claims that axiom-backed results are foundationally proved.

Add a stop condition: if the agent repeats the same failed command or has
no source change for a defined number of steps, it records the blocker in
the execution ledger and ends that run rather than waiting indefinitely on a
provider response.

## Expected operator workflow

```sh
scripts/opencode-pursue --runs 10
```

Then review:

```sh
git diff
cat docs/EXECUTION_PLAN.md
tail -n 120 docs/AGENT_ACTIVITY.md
cat docs/5_QA_SCOREBOARD.md
```

For a live tail, an operator could use:

```sh
tail -f docs/AGENT_ACTIVITY.md
```

Resume with directed priority when needed:

```sh
scripts/opencode-pursue --runs 5 \
  "prioritize complete direct compilation of the SGT core"
```

## Acceptance criteria for implementation

- A run writes durable progress and blockers to the execution ledger.
- Every run declares its intent before editing and leaves a terminal,
  human-readable activity-log entry with verification and next action.
- The activity log makes the active milestone, rationale, changed area, and
  current state understandable without opening an OpenCode transcript.
- Raw provider/command transcripts are captured locally, ignored by Git, and
  linked from the corresponding activity entry when useful.
- A bounded run budget executes and resumes the same OpenCode session.
- The runner exits cleanly on a completed milestone, exhausted budget, or
  documented hard blocker.
- Existing project-local safety denials remain enforced.
- Operator documentation explains cost, interruption, resumption, and review.
