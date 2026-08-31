# The Commit Steward Protocol

**Status:** Operating procedure, formalizing a role performed manually in
chat across the 2026-08-26 through 2026-08-29 sessions. Written so the
role can be handed to an isolated Antigravity 2.0 SDK process, a
scheduled script, or any future agent session without re-deriving it
from scratch.

**Companion to:** `docs/arch/scaffold-agentic-architecture-review.md`,
which names this function "the Isolated Read-Only Commit Steward" in
its control-plane diagram and specifies the adopted ADK + Antigravity
mix in §7.0. This document is the steward's procedure; the ADK spine
starts it after the generator has exited and does not become it.

**Sequence 0 is not implemented.** Live unattended `--commit` still
fails four criteria. The guarantee that would close them:

> **The exact Git tree that passed the complete trusted verification
> ladder is the exact tree committed.**

1. **Verifies one state, commits another.** Ladder runs on the live
   worktree; then `git add -A` stages whatever exists. No immutable
   snapshot. Close: temp index → *T* → verify *T* → `commit-tree` /
   `update-ref` (Step 7 replacement).
2. **Verifier is inside the candidate change.** Worktree
   `scripts/lint_axioms.py` (or `lakefile.lean`, toolchain pins) can
   be the copy that blesses the same diff. Close: pinned verifier;
   trust-root diffs fail closed to human review.
3. **Unattended ladder is incomplete.** `verify_for_commit` omits
   `check_refutation_independence.py` and
   `check_public_reachability.py`. Close: the full Step 3 table as a
   versioned fail-closed manifest.
4. **No enforced internal time budget.** The 12-step brake is prompt
   guidance. Close: host wall-clock/CPU on the generator.

This protects against races, accidental edits, stale checks, and
runaway runs. It does not assume a malicious agent.

## 1. Why this role exists

`scripts/opencode-pursue` runs an autonomous agent with **no git
authority** — it cannot commit, push, or declare its own work verified
(`AGENTS.md` § Working rules: "Do not commit, push, publish, rewrite
history"). Something outside that agent has to actually stage, verify
independently, and commit. Across this project's history that
something has been a human pasting `git status` into a chat and an
assistant doing the rest. This document exists because that "the rest"
turned out to be a real, repeatable procedure with real failure modes
— each one caught in production, not hypothesized:

- **A run's own verification claim is not sufficient.** `check_build_completeness.py`
  itself exists because a full `lake build` once printed "Build
  completed successfully" over a three-error QA file
  (`proposals/verify-build-completeness.md`). The steward's rule is
  downstream of this: never commit on a run's self-report; re-run the
  ladder independently.
- **A run can do real, correct work and still not tell you.** Commit
  `b9717df` closes a case where a run delivered two complete,
  verified theorems (`edgePerturbation_lambda2_cheeger_floor`,
  `edgePerturbation_connectivity_bracket`, plus their `Cheeger.lean`
  engine pair) but exited before writing its own terminal
  `docs/AGENT_ACTIVITY.md` entry — the "records-gap pattern," recorded
  by the agent itself as recurring under this exact name in multiple
  earlier entries. A steward that only reads the log's "Status:"
  field would have either missed real work or committed it unverified.
- **A hand-maintained side-document drifts even while its own
  regeneration hook runs on every commit.** `docs/scaffold_map.svg`'s
  pre-commit hook regenerated the SVG on every commit for days while
  the underlying status table went stale (fixed in `9c32a77`) — the
  hook was necessary but not sufficient, because it could only
  re-render existing data, never check it against ground truth.
- **An axiom repair is not a normal diff.** Commit `a1e59ac` changed
  the actual mathematical content of four admitted axioms
  (`hoeffding_lemma`'s constant, `matrix_hoeffding`/`matrix_bernstein`/
  `matrix_azuma_hoeffding`'s missing `Nonempty` guard). A steward that
  diffs line counts cannot tell a cosmetic docstring edit from a
  correctness-critical hypothesis change; it has to read the actual
  mathematics and re-derive the trust consequences.

None of these are exotic. They are the default failure modes of
"trust the subordinate process's own report," and this protocol exists
specifically to not do that.

## 2. Two distinct responsibilities

**2.1 The mechanical verification gate** (§3) — runs every time the
autonomous agent produces uncommitted changes. Reads what happened,
re-verifies it independently, commits and pushes only what passes.
This is the routine, high-frequency loop.

**2.2 Strategic process review** (§4) — runs occasionally, triggered by
noticing that a policy, a piece of tooling, or a documentation surface
has itself drifted or is inadequate — not a Lean correctness issue, a
process one. Examples from this project's own history: the README's
Status section growing into an unreadable 8,168-character wall of text
(`9f356d3`), the transit map's hand-maintained data going stale for
four days (`9c32a77`), or noticing that two axiom repairs shared a
pattern serious enough to need a standing checklist and a linter
(`c9b730d`, `f94bc12`). This responsibility requires judgment about
scope (fix directly vs. write a proposal vs. ask the human) that §4
makes explicit rather than leaving implicit.

Both responsibilities share one constraint: **never assert something
is verified without having independently run the check that verifies
it.** A steward that reads a claim and believes it has performed the
same function as a steward that reads no records at all.

## 3. Procedure: the mechanical verification gate

### Step 0 — Liveness check (live; insufficient — see Adopted Sequence 0)

```sh
scripts/isrunning
```

Prefer this over a raw `ps aux | grep -i opencode` — it also reports,
when idle, the launchd schedule's next expected fire time (from the
plist's `StartInterval` and the most recent run log) and whether the
Z.ai quota threshold has been reached, both of which a bare process
grep can't answer. Fall back to `ps aux | grep -i opencode | grep -v
grep` only if the script itself is unavailable.

If a run is active, **stop here.** Do not verify or commit against a
tree a live process may still be writing to. Re-check on the next
trigger rather than polling in a tight loop.

If nothing is running, proceed. Note the process being absent is not
proof the tree is stable for the whole duration of what follows — see
Step 6. **This check plus Step 6's one-second status diff is not an
atomic lock** (architecture review R-07, R-13). Sequence 0 replaces both
with a temporary index, tree OID *T* (`write-tree` serializes the
index, not the worktree), verification of a checkout of *T*,
`C=$(git commit-tree T -p P)`, and `git update-ref <ref> C P`.
A cooperative lock is not a substitute for that compare-and-swap.
Planned, not implemented.

### Step 1 — Read every unverified delivery record, in full

```sh
git status --short
grep -n "^## <today's date pattern>" docs/AGENT_ACTIVITY.md
```

Read each matching entry completely, not just its milestone line —
`Changes`, `Verification`, `Remaining risk`, and `Next handoff`. If
`git status` shows changes from more than one run since the last
verified commit, read all of them before acting on any — a later
entry's "Next handoff" often explains why an earlier one's plan
changed mid-stream.

**Do not stop at the first "in-progress" entry and assume there is
nothing to verify.** Cross-check its content against Step 2 before
concluding that.

### Step 2 — Cross-check the record against the actual diff

```sh
git diff --stat
```

Compare the file list against what the record's own `Changes` section
claims. Two specific failure shapes to watch for, both observed in
production:

- **A "terminal" entry with a smaller diff than it should have** — a
  records-gap in the other direction: the log claims completion but a
  planned file is untouched. Read the actual diff of every file the
  record names before trusting the claim.
- **An "in-progress" entry whose plan is fully realized on disk** — the
  records-gap pattern of `b9717df`. If every file and theorem name the
  plan lists is present and the tree builds, treat this as a real,
  completed delivery requiring the same verification as a terminal
  entry (see Step 7's closing-note procedure), not as unfinished work
  to wait on.

If a claimed file doesn't exist, or a file changed that no entry
mentions, stop and investigate before proceeding — do not silently
verify around the discrepancy.

### Step 3 — The verification ladder

Run every one of these, regardless of how small the change looks.
Record the actual output, not a paraphrase.

```sh
lake build
python3 scripts/check_build_completeness.py
python3 scripts/lint_axioms.py
python3 scripts/check_refutation_independence.py
python3 scripts/check_public_reachability.py
python3 scripts/check_scaffold_map_freshness.py   # only strictly required
                                                    # when a proposal's
                                                    # status header changed,
                                                    # but cheap enough to
                                                    # run every time
python3 scripts/check_citations.py
python3 scripts/check_markdown_links.py
```

Pass bar, exactly:

| Check | Pass condition |
| --- | --- |
| `lake build` | "Build completed successfully"; new warnings, if any, match ones the record's own `Verification` section names as pre-existing — confirm by eye, don't assume |
| `check_build_completeness.py` | `N source files, N fresh artifacts, 0 stale, 0 missing` |
| `lint_axioms.py` | exit 0; any `Allowlisted:` lines are pre-existing entries, not new unexplained ones |
| `check_refutation_independence.py` | `OK: N tagged refutation/fence declarations checked; none consumes the axiom it refutes` |
| `check_public_reachability.py` | `OK: public umbrella import closure is N repo modules; no non-public (wip.*) module reachable` |
| `check_scaffold_map_freshness.py` | exit 0 |
| `check_citations.py` | "All axioms have proper citations!" |
| `check_markdown_links.py` | "No broken local Markdown links" |

A record claiming these passed is not a substitute for running them.
Every commit in this project's history that cites a verification
ladder was re-run by the steward before being trusted, not copied from
the agent's own log.

The live `--commit` wrapper's `verify_for_commit` currently **omits**
`check_refutation_independence.py` and `check_public_reachability.py`
(architecture review R-09). Sequence 0 makes this entire table a
versioned fail-closed manifest and runs the Python steps from a
**pinned** verifier (last trusted commit or image), not from a
worktree the generator may have edited. Unattended `--commit` fails
closed (human review) if the **trust root** changed: `scripts/`
(including the verification manifest), `lakefile.lean`,
`lake-manifest.json`, `lean-toolchain`, and tracked hooks or other
Lake/toolchain pins — not only `scripts/` and `lakefile.lean`.
Planned, not implemented.

### Step 4 — Escalated verification for high-stakes changes

Trigger this step when the diff touches any of:

- an `axiom` declaration's hypotheses or conclusion (not just its
  docstring),
- a file under `Scaffold/Mathlib/**` that an existing consumer
  depends on,
- anything the record itself flags as a repair, a retirement, or a
  "found materially false" finding.

For each headline theorem the record names as newly delivered or
newly repaired, independently re-derive its trust cost — do not read
the record's `#print axioms` claim, reproduce it:

```sh
cat > wip/verify_<topic>.lean << 'EOF'
import <the module>
#print axioms <Namespace>.<theorem_name>
EOF
lake env lean wip/verify_<topic>.lean
rm -f wip/verify_<topic>.lean
```

Confirm the axiom list matches exactly what the record claims — no
more, no fewer. This step caught nothing wrong in this project's
history (every claim checked out), which is itself the point: the
value of independent verification is proportional to how often it
*could* have caught something, not to how often it did.

For an actual axiom-statement change, additionally read the real diff
of the axiom file and of every file the record says had a guard or
hypothesis "threaded through" — confirm the threading is real (a new
hypothesis actually appears in the consumer's signature, or is
genuinely derived internally without a signature change) rather than
asserted.

### Step 5 — `sorry`/`admit` sweep

```sh
git diff --name-only | grep '\.lean$'
git status --short | grep '^??' | grep '\.lean$'
grep -n "sorry\|admit" <every file from both lists> \
  | grep -viE "no.?sorry|no.?admit|not admitted|admitted axiom|materially false"
```

The exclusion pattern is load-bearing: this codebase's own docstrings
discuss admitted axioms constantly ("no `sorry`/`admit`", "previously
admitted as an axiom"), so a blind grep is mostly noise. Read every
surviving hit; a real `sorry` or `admit` tactic use is disqualifying
regardless of what else passed.

### Step 6 — Stability check immediately before staging

```sh
git status --short --porcelain > /tmp/pre_commit_status.txt
sleep 1
diff <(cat /tmp/pre_commit_status.txt) <(git status --short --porcelain) && echo STABLE
scripts/isrunning
```

A verification ladder takes real wall-clock time (a full `lake build`
is minutes, not seconds). Confirm nothing changed underneath it and
that no new run has started before staging — this is the check that
makes Step 0's liveness check still valid several minutes later.

### Step 7 — Commit and push

If Step 1 found a real records-gap (a completed delivery with no
terminal log entry), close it first: append an operator closing note
to the `AGENT_ACTIVITY.md` entry, naming what was independently
re-verified, before treating the delivery as ready to commit — never
commit real work with no record of it having happened, and never
invent a record without having actually run Step 3/4/5 yourself.

Stage everything the verified delivery touched:

```sh
git add -A
git commit -m "<message>"
git push origin main
```

**Adopted Sequence 0 replacement for this step (not implemented):**
`git write-tree` serializes the **index**, not the working tree. Do not
`git add -A` / `git commit` on the live worktree after the ladder.

```sh
# After generators (scoreboard, etc.) have finished — or prove they
# leave T unchanged:
export GIT_INDEX_FILE=/tmp/scaffold-verify.index
git read-tree HEAD
git add -A
T=$(git write-tree)
# pinned ladder against a checkout of T, not this worktree
C=$(git commit-tree "$T" -p "$P" -m "$message")   # P = current tip
git update-ref refs/heads/main "$C" "$P"          # atomic; fails if tip ≠ P
```

The steward may veto; a passing steward verdict is not a condition of
this commit. `update-ref C P` is the compare-and-swap against an
outside writer; a cooperative lock is not a substitute.

Commit message content, every time:
- what changed (the theorem/tool/proposal, one line each if there are
  several unrelated deliveries in one batch),
- the exact verification ladder results (build target count, QA
  before/after, axiom count, which checks passed),
- for axiom-touching changes: which axioms, old vs. new hypothesis
  shape, and the independent `#print axioms` result from Step 4,
- attribution trailer matching this project's existing convention
  (`Co-Authored-By:` / `Claude-Session:`).

Push immediately after each verified commit rather than batching —
this project's history shows `origin/main` kept continuously in sync
with the verified local state, not held back.

### Failure handling

If any ladder step fails: **do not commit any part of the batch.**
Diagnose from the actual error, not from a guess. If the fix is
docs-only and mechanical (a stale cross-reference, a missing
allowlist entry), fix it directly and re-run the full ladder before
committing. If the fix requires Lean or mathematical judgment, that is
the autonomous agent's job, not the steward's — leave the tree
uncommitted, do not attempt the mathematics yourself under this role.

## 4. Procedure: strategic process review

### Triggers

- A human directly asks a question that only makes sense if something
  has drifted ("is this what a first-time visitor wants to read?",
  "why does the map say X when Y happened weeks ago?").
- While performing §3, noticing the *documentation about* a delivery
  is inconsistent with the delivery itself, independent of whether the
  Lean content is correct.
- Noticing the same defect class recur twice — this project's own
  standing rule (`docs/2_ARCHITECTURE.md` §5's hazard checklist was
  written specifically because the same missing-guard shape broke two
  separate axiom families in one week).

### Decision: fix directly, write a proposal, or escalate to the human

| Scope of the fix | Action |
| --- | --- |
| Docs-only, reversible, mechanically checkable (`check_markdown_links`, `check_citations`) | Fix directly, verify, commit under this role — no proposal needed. Examples: `9f356d3` (README compression), `9c32a77` (map staleness), `b84f6d5` (map station additions) |
| Requires new Lean content, a proof, or real mathematical judgment | Write a proposal in `proposals/`, index it in `proposals/README.md`'s Active priority table at an honest tier, and let the autonomous agent's own Step 0 discipline take it from there. Do not write the Lean yourself under this role. Examples: `c9b730d` (the degenerate-corner audit proposals), the multiway hard-direction proposal |
| A judgment call only the human can make (adopt a new research direction, accept a scope tradeoff, spend real money/time) | Ask directly. Do not write a proposal that presumes the answer, and do not act as if silence is consent — see `alon-boppana-bound.md`'s own pre-adoption Gate pattern, which this project already uses for exactly this case |

### Verification bar for direct fixes

Even a "docs-only" fix gets the same discipline as §3, scaled to what's
actually touched: run `check_markdown_links.py` and `check_citations.py`
at minimum; run `check_scaffold_map_freshness.py` if a proposal status
or the map's own data changed; do the Step 6 stability check before
committing. "It's just docs" is not license to skip verification — it
is license to skip the Lean-specific steps that don't apply.

## 5. What this role does not do

- **Does not judge mathematical correctness beyond what the kernel and
  the ladder check.** Whether an axiom's citation accurately
  transcribes the cited paper's theorem is a human/domain-expert
  question (`docs/2_ARCHITECTURE.md` §8: "The citation checker is a
  hygiene tool. Human mathematical review remains necessary.") — the
  steward confirms a citation exists and is formatted correctly, not
  that it's the right citation.
- **Does not write Lean.** Escalated verification (§3.4) reads and
  re-derives; it does not patch. A verification failure that needs a
  mathematical fix goes back to the autonomous agent via a proposal or
  a direct handoff note, not into an ad hoc Lean edit under this role.
- **Does not commit on a schedule regardless of state.** The gate is
  triggered by the presence of verified, uncommitted work — an idle
  agent with nothing to verify is not a failure to fix.
- **Does not treat one prior approval as standing authorization** for
  a different or larger action — pausing/resuming the LaunchAgent,
  force-pushing, or any destructive git operation still needs its own
  explicit instruction each time, per this project's general safety
  posture, independent of this protocol.

## 6. Operationalizing this as an agentic flow

This document is written to be mechanically followable, which is what
makes it portable off of "a human pastes `git status` into chat":

- **As an isolated Antigravity 2.0 SDK process**: the steward is a
  sibling started by trusted host code after the pursuit agent has
  exited — not a child `invoke_subagent` of the generator (dynamic
  subagents inherit parent permissions). Configure `google.antigravity`
  deny-by-default: allow `view_file` / grep and host-owned verification
  tools only; deny `run_command`, `write_to_file`, and git. The model
  returns a structured verdict (`commit` / `wait` / `escalate`, plus
  Conventional Commit subject and records-gap flags). The host
  validates that verdict and is the only process that runs `git add` /
  `git commit` / `git push`. `agy -p` is not this role: print mode
  auto-approves writes, and `--sandbox` does not block `write_file`.
- **§3 as a linear procedure**: pass/fail bars and no branching that
  requires creative judgment except Step 4's "is this high-stakes"
  trigger list and §4's three-way scope decision — both are checklists,
  not open questions. Escalate to a human exactly at the two points
  this document names one (§3's Failure Handling for Lean-judgment
  fixes; §4's third row for human-only decisions). Antigravity's
  `ask_user` policy is the hook for that third row.
- **As a scheduled check**: Step 0 through Step 7 can run on an SDK
  `every(N)` trigger or a filesystem watch of `.opencode/runs/`, rather
  than waiting for a human to notice `git status` has changes. Step 0
  (`scripts/isrunning`) still gates the rest.
- **What would still need a human in the loop even fully automated**:
  §4's human-decision row, and any Step 3/4 failure whose diagnosis
  concludes the autonomous agent's own proposal or math is wrong in a
  way that needs a strategic redirection rather than a retry.

The live `--commit` path in `scripts/opencode-pursue` still uses a
thinner Codex subject-line stand-in (`codex exec --ephemeral --sandbox
read-only`). This section names the Google-stack steward as an
**advisory** Sequence 3 target; it does not claim the wrapper has
already been retargeted, and it does not make the steward an
authorizer. **Advisory means veto or escalate only:** after the
deterministic ladder has passed on tree *T*, a passing steward
verdict is never the positive condition that authorizes `commit-tree T`.
SDK deny-policies are not OS isolation (R-10). When the Sequence 0
host gate in `docs/arch/scaffold-agentic-architecture-review.md` §7.0
exists, that gate verifies and commits *T*; ADK (Sequence 2) may wrap
the gate later and still must not give this process git.

Nothing here presumes that retargeting exists yet. It is written so
that building it is a mechanical translation of this document, not a
fresh design exercise.

## Revision history

- 2026-08-29 — Initial version, written after roughly a dozen verify-
  and-commit cycles performed manually in a single chat session,
  formalizing the procedure that had by then stabilized in practice.
- 2026-08-30 — §6 names an isolated Antigravity 2.0 Python SDK process
  (`google.antigravity`, deny-by-default, host-only git) as the
  steward runtime; records that the live `--commit` wrapper is still
  the thinner Codex subject-line stand-in.
- 2026-08-30 — Companion and §6 note the adopted ADK + Antigravity mix
  (`scaffold-agentic-architecture-review.md` §7.0): ADK launches this
  steward after the generator exits; ADK does not absorb the role.
- 2026-08-30 — Sequence 0 planning: exclusive lock + snapshot replaces
  Step 0/6; pinned verifier + full ladder; steward is advisory only.
  No wrapper change in this revision.
- 2026-08-30 — A− regrade: Step 7 adopted replacement is `commit-tree`
  of the verified tree OID; trust root includes `lean-toolchain`,
  `lake-manifest.json`, hooks, and the verification manifest; steward
  is veto-only, never the go-signal.
- 2026-08-30 — Step 7 recipe made index-explicit: temporary
  `GIT_INDEX_FILE`, `write-tree` → *T*, `commit-tree T -p P`,
  `update-ref <ref> C P`; generators before *T*.
- 2026-08-30 — Sequence 0 acceptance is the four live failures: verify
  vs commit mismatch; verifier in the candidate tree; incomplete
  ladder; prompt-only time budget. Transactional guarantee is the
  one-sentence test.
