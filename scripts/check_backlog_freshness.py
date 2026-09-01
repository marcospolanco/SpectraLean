#!/usr/bin/env python3
"""Check that `docs/6_SGT_BACKLOG.md`'s "Last reviewed" date isn't
stale relative to the delivery log.

Provenance: the commit steward found the backlog's reviewed date stuck
at August 17, 2026 on 2026-09-01, while dozens of completed autonomous
deliveries had landed since (Poincare, the heat-variance/mixing/entropy
cascade, the spectral mixing floor, ...). Several of the backlog's own
item openings were left describing gates as "conditional" or "entirely
absent" long after those gates were satisfied, because nothing forced a
reconciliation pass. `check_scaffold_map_freshness.py` solves the exact
same problem for the transit map by cross-checking structured station
data; this backlog is free prose, not a structured table, so a content
checker isn't cheaply buildable. What *is* cheaply buildable, and closes
the actual failure mode observed, is a clock check: has this document's
own "Last reviewed" date fallen behind the delivery log by more than a
reasonable review cadence.

This is a coarse, mechanical check. It catches "nobody has looked at
this in weeks despite continuous delivery," not "every claim in it is
still accurate." Passing this check is necessary, not sufficient, for
the backlog being current -- a human or the commit steward still has to
actually read and reconcile it when this fails.

The check: parse the backlog's "**Last reviewed:** <Month DD, YYYY>"
header line, find the most recent `## <ISO-8601 timestamp> --- ...`
delivery heading anywhere in `docs/AGENT_ACTIVITY.md`, and fail if the
gap exceeds STALENESS_THRESHOLD_DAYS.
"""

import re
import sys
from datetime import datetime
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
BACKLOG = REPO / "docs" / "6_SGT_BACKLOG.md"
ACTIVITY_LOG = REPO / "docs" / "AGENT_ACTIVITY.md"

# How many days the backlog's reviewed date may lag the latest delivery
# before this fails. Chosen to catch drift well before it becomes the
# multi-week, dozens-of-deliveries gap this check was built in response
# to, without firing on every single delivery during an active stretch.
STALENESS_THRESHOLD_DAYS = 7

REVIEWED_RE = re.compile(
    r"\*\*Last reviewed:\*\*\s*([A-Za-z]+ \d{1,2},\s*\d{4})"
)
ACTIVITY_HEADING_RE = re.compile(
    r"^##\s+(\d{4}-\d{2}-\d{2})T\d{2}:\d{2}:\d{2}Z\s+—",
    re.MULTILINE,
)


def parse_month_day_year(text: str) -> datetime:
    return datetime.strptime(text.strip(), "%B %d, %Y")


def main() -> int:
    if not BACKLOG.is_file():
        print(f"FAIL: {BACKLOG} does not exist", file=sys.stderr)
        return 1
    if not ACTIVITY_LOG.is_file():
        print(f"FAIL: {ACTIVITY_LOG} does not exist", file=sys.stderr)
        return 1

    backlog_text = BACKLOG.read_text(encoding="utf-8")
    reviewed_match = REVIEWED_RE.search(backlog_text)
    if not reviewed_match:
        print(
            "FAIL: could not find a '**Last reviewed:** <Month DD, YYYY>' "
            f"line near the top of {BACKLOG}",
            file=sys.stderr,
        )
        return 1

    try:
        reviewed_date = parse_month_day_year(reviewed_match.group(1))
    except ValueError as exc:
        print(
            f"FAIL: could not parse backlog reviewed date "
            f"'{reviewed_match.group(1)}': {exc}",
            file=sys.stderr,
        )
        return 1

    activity_text = ACTIVITY_LOG.read_text(encoding="utf-8")
    heading_dates = ACTIVITY_HEADING_RE.findall(activity_text)
    if not heading_dates:
        print(
            f"FAIL: found no dated '## <timestamp> — ...' headings in "
            f"{ACTIVITY_LOG}",
            file=sys.stderr,
        )
        return 1

    latest_activity_date = max(
        datetime.strptime(d, "%Y-%m-%d") for d in heading_dates
    )

    gap_days = (latest_activity_date - reviewed_date).days

    if gap_days > STALENESS_THRESHOLD_DAYS:
        print(
            "scaffold backlog freshness FAILED: docs/6_SGT_BACKLOG.md's "
            f"'Last reviewed' date ({reviewed_match.group(1)}) is "
            f"{gap_days} days behind the latest docs/AGENT_ACTIVITY.md "
            f"entry ({latest_activity_date.date()}), past the "
            f"{STALENESS_THRESHOLD_DAYS}-day threshold.",
            file=sys.stderr,
        )
        print(
            "Reconcile docs/6_SGT_BACKLOG.md against what has actually "
            "landed since the reviewed date (read the delivery records, "
            "correct any item whose gate/status claim is now stale, add "
            "a dated update block where warranted), then bump the "
            "'Last reviewed' line to today.",
            file=sys.stderr,
        )
        return 1

    print(
        f"OK: backlog reviewed {reviewed_match.group(1)} is "
        f"{gap_days} day(s) behind the latest activity-log entry "
        f"({latest_activity_date.date()}), within the "
        f"{STALENESS_THRESHOLD_DAYS}-day threshold."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
