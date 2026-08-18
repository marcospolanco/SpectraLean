#!/usr/bin/env bash
set -euo pipefail

root_dir=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
fixture_dir=$(mktemp -d "$root_dir/.opencode/opencode-pursue-test.XXXXXX")
trap 'rm -rf "$fixture_dir"' EXIT

mkdir -p "$fixture_dir/scripts" "$fixture_dir/bin" "$fixture_dir/docs"
cp "$root_dir/scripts/opencode-pursue" "$fixture_dir/scripts/opencode-pursue"
chmod +x "$fixture_dir/scripts/opencode-pursue"

git -C "$fixture_dir" init --quiet
git -C "$fixture_dir" config user.name "Scaffold Test"
git -C "$fixture_dir" config user.email "scaffold-test@example.invalid"
printf 'baseline\n' > "$fixture_dir/README.md"
printf '# Activity\n' > "$fixture_dir/docs/AGENT_ACTIVITY.md"
git -C "$fixture_dir" add README.md docs/AGENT_ACTIVITY.md
git -C "$fixture_dir" commit --quiet -m 'test: baseline'

printf '%s\n' '#!/usr/bin/env bash' 'exit 0' > "$fixture_dir/scripts/zquota"
chmod +x "$fixture_dir/scripts/zquota"

cat > "$fixture_dir/bin/opencode" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
if [[ "$1" == "session" ]]; then
  printf '{\n  "id": "test-session"\n}\n'
  exit 0
fi
printf 'changed by pursuit\n' >> README.md
printf '\n**Status:** completed\n' >> docs/AGENT_ACTIVITY.md
EOF
chmod +x "$fixture_dir/bin/opencode"

cat > "$fixture_dir/bin/codex" <<'EOF'
#!/usr/bin/env bash
set -euo pipefail
while (($#)); do
  if [[ "$1" == "--ask-for-approval" ]]; then
    echo 'unsupported --ask-for-approval passed to codex exec' >&2
    exit 64
  fi
  if [[ "$1" == "--output-last-message" || "$1" == "-o" ]]; then
    printf 'feat(sgt): automate pursuit commits\n' > "$2"
    exit 0
  fi
  shift
done
exit 1
EOF
chmod +x "$fixture_dir/bin/codex"

for command_name in python3 lake; do
  printf '%s\n' '#!/usr/bin/env bash' 'exit 0' > "$fixture_dir/bin/$command_name"
  chmod +x "$fixture_dir/bin/$command_name"
done

git -C "$fixture_dir" add scripts bin
git -C "$fixture_dir" commit --quiet -m 'test: fixture commands'

PATH="$fixture_dir/bin:$PATH" "$fixture_dir/scripts/opencode-pursue" --runs 1 --commit

subject=$(git -C "$fixture_dir" log -1 --format=%s)
[[ "$subject" == 'feat(sgt): automate pursuit commits' ]]
[[ -z "$(git -C "$fixture_dir" status --porcelain)" ]]
