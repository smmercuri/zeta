#!/usr/bin/env bash
# Manage the proof terms of the certificate batches: the private oleans that
# `scripts/build.sh --proofs=discard|archive` shrinks as each batch is built.
#
# A batch module `Zeta.Zeros.Certificates.*.BatchNNNN` leaves three olean parts in
# `.lake/build/lib/lean/`: `.olean` (its public interface: the statement `batch : BatchSpec …`),
# `.olean.server`, and `.olean.private` (the kernel-checked proof term, megabytes per batch, growing
# with ν = ⌊√(t/2π)⌋). Under
# `lake build` the private part is never opened again once the batch is built: Lake hands a `module`
# importer only `.olean` and `.olean.server`, and its freshness check asks only that the file
# *exist* beside its `.hash` sidecar. The assembler, the count certificate and `Zeta.Main`'s
# `#print axioms` (all `module`s) work from the public part. The proof term is wanted again only to
# re-check or inspect it without rebuilding, or by a non-`module` importer. `comparator/` is such
# a re-check: it exports the proof terms from these files and fails on a placeholder, and Lake will
# not rebuild one on its own, so `restore` the batches it needs first.
#
# So a batch's private olean can be replaced by a one-line placeholder under the original name,
# with the SHA-256 of the original beside it (`.olean.private.sha256`, one file per batch, so
# parallel shrinks never share a file):
#
#   discard  keeps only the placeholder and the hash; `restore` rebuilds the batch from source and,
#            the build being deterministic (same source and toolchain), checks it against the hash.
#   archive  also keeps the proof term compressed with plain `zstd` (`.olean.private.zst`);
#            `restore` unpacks it and checks the hash. `.olean.private.xz` archives are also
#            recognised and restored.
#
#   scripts/proofs.sh status         # how many batches are full-size, archived, discarded, unbuilt
#   scripts/proofs.sh discard [Batch…]     # shrink full-size proof terms (all built batches if none)
#   scripts/proofs.sh archive [Batch…]     # ... keeping a lossless archive
#   scripts/proofs.sh restore [Batch…]     # full-size again (all if none): unpack, or rebuild
#   scripts/proofs.sh verify [Batch…]      # check archives unpack to their recorded hashes
#
# Batch names may be given as `Batch0050`, `RiemannSiegel/Batch0050` or the module name.
# Environment: PROOFS_ZSTD_LEVEL zstd level for `archive` (default 3).
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
LIB=.lake/build/lib/lean/Zeta/Zeros/Certificates
SRC=Zeta/Zeros/Certificates
LEVEL=${PROOFS_ZSTD_LEVEL:-3}
PLACEHOLDER_MAX=512   # a placeholder is tiny; a real private olean is megabytes

if command -v sha256sum >/dev/null; then hash_file() { sha256sum < "$1" | cut -d' ' -f1; }
else hash_file() { shasum -a 256 < "$1" | cut -d' ' -f1; }
fi
fsize() { wc -c < "$1" | tr -d ' '; }   # portable (no BSD/GNU `stat` split)
mb() { echo $(( $1 / 1048576 )); }

need_archive_tools() {
  command -v zstd >/dev/null || { echo "proofs.sh: zstd not found on PATH" >&2; exit 2; }
}

# --- batch discovery ---------------------------------------------------------------------

# `Method/BatchNNNN` for every batch source, in build order.
all_batches() {
  find "$SRC" -name 'Batch*.lean' | sed -E "s|^$SRC/||; s|\.lean$||" | sort
}

# Normalise a user-supplied name to `Method/BatchNNNN`.
resolve() {
  local n=$1
  n=${n#Zeta.Zeros.Certificates.}; n=${n//./\/}
  if [[ $n != */* ]]; then
    local hits; hits=$(all_batches | grep -E "/$n$" || true)
    [[ -n $hits ]] || { echo "proofs.sh: no batch named $1" >&2; exit 2; }
    n=$hits
  fi
  [[ -f $SRC/$n.lean ]] || { echo "proofs.sh: no batch source $SRC/$n.lean" >&2; exit 2; }
  echo "$n"
}

module_of() { echo "Zeta.Zeros.Certificates.${1//\//.}"; }
private_of() { echo "$LIB/$1.olean.private"; }
new_archive_of() { echo "$LIB/$1.olean.private.zst"; }
# the batch's archive: the `.zst`, or a legacy `.xz` if that is all it has
archive_of() {
  local zst legacy="$LIB/$1.olean.private.xz"
  zst=$(new_archive_of "$1")
  if [[ ! -f $zst && -f $legacy ]]; then echo "$legacy"; else echo "$zst"; fi
}
hash_of() { echo "$LIB/$1.olean.private.sha256"; }

# unbuilt | full | archived | discarded (placeholder only: `restore` rebuilds it)
state_of() {
  local p; p=$(private_of "$1")
  if [[ ! -f $p ]]; then echo unbuilt
  elif (( $(fsize "$p") > PLACEHOLDER_MAX )); then echo full
  elif [[ -f $(archive_of "$1") && -f $(hash_of "$1") ]]; then echo archived
  else echo discarded
  fi
}

# explicit names, or every built batch
targets() {
  if (( $# )); then local n; for n in "$@"; do resolve "$n"; done
  else all_batches | while read -r b; do [[ $(state_of "$b") == unbuilt ]] || echo "$b"; done
  fi
}

# --- the archive format: plain zstd --------------------------------------------------------

pack() { zstd -q -T1 "-$LEVEL" -c < "$1" > "$2"; }   # pack <olean> <archive>
unpack() {                                           # unpack <archive> <olean>
  case $1 in
    *.xz)
      command -v xz >/dev/null || { echo "proofs.sh: xz is needed to unpack $1" >&2; return 2; }
      xz -d -c < "$1" > "$2" ;;
    *) zstd -q -d -c < "$1" > "$2" ;;
  esac
}

# --- operations --------------------------------------------------------------------------

placeholder() {  # placeholder <batch> <how to get it back>
  printf 'the proof term of %s is not stored here: %s\n' "$(module_of "$1")" "$2" > "$(private_of "$1")"
}

shrink_one() {  # shrink_one discard|archive <batch>
  local mode=$1 b=$2 p a h
  p=$(private_of "$b"); a=$(new_archive_of "$b")
  case $(state_of "$b") in
    full) ;;
    archived|discarded) return 0 ;;
    unbuilt) echo "proofs.sh: $b is not built" >&2; return 1 ;;
  esac
  h=$(hash_file "$p")
  if [[ $mode == discard ]]; then
    echo "$h" > "$(hash_of "$b")"
    placeholder "$b" "run \`scripts/proofs.sh restore $(basename "$b")\` to rebuild it"
    echo "discarded $b"
    return 0
  fi
  pack "$p" "$a.tmp"
  # verify the archive before discarding the original
  unpack "$a.tmp" "$p.check"
  [[ $(hash_file "$p.check") == "$h" ]] \
    || { rm -f "$a.tmp" "$p.check"; echo "proofs.sh: archive of $b does not round-trip; original kept" >&2; return 1; }
  rm -f "$p.check"
  mv "$a.tmp" "$a"
  echo "$h" > "$(hash_of "$b")"
  placeholder "$b" "it is in $(basename "$a"); run \`scripts/proofs.sh restore $(basename "$b")\`"
  echo "archived $b ($(mb "$(fsize "$a")") MB)"
}

restore_archived() {
  need_archive_tools
  local b=$1 p a h
  p=$(private_of "$b"); a=$(archive_of "$b"); h=$(cat "$(hash_of "$b")")
  unpack "$a" "$p.tmp"
  [[ $(hash_file "$p.tmp") == "$h" ]] \
    || { rm -f "$p.tmp"; echo "proofs.sh: restored $b does not match its recorded hash $h" >&2; return 1; }
  mv "$p.tmp" "$p"
  echo "restored $b ($(mb "$(fsize "$p")") MB)"
}

# Restore the given batches: unpack the archived ones, rebuild the discarded ones (one `scripts/build.sh`
# for all of them; deleting a module's private olean is what makes Lake rebuild it).
cmd_restore() {
  local b rc=0
  local -a rebuild=()
  while read -r b; do
    case $(state_of "$b") in
      archived) restore_archived "$b" || rc=1 ;;
      discarded) rm -f "$(private_of "$b")"; rebuild+=("$b") ;;
      *) ;;
    esac
  done < <(targets "$@")
  if (( ${#rebuild[@]} )); then
    echo "proofs.sh: rebuilding ${#rebuild[@]} discarded batch(es)" >&2
    local -a mods=()
    for b in "${rebuild[@]}"; do mods+=("$(module_of "$b")"); done
    scripts/build.sh "${mods[@]}" || rc=1
    # the build is deterministic, so a rebuild must reproduce the recorded hash exactly
    for b in "${rebuild[@]}"; do
      [[ -f $(hash_of "$b") && -f $(private_of "$b") ]] || continue
      if [[ $(hash_file "$(private_of "$b")") == "$(cat "$(hash_of "$b")")" ]]; then
        echo "rebuilt $b: identical to the original build"
      else
        echo "proofs.sh: rebuilt $b differs from the original build (different source or toolchain?)" >&2
        rc=1
      fi
    done
  fi
  return $rc
}

verify_one() {
  local b=$1 p
  case $(state_of "$b") in
    archived) ;;
    discarded) echo "$b: discarded (only a rebuild can check it)"; return 0 ;;
    *) echo "$b: $(state_of "$b"), no archive"; return 0 ;;
  esac
  p=$(private_of "$b")
  unpack "$(archive_of "$b")" "$p.check"
  if [[ $(hash_file "$p.check") == "$(cat "$(hash_of "$b")")" ]]; then echo "$b: ok"; rm -f "$p.check"
  else echo "$b: MISMATCH"; rm -f "$p.check"; return 1; fi
}

cmd_status() {
  local b unbuilt=0 full=0 archived=0 discarded=0 full_bytes=0 arch_bytes=0
  while read -r b; do
    case $(state_of "$b") in
      unbuilt) unbuilt=$(( unbuilt + 1 )) ;;
      full) full=$(( full + 1 )); full_bytes=$(( full_bytes + $(fsize "$(private_of "$b")") )) ;;
      archived) archived=$(( archived + 1 )); arch_bytes=$(( arch_bytes + $(fsize "$(archive_of "$b")") )) ;;
      discarded) discarded=$(( discarded + 1 )) ;;
    esac
  done < <(all_batches)
  printf 'unbuilt %d, full-size %d (%d MB), archived %d (%d MB), discarded %d\n' \
    "$unbuilt" "$full" "$(mb $full_bytes)" "$archived" "$(mb $arch_bytes)" "$discarded"
}

case "${1:-}" in
  discard|archive)
    mode=$1; shift
    [[ $mode == archive ]] && need_archive_tools
    rc=0; while read -r b; do shrink_one "$mode" "$b" || rc=1; done < <(targets "$@"); exit $rc ;;
  restore) shift; cmd_restore "$@" ;;
  verify)  shift; need_archive_tools
           rc=0; while read -r b; do verify_one "$b" || rc=1; done < <(targets "$@"); exit $rc ;;
  status)  cmd_status ;;
  *) awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' scripts/proofs.sh; exit 2 ;;
esac
