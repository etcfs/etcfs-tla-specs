#!/bin/bash
# Runs TLC over every model configuration in specs/ and asserts the outcome
# each one is supposed to have.
#
# Half the configurations are supposed to FAIL. A spec that proves everything
# proves nothing, so the deliberately broken variants are checked to still
# produce a counterexample — the same reasoning as the negative controls in
# test/verify (see docs/verification/porcupine.md).
#
# Usage:
#   ./check.sh            # the 2-node models, ~10s total
#   DEEP=1 ./check.sh     # adds the 3-node model, minutes and hot
#   TLA_WORKERS=4 ./check.sh
#
# TLC is brute-force state enumeration and will use every core it is given.
# The default is deliberately 2 workers and nice'd: the 2-node models settle
# in seconds either way, and the difference on a laptop is a warm fan rather
# than a hot one.

set -uo pipefail

SPECS="$(cd "$(dirname "$0")" && pwd)"
TOOLS="$SPECS/.tools"
JAR="$TOOLS/tla2tools.jar"
WORKERS="${TLA_WORKERS:-2}"

if [[ ! -f "$JAR" ]]; then
    echo "[tla] fetching tla2tools.jar"
    mkdir -p "$TOOLS"
    curl -sSL -o "$JAR" \
        https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar || {
        echo "[tla] could not download tla2tools.jar" >&2
        exit 1
    }
fi

# module:config:expected — "pass" means TLC must find no error, "fail" means it
# must produce a counterexample, and the named invariant or temporal property is
# the one it must break.
CHECKS=(
    "Fencing:Fencing:pass:"
    "Fencing:FencingNoFencer:pass:"
    "Fencing:FencingUnreliableFencer:pass:"
    "Fencing:FencingGuardIsBackstop:pass:"
    "Fencing:FencingNoIncarnationCheck:fail:NoHealthyNodeSevered"
    "Fencing:FencingNoGuard:fail:StaleWriteRejected"
    "Fencing:FencingArenaBug:fail:ReleasedArenaHasNoLiveWriter"
    "Fencing:FencingDepartureNotQuiescent:fail:ReleasedArenaHasNoLiveWriter"
    "CachedLock:CachedLock:pass:"
    "CachedLock:CachedLockNoLeaseIdentity:fail:NoTwoHolders"
    "CachedLock:CachedLockNoFlushKeyCheck:fail:NoPublishWithoutLock"
    "CachedLock:CachedLockNoRecallFlush:fail:NoLostAckedWrite"
    "CachedLock:CachedLockNoInvalidate:fail:NoStalePages"
    "CachedLock:CachedLockStaleSnapshot:fail:ViewMatchesTruth"
    "CachedLock:CachedLockKeepsCacheOnKeyLoss:fail:NoStalePages"
    "CachedLock:CachedLockOrphanedKey:pass:"
    "CachedLock:CachedLockNoOrphanDiscard:fail:OrphanFreed"
)
[[ "${DEEP:-0}" == "1" ]] && CHECKS+=("Fencing:Fencing3Nodes:pass:")

cd "$SPECS" || exit 1
fails=0

for check in "${CHECKS[@]}"; do
    module="${check%%:*}"
    rest="${check#*:}"
    cfg="${rest%%:*}"
    rest="${rest#*:}"
    expected="${rest%%:*}"
    wanted="${rest#*:}"

    printf '%-32s ' "$cfg"
    out=$(nice -n 10 java -XX:+UseParallelGC -cp "$JAR" tlc2.TLC \
            -workers "$WORKERS" -config "$cfg.cfg" "$module.tla" 2>&1)

    states=$(echo "$out" | grep -oE '[0-9]+ distinct states found' | tail -1 | grep -oE '^[0-9]+')
    broke=$(echo "$out" | grep -oE 'Invariant [A-Za-z]+ is violated' | head -1 | awk '{print $2}')
    # A temporal property violation does not name the property it broke, so the
    # configuration is asked instead: TLC checked what the cfg declares, and a
    # cfg declaring one property leaves nothing to attribute wrongly.
    if [[ -z "$broke" ]] && echo "$out" | grep -q 'Temporal properties were violated'; then
        grep -q "^ *$wanted\$" "$cfg.cfg" && broke="$wanted"
    fi

    if echo "$out" | grep -q "No error has been found"; then
        if [[ "$expected" == "pass" ]]; then
            echo "OK    no counterexample, ${states:-?} states"
        else
            echo "WRONG expected a counterexample on $wanted, found none"
            fails=$((fails + 1))
        fi
    elif [[ -n "$broke" ]]; then
        if [[ "$expected" == "fail" && "$broke" == "$wanted" ]]; then
            echo "OK    broke $broke as expected"
        elif [[ "$expected" == "fail" ]]; then
            echo "WRONG expected $wanted to break, but $broke broke first"
            fails=$((fails + 1))
        else
            echo "WRONG unexpected violation of $broke"
            fails=$((fails + 1))
        fi
    else
        echo "ERROR TLC did not run:"
        echo "$out" | tail -5
        fails=$((fails + 1))
    fi
done

echo
if [[ "$fails" -eq 0 ]]; then
    echo "[tla] all models behaved as specified"
else
    echo "[tla] $fails model(s) did not behave as specified" >&2
fi
exit "$fails"
