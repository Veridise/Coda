#!/usr/bin/env bash

cd "$( dirname "${BASH_SOURCE[0]}" )"

cat > Tactics.v.tmp <<EOF
(** * Generic Tactics *)
Require Export Crypto.Util.FixCoqMistakes.
EOF
FILES="$(cd Tactics; git ls-files '*.v' | env LC_COLLATE=C sort)"
for i in $FILES; do
    echo "Require Export Crypto.Util.Tactics.${i%.v}." >> Tactics.v.tmp
done

cmp --silent Tactics.v Tactics.v.tmp || mv Tactics.v.tmp Tactics.v
