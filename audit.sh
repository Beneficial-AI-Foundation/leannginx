#!/bin/sh
# Regenerate LeanNginx/Audit.lean (the axiom audit of every spec). Run after changing specs.
set -e
cd "$(dirname "$0")"
lake build LeanNginx.Spec
python3 -I scripts/gen_audit.py
lake build
