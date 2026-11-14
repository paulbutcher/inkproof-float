#!/usr/bin/env bash
# Copyright (c) 2026 Paul Butcher. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Print this library's public API; the output is API.lock.
set -euo pipefail
cd "$(dirname "$0")/.."
lake build >&2
cd test
lake build >&2
lake exe api-lock "${@:-Inkproof.Float}"
