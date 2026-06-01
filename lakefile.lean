import Lake
open Lake DSL

package «FormalRV» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"

-- doc-gen4 is an OPTIONAL dependency, only pulled in when building docs.
-- It is gated behind `-Kenv=docs` so that a normal `lake build` does NOT
-- require (or download/compile) doc-gen4. The doc-gen4 ref is pinned to the
-- tag that matches this project's Lean toolchain (leanprover/lean4:v4.29.1).
-- NOTE: this `meta if` gating only works in a lakefile.lean (Lean DSL); it is
-- not expressible in lakefile.toml, which is why this file replaces the .toml.
meta if get_config? env = some "docs" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.29.1"

@[default_target]
lean_lib «FormalRV» where
  -- root module is FormalRV.lean
