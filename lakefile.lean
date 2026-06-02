import Lake
open Lake DSL

package «FormalRV» where
  version := v!"0.1.0"

-- doc-gen4 is an OPTIONAL dependency, pulled in only when building docs
-- (`-Kenv=docs`); a normal `lake build` never requires it. It is required
-- BEFORE mathlib on purpose: mathlib is required LAST so that mathlib's pinned
-- versions of shared transitive dependencies (plausible, batteries, …) take
-- precedence, keeping `lake exe cache get` hashes valid for the normal build.
-- The doc-gen4 ref is pinned to the tag matching this toolchain (v4.29.1).
meta if get_config? env = some "docs" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.29.1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"

@[default_target]
lean_lib «FormalRV» where
  -- root module is FormalRV.lean
