import Lake
open Lake DSL

package «pb701» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`pp.unicode.fun, true⟩
  ]

-- require undergrad from git
--    "https://github.com/drhodes/undergrad.git" @ "main"

require undergrad from git
   "../../../undergrad" @ "main"

@[default_target]
lean_lib «Pb701» where
  -- add any library configuration options here
