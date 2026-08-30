# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify all .lean files are imported.
lake exe mk_all --lib EllipticCurves --git --check || exit 1

# Fetch build cache
lake exe cache get

# Verify everything builds.
lake build --wfail || exit 1

# Verify the environment linters pass.  These are NOT the `mathlibStandardSet` linters that
# `--wfail` above enforces: those are syntactic, fire during elaboration and surface as build
# warnings.  These run as a post-hoc pass over the elaborated environment (`simpNF`,
# `unusedArguments`, `defsWithUnderscore`, `docBlame`, ...) and `lake build` never invokes them,
# so a green warning-free build says nothing about them.  Driven by `lintDriver` in
# `lakefile.toml`; see the "Linting" section of README.md.
lake lint || exit 1
