# Verify the worktree is clean
if ! [ -z "$(git status --porcelain)" ]; then
  echo "The working tree is not clean. Commit changes or discard if temporary."
  exit 1
fi

# Verify no line of a `.lean` file that Lean never reads as an import nonetheless looks like one
# to the import-closure walkers: a docstring sentence reflowed onto the word `import`, or a fenced
# block displaying import syntax, leaves their recogniser a match inside a comment and so a phantom
# module named after the next word.  See the "Import-closure figures" section of README.md for
# the rule and its two repair shapes; the test below is that rule's own definition rather than a
# proxy for it, masking Lean comments (block comments nest, `--` runs to end of line) and reporting
# a line only when its first character is masked, so it consults no module index and never reads
# `.lake`.  It runs over the TRACKED `.lean` files, never a filesystem walk, so that an untracked
# scratch file under `EllipticCurves/` cannot fail the run, and it sits here -- after the
# cleanliness check whose reading it depends on, ahead of everything that needs Lake -- because it
# costs seconds and a branch author should learn about a whitespace position without waiting for a
# twenty-minute build.
python3 <<'PHANTOM_IMPORT' || exit 1
import pathlib, re, subprocess, sys

IMPORT = re.compile(r"^(?:public |private |meta )*import (\S+)")


def comment_mask(src):
    """1 at every position inside a Lean comment.  Block comments nest; `--` runs to end of line."""
    n = len(src); m = bytearray(n); d = 0; i = 0
    while i < n:
        if d == 0:
            if src.startswith("/-", i):
                d = 1; m[i] = m[i + 1] = 1; i += 2; continue
            if src.startswith("--", i):
                j = src.find("\n", i); j = n if j < 0 else j
                for k in range(i, j):
                    m[k] = 1
                i = j; continue
            i += 1
        else:
            if src.startswith("/-", i):
                d += 1; m[i] = m[i + 1] = 1; i += 2; continue
            if src.startswith("-/", i):
                d -= 1; m[i] = m[i + 1] = 1; i += 2; continue
            m[i] = 1; i += 1
    return m


listing = subprocess.run(["git", "ls-files", "-z", "*.lean"],
                         capture_output=True, check=True).stdout
paths = [p.decode() for p in listing.split(b"\0") if p]

hits = []
for path in paths:
    text = pathlib.Path(path).read_text(encoding="utf-8")
    mask = comment_mask(text)
    offset = 0
    for lineno, line in enumerate(text.split("\n"), 1):
        matched = IMPORT.match(line)
        if matched and offset < len(mask) and mask[offset]:
            hits.append((path, lineno, matched.group(1)))
        offset += len(line) + 1

for path, lineno, phantom in hits:
    print(f"{path}:{lineno}: phantom import of module `{phantom}` -- this line sits inside a "
          f"comment.  Reflow the sentence, or indent the fence body by two spaces.")
if hits:
    print(f"{len(hits)} phantom `import` line(s) over {len(paths)} tracked .lean files.")
    sys.exit(1)
PHANTOM_IMPORT

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
