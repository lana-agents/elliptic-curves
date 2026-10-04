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

# Verify no Markdown ATX heading wraps onto a second source line.  An ATX heading is a leaf block
# that ends at the end of its own line and CommonMark gives it no continuation syntax, so a title
# written across two lines renders as a heading holding the FIRST line and an ordinary paragraph
# holding the rest -- the reader who consults the heading is handed a clause chopped at whatever
# word the line broke on.  See the "A heading is one source line" bullet under "Scope of the rules
# above" in README.md for the rule, its ground, and the repair form (shorten the title; state the
# clause that does not fit in the prose below, do not wrap it).  Two recognisers are needed and the
# obvious one misses the worse case: (1) a heading followed by a non-blank line, which is the plain
# wrap; (2) a heading whose text begins in lower case, which is the variant where the author put
# the hashes on the CONTINUATION line and so made a SECOND heading, invisible to (1).  Both
# exemptions below are load-bearing and removing either changes the reading, and the first of them
# is CommonMark's block starters MINUS the HTML block, which is ruled on three sentences below,
# because every one of those shapes is a complete heading followed by a complete block: a following
# line opening a bullet list (`*`, `-`, `+`), an ORDERED list item (`1.`, `1)`), a table row, a
# block quote, a heading, either fence form (``` or ~~~), an indented code block (four spaces or a
# tab), a thematic break in any of its three spellings (`---`, `***`, `___`) or a link reference
# definition (`[label]: dest`) is legal beneath a title; and a heading that opens with a code span
# is a title rather than a continuation.  A starter missing from that set is a FALSE failure of a
# HARD gate, which is worse than a missed defect because the author cannot comply with it -- there
# is nothing to shorten -- which is why the set is ENUMERATED here and the one member left out is
# named rather than left to be re-found.  THE HTML BLOCK IS THAT MEMBER, AND IT IS LEFT OUT
# DELIBERATELY: its reading is renderer-dependent, so no choice here is unconditionally right.
# With HTML enabled, `## Note` over `<!-- c -->` orphans no paragraph and this gate is WRONG on it;
# with HTML disabled the continuation IS a paragraph and the gate is RIGHT.  Which reading this
# population gets is UNDETERMINED: `doc-gen` occurs 0 times in lakefile.toml, lake-manifest.json
# and all three .github/workflows files, so the docstring half of the population has no rendered
# artifact in this repository at all, while README.md is read on GitHub, whose parser DOES open an
# HTML block (it sanitises after parsing) -- i.e. the determinable half gives the reading under
# which this gate convicts a non-defect.  So the omission is recorded as a GAP and not as a
# ruling that the gate is right there: measured exposure is 0 (no tracked file opens an HTML block
# beneath a heading and README.md holds no such line anywhere), and if one ever appears the repair
# is to add CommonMark's seven HTML-block conditions as a further disjunct below, NOT to reword
# the heading.  Fenced blocks
# are masked so that a shell comment on display cannot fail the run, and an unbalanced fence is
# reported rather than failed: it makes the mask swallow the rest of its file, so the count
# UNDER-reads, and a gate that under-reads must say so rather than report a quiet success.  Runs
# over the TRACKED `.lean` files plus README.md -- the same population the rule's own row measured
# -- and costs seconds, so it sits beside the gate above rather than behind Lake.
python3 <<'WRAPPED_HEADING' || exit 1
import pathlib, re, subprocess, sys

HEADING = re.compile(r"^(#{1,6}) (.+)$")
FENCE = re.compile(r"^\s*(```|~~~)")
# A following line that opens one of these is a block in its own right, not a wrapped title:
# all three bullet markers, a table row, a block quote, a heading, and either fence form.
FOLLOWERS = ("*", "-", "+", "|", ">", "#", "```", "~~~")
# An ordered list item is a block starter too and takes a pattern rather than a prefix: one to
# nine digits followed by `.` or `)`.
ORDERED = re.compile(r"^[0-9]{1,9}[.)]")
# Four leading spaces or a tab open an indented code block.  This one is tested on the RAW line,
# because the lstrip() that lets the markers above be indented would throw the signal away.
INDENTED = ("    ", "\t")
# A thematic break opens a block in three spellings and only two of them reach FOLLOWERS -- `-`
# and `*`, by accident, through the loose prefixes.  `___` needs its own pattern.  Added as a
# FURTHER disjunct rather than as a replacement for those prefixes, so the exemption set only
# grows and the reading stays monotone: whatever the previous gate exempted, this one exempts.
THEMATIC_BREAK = re.compile(r"^ {0,3}([-*_])[ \t]*(?:\1[ \t]*){2,}$")
# A link reference definition renders to NOTHING at all, so a heading above one orphans no
# paragraph.  Both of these are tested on the RAW line: CommonMark allows up to three leading
# spaces, and a fourth makes the line an indented code block, which INDENTED already exempts.
LINK_REF_DEF = re.compile(r"^ {0,3}\[[^\]]*\]:")

listing = subprocess.run(["git", "ls-files", "-z", "*.lean", "README.md"],
                         capture_output=True, check=True).stdout
paths = [p.decode() for p in listing.split(b"\0") if p]

total = 0
hits = []
unbalanced = []
for path in paths:
    lines = pathlib.Path(path).read_text(encoding="utf-8").split("\n")
    fenced = False
    for lineno, line in enumerate(lines, 1):
        if FENCE.match(line):
            fenced = not fenced
            continue
        if fenced:
            continue
        matched = HEADING.match(line)
        if not matched:
            continue
        total += 1
        following = lines[lineno] if lineno < len(lines) else ""
        # Strip decoration so that a heading opening on an emoji or a dash is judged on its text,
        # and keep the backtick so that a heading opening on a code span is exempt from (2).
        core = re.sub(r"^[^0-9A-Za-z`]*", "", matched.group(2))
        opens_block = (following.startswith(INDENTED)
                       or following.lstrip().startswith(FOLLOWERS)
                       or bool(ORDERED.match(following.lstrip()))
                       or bool(THEMATIC_BREAK.match(following))
                       or bool(LINK_REF_DEF.match(following)))
        wrapped = bool(following.strip()) and not opens_block
        lowercase = bool(re.match(r"^[a-z]", core))
        if wrapped or lowercase:
            hits.append((path, lineno, wrapped, lowercase, line, following))
    if fenced:
        unbalanced.append(path)

for path in unbalanced:
    print(f"{path}: WARNING unbalanced code fence -- the mask stayed on to the end of the file, so "
          f"every heading after the last fence line in it was skipped and this run's heading "
          f"count UNDER-reads.  The summary line prints only when there are hits, so on a clean "
          f"run this warning stands alone.  Balance the fence.")

for path, lineno, wrapped, lowercase, line, following in hits:
    why = ("its continuation renders as an ordinary paragraph" if wrapped
           else "its text begins in lower case, so it is the tail of the heading above")
    print(f"{path}:{lineno}: this heading wraps -- {why}.  Shorten the title to one source line "
          f"and state the clause that does not fit in the prose below it.")
    print(f"    heading: {line}")
    if wrapped:
        print(f"    orphaned: {following}")
if hits:
    print(f"{len(hits)} wrapped heading(s) over {total} headings in {len(paths)} tracked files.")
    sys.exit(1)
WRAPPED_HEADING

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
