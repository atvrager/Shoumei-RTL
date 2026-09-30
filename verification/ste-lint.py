#!/usr/bin/env python3
"""ste-lint.py - dictionary-free ASD-STE100 prose linter.

Check prose against a small set of mechanical Simplified Technical English
rules.  There is no approved-word list: every rule is a regex or a length
limit, so the tool runs offline and cannot drift from a dictionary file.

Rules cover markdown files, code comments, and commit messages.

Severity:
  error    mechanical violation; blocks the git hook
  warning  reported only; promoted to error by --strict

Known limits (by design):
  - no part-of-speech tagger: the 3-word noun-cluster rule is not checked
  - passive voice is reported but never blocked; STE allows it in
    descriptive text, and the tagger cannot tell the two apart
  - a line continues the sentence above only when it stops on a comma or a
    function word, so a wrapped sentence that ends on a content word can
    escape the word limit.  The trade keeps a run of short label comments
    from reading as one long sentence.
  - add `ste-lint: ignore` to a line to skip it

Usage:
  ste-lint.py --diff                 # lines added in the staged diff
  ste-lint.py --stdin < msgfile      # a commit message
  ste-lint.py --all                  # every tracked prose file
  ste-lint.py docs/ foo.md           # explicit paths
  ste-lint.py --list-rules
"""

from __future__ import annotations

import argparse
import enum
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Lengths.  STE limits a procedural sentence to 20 words and a descriptive
# sentence to 25 words, so 21 warns and 26 fails.
SENTENCE_WARN_WORDS = 21
SENTENCE_FAIL_WORDS = 26
PARAGRAPH_MAX_SENTENCES = 6
MAX_FINDINGS = 200
MAX_FINDINGS_PER_LINE = 3

PROSE_EXTS = frozenset({".md", ".txt", ".rst", ".adoc"})
# Machine-generated files.  Their comments are output of a tool and not prose
# a reader can rewrite.
SKIP_FILES = frozenset({"requirements_lock.txt"})
SKIP_DIRS = frozenset(
    {".git", ".lake", "output", "build-sim", "node_modules", "third_party", "generated"}
)


class Severity(enum.Enum):
    ERROR = "error"
    WARNING = "warning"

    @property
    def rank(self) -> int:
        return 0 if self is Severity.ERROR else 1


class Rule:
    """Rule identifiers.  Stable; the test file asserts on them."""

    SENTENCE = "STE001"  # sentence longer than the word limit
    SEMICOLON = "STE002"  # semicolon instead of two sentences
    CONTRACTION = "STE003"  # do not use contractions
    LATIN = "STE004"  # spell out a Latin abbreviation or tag
    WORDY = "STE005"  # wordy phrase with a short replacement
    HYPE = "STE006"  # praise, filler, metaphor, emoji
    PASSIVE = "STE007"  # passive voice (descriptive text only)
    PARAGRAPH = "STE008"  # more than 6 sentences in one paragraph
    EXPLETIVE = "STE009"  # name the subject after "there"

    # Commit message rules, checked on the message itself.
    SUBJECT_LONG = "COMMIT001"  # subject over the length limit
    SUBJECT_CASE = "COMMIT002"  # subject does not start with a capital
    SUBJECT_PERIOD = "COMMIT003"  # subject ends with a period
    BLANK_LINE = "COMMIT004"  # no blank line after the subject
    BODY_WRAP = "COMMIT005"  # body line over the length limit
    FIXUP = "COMMIT006"  # a fixup, squash or WIP subject
    TRAILING_WS = "COMMIT007"  # trailing whitespace in the message


RULE_HELP = {
    Rule.SENTENCE: f"sentence longer than {SENTENCE_FAIL_WORDS - 1} words",
    Rule.SEMICOLON: "semicolon: write two sentences",
    Rule.CONTRACTION: "expand the contraction",
    Rule.LATIN: "spell out the Latin abbreviation",
    Rule.WORDY: "use the short form",
    Rule.HYPE: "delete praise, filler, or metaphor",
    Rule.PASSIVE: "prefer active voice",
    Rule.PARAGRAPH: f"split a paragraph longer than {PARAGRAPH_MAX_SENTENCES} sentences",
    Rule.EXPLETIVE: "name the subject",
    Rule.SUBJECT_LONG: "shorten the subject",
    Rule.SUBJECT_CASE: "capitalize the subject",
    Rule.SUBJECT_PERIOD: "drop the final period",
    Rule.BLANK_LINE: "put a blank line after the subject",
    Rule.BODY_WRAP: "wrap the body",
    Rule.FIXUP: "squash the fixup before it lands",
    Rule.TRAILING_WS: "delete the trailing whitespace",
}

# Commit message lengths.  The subject target is 50 characters and the hard
# limit 72.  The body wraps at 72.
SUBJECT_MAX = 50
SUBJECT_HARD = 72
BODY_MAX = 72


# ---------------------------------------------------------------- word lists

# Wordy phrase -> short replacement.  Only phrases with a mechanical fix.
WORDY = {
    "in order to": "to",
    "prior to": "before",
    "subsequent to": "after",
    "in the event that": "if",
    "in the case that": "if",
    "due to the fact that": "because",
    "owing to the fact that": "because",
    "in spite of the fact that": "although",
    "for the purpose of": "to",
    "with regard to": "about",
    "with respect to": "about",
    "in relation to": "about",
    "at this point in time": "now",
    "at the present time": "now",
    "in the near future": "soon",
    "a number of": "some",
    "a majority of": "most",
    "is able to": "can",
    "are able to": "can",
    "has the ability to": "can",
    "have the ability to": "can",
    "make use of": "use",
    "makes use of": "use",
    "utilize": "use",
    "utilizes": "use",
    "utilizing": "use",
    "utilization": "use",
    "utilise": "use",
    "leverage": "use",
    "leverages": "use",
    "leveraging": "use",
    "commence": "start",
    "commences": "start",
    "terminate": "end",
    "terminates": "end",
    "it should be noted that": "",
    "it is worth noting that": "",
    "it is important to note that": "",
    "please note that": "",
    "note that": "",
    "in addition": "also",
    "additionally": "also",
    "furthermore": "also",
    "moreover": "also",
}

# Praise, filler, metaphor, self-assessment.  Delete the word and the
# sentence usually survives.
HYPE = {
    "keystone": "state the finding",
    "beautiful": "delete",
    "beautifully": "delete",
    "elegant": "delete",
    "elegantly": "delete",
    "crucially": "delete",
    "crucial": "delete",
    "remarkable": "delete",
    "remarkably": "delete",
    "profound": "delete",
    "profoundly": "delete",
    "deeply": "delete",
    "superb": "delete",
    "excellent": "delete",
    "brilliant": "delete",
    "awesome": "delete",
    "flawless": "delete",
    "seamless": "delete",
    "seamlessly": "delete",
    "effortless": "delete",
    "effortlessly": "delete",
    "powerful": "delete",
    "revolutionary": "delete",
    "groundbreaking": "delete",
    "cutting-edge": "delete",
    "state-of-the-art": "delete",
    "world-class": "delete",
    "best-in-class": "delete",
    "game-changing": "delete",
    "obviously": "delete",
    "clearly": "delete",
    "of course": "delete",
    "simply": "delete",
    "nicely": "delete",
    "great job": "delete",
    "well done": "delete",
    "the real work": "state the fact",
    "what matters here": "state the fact",
}

LATIN = {
    "e.g.": "for example",
    "i.e.": "that is",
    "etc.": "and more",
    "cf.": "compare",
    "vs.": "against",
    "et al.": "and others",
    "viz.": "namely",
    "via": "through",
}

CONTRACTIONS = (
    "can't|won't|don't|doesn't|didn't|isn't|aren't|wasn't|weren't|hasn't|haven't|"
    "hadn't|it's|that's|there's|here's|we're|we've|we'll|we'd|you're|you've|you'll|"
    "they're|they've|they'll|I'm|I've|I'll|let's|shouldn't|couldn't|wouldn't|mustn't|"
    "ain't|isnt|dont|doesnt"
)

# Past participles that need no "-ed" suffix.
IRREGULAR_PARTICIPLES = (
    "done|made|given|taken|shown|written|built|sent|kept|held|found|set|put|read|"
    "run|seen|told|left|lost|met|paid|sold|spent|brought|thought|caught|taught|"
    "understood|chosen|driven|eaten|fallen|forgotten|hidden|broken|spoken|stolen|"
    "worn|torn|drawn|grown|thrown|flown|blown|known|begun|become|come|gone"
)

# Words that end in "-en" or "-ed" but are not participles.
PASSIVE_STOP = frozenset(
    {
        "often",
        "open",
        "seven",
        "ten",
        "garden",
        "token",
        "golden",
        "wooden",
        "sudden",
        "even",
        "when",
        "then",
        "within",
    }
)

# Sentences do not end after these tokens.
ABBREVIATIONS = frozenset(
    {
        "e.g.",
        "i.e.",
        "etc.",
        "cf.",
        "vs.",
        "al.",
        "viz.",
        "fig.",
        "no.",
        "approx.",
        "dr.",
        "mr.",
        "ms.",
    }
)

# Function words that a sentence rarely ends on.  A line that ends with one of
# them is a wrapped sentence, so the next line continues it.
CONTINUATION = frozenset(
    [
        "and",
        "or",
        "but",
        "so",
        "the",
        "a",
        "an",
        "of",
        "to",
        "in",
        "on",
        "at",
        "by",
        "for",
        "with",
        "from",
        "into",
        "over",
        "under",
        "that",
        "which",
        "who",
        "whom",
        "whose",
        "is",
        "are",
        "was",
        "were",
        "be",
        "been",
        "being",
        "not",
        "it",
        "its",
        "their",
        "they",
        "this",
        "these",
        "those",
        "as",
        "if",
        "when",
        "then",
        "than",
        "because",
        "while",
        "does",
        "do",
        "did",
        "must",
        "can",
        "may",
        "will",
        "shall",
        "should",
        "would",
        "could",
        "has",
        "have",
        "had",
        "there",
        "here",
        "also",
        "both",
    ]
)

# Skip any line that carries this marker.  Use it for text that is data, not prose.
IGNORE = re.compile(r"ste-lint:\s*ignore", re.IGNORECASE)


# ------------------------------------------------------------------ patterns

INLINE_CODE = re.compile(r"`[^`\n]*`")
HTML_COMMENT = re.compile(r"<!--.*?-->")
URL = re.compile(r"<https?://[^>\s]+>|https?://\S+")
LINK_TARGET = re.compile(r"\]\([^)\n]*\)")
TABLE_SEP = re.compile(r"^\s*\|?[\s:|-]*-[\s:|-]*\|?\s*$")
FENCE = re.compile(r"^\s*(```|~~~)")
BADGE = re.compile(r"!\[[^\]]*\]\([^)]*\)")

SENTENCE_SEP = re.compile(r"(?<=[.!?])[ \t]+")
WORD = re.compile(r"\S+")
CONTRACTION_RE = re.compile(rf"\b(?:{CONTRACTIONS})\b", re.IGNORECASE)
LATIN_RE = re.compile(
    r"(?<![\w.])(?:{})(?![\w])".format("|".join(re.escape(k) for k in LATIN)), re.IGNORECASE
)
WORDY_RE = re.compile(
    r"\b(?:{})\b".format("|".join(re.escape(k) for k in sorted(WORDY, key=len, reverse=True))),
    re.IGNORECASE,
)
HYPE_RE = re.compile(
    r"(?:\b(?:{})\b)".format("|".join(re.escape(k) for k in sorted(HYPE, key=len, reverse=True))),
    re.IGNORECASE,
)
# Emoji only.  Arrows and box-drawing characters are deliberate in ASCII art,
# so the arrow and dingbat blocks stay out.
EMOJI_RE = re.compile("[\U0001f000-\U0001faff]|[\u2728\u2705\u274c\u2757\u2764\u2b50\u26a0\ufe0f]")
PASSIVE_RE = re.compile(
    rf"\b(?:is|are|was|were|be|been|being)\s+(?:\w+ly\s+)?(\w+(?:ed|en)\b|{IRREGULAR_PARTICIPLES}\b)",
    re.IGNORECASE,
)
EXPLETIVE_RE = re.compile(r"\bthere\s+(?:is|are|was|were)\b", re.IGNORECASE)

# Line-comment token and block-comment delimiter per extension.
LINE_COMMENT = {
    ".lean": "--",
    ".py": "#",
    ".sh": "#",
    ".bash": "#",
    ".yml": "#",
    ".yaml": "#",
    ".toml": "#",
    ".cfg": "#",
    ".c": "//",
    ".h": "//",
    ".cc": "//",
    ".cpp": "//",
    ".hpp": "//",
    ".sv": "//",
    ".svh": "//",
    ".v": "//",
    ".js": "//",
    ".ts": "//",
    ".java": "//",
    ".rs": "//",
    ".go": "//",
}
BLOCK_COMMENT = {
    ".lean": ("/-", "-/"),
    ".c": ("/*", "*/"),
    ".h": ("/*", "*/"),
    ".cc": ("/*", "*/"),
    ".cpp": ("/*", "*/"),
    ".hpp": ("/*", "*/"),
    ".sv": ("/*", "*/"),
    ".svh": ("/*", "*/"),
    ".v": ("/*", "*/"),
    ".java": ("/*", "*/"),
    ".rs": ("/*", "*/"),
    ".go": ("/*", "*/"),
    ".css": ("/*", "*/"),
}


@dataclass(frozen=True)
class Finding:
    path: str
    line: int
    col: int
    severity: Severity
    rule: str
    text: str
    detail: str

    def render(self) -> str:
        head = (
            f"{self.path}:{self.line}:{self.col}: {self.severity.value}: {self.text} [{self.rule}]"
        )
        return f"{head}\n    {self.detail}" if self.detail else head

    def github(self) -> str:
        kind = "error" if self.severity is Severity.ERROR else "warning"
        return (
            f"::{kind} file={self.path},line={self.line},col={self.col}::{self.rule}: {self.text}"
        )


# ------------------------------------------------------------------ cleaning


def _blank(match: re.Match) -> str:
    """Replace a match with spaces.  Keeps line length, so columns stay true."""
    return re.sub(r"[^\n]", " ", match.group(0))


def clean_line(line: str) -> str:
    """Remove code, links, and markup from one prose line."""
    if TABLE_SEP.match(line):
        return ""
    for pattern in (INLINE_CODE, HTML_COMMENT, BADGE, LINK_TARGET, URL):
        line = pattern.sub(_blank, line)
    return line


def markdown_lines(text: str) -> list[tuple[int, str]]:
    """Yield (lineno, prose) for markdown.  Fenced code blocks are dropped."""
    out: list[tuple[int, str]] = []
    in_fence = False
    for lineno, raw in enumerate(text.splitlines(), 1):
        if FENCE.match(raw):
            in_fence = not in_fence
            continue
        if in_fence:
            continue
        out.append((lineno, clean_line(raw)))
    return out


def _find_line_comment(payload: str, token: str) -> int:
    """Index of the first real line comment, or -1.

    A comment token starts a line or follows whitespace, and it must not sit
    inside a string literal.  This keeps `http://`, `"#tag"` and a Bazel label
    in a C++ string, as in `"bazel run //generators:generate_all"`, out of the
    prose.
    """
    quote = ""
    idx = 0
    while idx < len(payload):
        char = payload[idx]
        if quote:
            if char == "\\":
                idx += 2
                continue
            if char == quote:
                quote = ""
            idx += 1
            continue
        if char in "\"'":
            quote = char
            idx += 1
            continue
        if payload.startswith(token, idx) and (idx == 0 or payload[idx - 1] in " \t"):
            return idx
        idx += 1
    return -1


def comment_lines(path: Path, text: str) -> list[tuple[int, str]]:
    """Yield (lineno, prose) for the comments of a source file."""
    ext = path.suffix.lower()
    line_token = LINE_COMMENT.get(ext)
    block = BLOCK_COMMENT.get(ext)
    if line_token is None and block is None:
        return []

    out: list[tuple[int, str]] = []
    in_block = False
    for lineno, raw in enumerate(text.splitlines(), 1):
        payload = raw
        if block is not None:
            while payload:
                if in_block:
                    end = payload.find(block[1])
                    if end < 0:
                        out.append((lineno, payload))
                        payload = ""
                        break
                    out.append((lineno, payload[:end]))
                    payload = payload[end + len(block[1]) :]
                    in_block = False
                    continue
                start = payload.find(block[0])
                if start < 0:
                    break
                rest = payload[start + len(block[0]) :]
                end = rest.find(block[1])
                if end < 0:
                    out.append((lineno, rest))
                    in_block = True
                    payload = ""
                    break
                out.append((lineno, rest[:end]))
                payload = rest[end + len(block[1]) :]
        if payload and line_token is not None:
            idx = _find_line_comment(payload, line_token)
            if idx >= 0:
                out.append((lineno, payload[idx + len(line_token) :]))
    return [(n, clean_line(t)) for n, t in out]


def prose_lines(path: Path, text: str) -> list[tuple[int, str]]:
    """Prose segments of one file, as (lineno, text)."""
    if path.suffix.lower() in PROSE_EXTS:
        return markdown_lines(text)
    return comment_lines(path, text)


# ------------------------------------------------------------------- rules


def count_words(sentence: str) -> int:
    return sum(1 for token in WORD.findall(sentence) if any(c.isalnum() for c in token))


def ends_sentence(prev: str) -> bool:
    """False when a split after `prev` was caused by an abbreviation or number."""
    last = prev.rstrip().rsplit(" ", 1)[-1].lower()
    if last in ABBREVIATIONS:
        return False
    if re.fullmatch(r"[a-z]\.", last):  # a single initial, as in "J."
        return False
    # A version or decimal, as in "1.2.".
    return not re.fullmatch(r"[\d.]+\.", last)


def ends_open(text: str) -> bool:
    """True when the next line continues this one.

    A wrapped sentence stops mid-thought, so it ends with a comma, a dash, or a
    function word.  A closed line ends with a content word or a period.
    """
    stripped = text.rstrip()
    if not stripped:
        return False
    if stripped.endswith((",", "\u2014", "-", ":", "(")):
        return True
    last = re.split(r"[\s/]+", stripped)[-1].strip(",;:").lower()
    return last in CONTINUATION


def split_sentences(text: str) -> list[tuple[int, str]]:
    """Split text into (offset, sentence) pairs.  Offsets are exact."""
    pieces: list[tuple[int, str]] = []
    start = 0
    for match in SENTENCE_SEP.finditer(text):
        pieces.append((start, text[start : match.end()]))
        start = match.end()
    pieces.append((start, text[start:]))

    merged: list[tuple[int, str]] = []
    for offset, piece in pieces:
        if merged and not ends_sentence(merged[-1][1]):
            prev_offset, prev = merged[-1]
            merged[-1] = (prev_offset, prev + piece)
        else:
            merged.append((offset, piece))
    return [(offset, s.strip()) for offset, s in merged if s.strip()]


def lint_text(path: str, segments: list[tuple[int, str]], strict: bool) -> list[Finding]:
    """Apply every rule to the prose segments of one file."""
    findings: list[Finding] = []
    warnings_block = strict
    paragraph: list[tuple[int, str]] = []

    def flush() -> None:
        if not paragraph:
            return
        joined = " ".join(t for _, t in paragraph)
        offsets = []
        cursor = 0
        for lineno, text in paragraph:
            offsets.append((cursor, lineno))
            cursor += len(text) + 1
        sentences = split_sentences(joined)
        for offset, sentence in sentences:
            lineno = max((ln for off, ln in offsets if off <= offset), default=paragraph[0][0])
            words = count_words(sentence)
            if words >= SENTENCE_FAIL_WORDS:
                findings.append(
                    Finding(
                        path,
                        lineno,
                        1,
                        Severity.ERROR,
                        Rule.SENTENCE,
                        f"sentence has {words} words (STE limit {SENTENCE_FAIL_WORDS - 1})",
                        sentence[:80],
                    )
                )
            elif words >= SENTENCE_WARN_WORDS:
                findings.append(
                    Finding(
                        path,
                        lineno,
                        1,
                        Severity.ERROR if warnings_block else Severity.WARNING,
                        Rule.SENTENCE,
                        f"sentence has {words} words (STE limit {SENTENCE_WARN_WORDS - 1})",
                        sentence[:80],
                    )
                )
        if len(sentences) > PARAGRAPH_MAX_SENTENCES:
            findings.append(
                Finding(
                    path,
                    paragraph[0][0],
                    1,
                    Severity.ERROR if warnings_block else Severity.WARNING,
                    Rule.PARAGRAPH,
                    f"paragraph has {len(sentences)} sentences (limit {PARAGRAPH_MAX_SENTENCES})",
                    "",
                )
            )
        paragraph.clear()

    carries_on = False
    previous = 0
    for lineno, text in segments:
        if IGNORE.search(text):
            continue

        # A line joins the paragraph only when the line before it stops in the
        # middle of a sentence.  This keeps a run of short label comments from
        # reading as one long sentence.
        #
        # A gap in the line numbers also breaks the paragraph.  `--diff` keeps
        # only the added lines, so two added lines that are far apart would
        # otherwise merge into a sentence that exists nowhere.
        if previous and lineno != previous + 1:
            flush()

        if not text.strip() or not carries_on:
            flush()

        if not text.strip():
            continue

        paragraph.append((lineno, text))
        carries_on = ends_open(text)
        previous = lineno
        add_line_findings(path, lineno, text, warnings_block, findings)

    flush()
    return findings


def add_line_findings(
    path: str, lineno: int, text: str, warnings_block: bool, out: list[Finding]
) -> None:
    hits: list[Finding] = []

    def add(col: int, severity: Severity, rule: str, message: str, detail: str = "") -> None:
        hits.append(Finding(path, lineno, col, severity, rule, message, detail))

    warn = Severity.ERROR if warnings_block else Severity.WARNING

    for match in re.finditer(r";", text):
        add(match.start() + 1, Severity.ERROR, Rule.SEMICOLON, "semicolon in prose")

    for match in CONTRACTION_RE.finditer(text):
        add(
            match.start() + 1,
            Severity.ERROR,
            Rule.CONTRACTION,
            f'contraction "{match.group(0)}"',
        )

    for match in LATIN_RE.finditer(text):
        key = match.group(0).lower().rstrip(".")
        replacement = LATIN.get(match.group(0).lower()) or LATIN.get(key + ".") or LATIN.get(key)
        add(
            match.start() + 1,
            Severity.ERROR,
            Rule.LATIN,
            f'Latin abbreviation "{match.group(0)}": use "{replacement}"',
        )

    for match in WORDY_RE.finditer(text):
        replacement = WORDY[match.group(0).lower()]
        detail = f'use "{replacement}"' if replacement else "delete the phrase"
        add(
            match.start() + 1,
            Severity.ERROR,
            Rule.WORDY,
            f'wordy phrase "{match.group(0)}"',
            detail,
        )

    for match in HYPE_RE.finditer(text):
        add(
            match.start() + 1,
            Severity.ERROR,
            Rule.HYPE,
            f'praise or filler "{match.group(0)}"',
            HYPE[match.group(0).lower()],
        )

    for match in EMOJI_RE.finditer(text):
        add(match.start() + 1, Severity.ERROR, Rule.HYPE, "emoji in technical prose")

    for match in EXPLETIVE_RE.finditer(text):
        add(
            match.start() + 1,
            warn,
            Rule.EXPLETIVE,
            f'expletive "{match.group(0)}"',
        )

    for match in PASSIVE_RE.finditer(text):
        if match.group(1).lower() in PASSIVE_STOP:
            continue
        add(
            match.start() + 1,
            warn,
            Rule.PASSIVE,
            f'passive voice "{match.group(0)}"',
        )

    out.extend(sorted(hits, key=lambda f: f.col)[:MAX_FINDINGS_PER_LINE])


# -------------------------------------------------------------------- input


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        print(f"ste-lint: cannot read {path}: {exc}", file=sys.stderr)
        return ""


def tracked_files() -> list[Path]:
    """Lintable files under version control, one entry per real path."""
    proc = subprocess.run(
        ["git", "ls-files"], cwd=ROOT, capture_output=True, text=True, check=False
    )
    if proc.returncode != 0:
        return []

    seen: set[Path] = set()
    out: list[Path] = []
    for name in proc.stdout.splitlines():
        path = ROOT / name
        if SKIP_DIRS.intersection(path.parts) or not is_lintable(path) or not path.is_file():
            continue
        real = path.resolve()
        if real in seen or real.is_dir():  # is_dir catches submodule gitlinks
            continue
        seen.add(real)
        out.append(path)
    return out


def is_lintable(path: Path) -> bool:
    if path.name in SKIP_FILES:
        return False
    ext = path.suffix.lower()
    return ext in PROSE_EXTS or ext in LINE_COMMENT or ext in BLOCK_COMMENT


def expand(paths: list[str]) -> list[Path]:
    out: list[Path] = []
    for raw in paths:
        path = Path(raw)
        if path.is_dir():
            out.extend(p for p in sorted(path.rglob("*")) if p.is_file() and is_lintable(p))
        elif path.is_file():
            out.append(path)
        else:
            print(f"ste-lint: no such path: {raw}", file=sys.stderr)
    return [p for p in out if not SKIP_DIRS.intersection(p.parts)]


HUNK = re.compile(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@")
FILE = re.compile(r"^\+\+\+ b/(.+)$")


def staged_added_lines() -> dict[str, set[int]]:
    """Map each staged file to the line numbers it gains."""
    proc = subprocess.run(
        ["git", "diff", "--cached", "-U0", "--diff-filter=ACM"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    added: dict[str, set[int]] = {}
    current = None
    for line in proc.stdout.splitlines():
        match = FILE.match(line)
        if match:
            current = match.group(1)
            added.setdefault(current, set())
            continue
        match = HUNK.match(line)
        if match and current is not None:
            start = int(match.group(1))
            count = int(match.group(2) or 1)
            added[current].update(range(start, start + count))
    return added


def commit_findings(text: str, name: str = "<commit>") -> list[Finding]:
    """The mechanical rules of one commit message."""
    out: list[Finding] = []
    lines = text.splitlines()
    subject_index = next((i for i, line in enumerate(lines) if line.strip()), None)
    if subject_index is None:
        return [
            Finding(name, 1, 1, Severity.ERROR, Rule.SUBJECT_CASE, "the message has no subject", "")
        ]

    subject = lines[subject_index].rstrip()
    lineno = subject_index + 1
    if len(subject) > SUBJECT_HARD:
        out.append(
            Finding(
                name,
                lineno,
                SUBJECT_HARD + 1,
                Severity.ERROR,
                Rule.SUBJECT_LONG,
                f"subject is {len(subject)} characters (limit {SUBJECT_HARD})",
                subject,
            )
        )
    elif len(subject) > SUBJECT_MAX:
        out.append(
            Finding(
                name,
                lineno,
                SUBJECT_MAX + 1,
                Severity.WARNING,
                Rule.SUBJECT_LONG,
                f"subject is {len(subject)} characters (target {SUBJECT_MAX})",
                subject,
            )
        )

    if subject[:1].islower():
        out.append(
            Finding(
                name,
                lineno,
                1,
                Severity.ERROR,
                Rule.SUBJECT_CASE,
                "capitalize the subject",
                subject,
            )
        )
    if subject.endswith("."):
        out.append(
            Finding(
                name,
                lineno,
                len(subject),
                Severity.ERROR,
                Rule.SUBJECT_PERIOD,
                "the subject ends with a period",
                subject,
            )
        )
    if subject.startswith(("fixup!", "squash!", "WIP", "wip")):
        out.append(
            Finding(
                name,
                lineno,
                1,
                Severity.ERROR,
                Rule.FIXUP,
                "a fixup, squash or WIP commit must not land",
                subject,
            )
        )

    body = lines[subject_index + 1 :]
    if any(line.strip() for line in body) and body and body[0].strip():
        out.append(
            Finding(
                name,
                subject_index + 2,
                1,
                Severity.ERROR,
                Rule.BLANK_LINE,
                "put a blank line after the subject",
                body[0],
            )
        )

    for offset, line in enumerate(lines, 1):
        stripped = line.rstrip()
        if stripped != line:
            out.append(
                Finding(
                    name,
                    offset,
                    len(stripped) + 1,
                    Severity.ERROR,
                    Rule.TRAILING_WS,
                    "trailing whitespace",
                    stripped[-40:],
                )
            )
        if (
            offset > subject_index + 1
            and len(line) > BODY_MAX
            and not line.lstrip().startswith("http")
        ):
            out.append(
                Finding(
                    name,
                    offset,
                    BODY_MAX + 1,
                    Severity.WARNING,
                    Rule.BODY_WRAP,
                    f"body line is {len(line)} characters (limit {BODY_MAX})",
                    line[:40],
                )
            )
    return out


def read_stdin(text: str | None = None) -> list[tuple[int, str]]:
    """Read a commit message.  Drop comment lines and the scissors block."""
    if text is None:
        text = sys.stdin.read()
    cut = text.find("# ------------------------ >8 ------------------------")
    if cut >= 0:
        text = text[:cut]
    out = []
    for lineno, line in enumerate(text.splitlines(), 1):
        if line.lstrip().startswith("#"):
            continue
        out.append((lineno, clean_line(line)))
    return out


# ---------------------------------------------------------------------- main


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        prog="ste-lint.py", description="Dictionary-free ASD-STE100 prose linter."
    )
    parser.add_argument("paths", nargs="*", help="files or directories to lint")
    parser.add_argument("--stdin", action="store_true", help="lint a commit message on stdin")
    parser.add_argument(
        "--commit-log",
        help="lint every commit message in the given git range, for example origin/main..HEAD",
    )
    parser.add_argument("--all", action="store_true", help="lint every tracked prose file")
    parser.add_argument(
        "--diff", action="store_true", help="lint only the lines added in the staged diff"
    )
    parser.add_argument("--strict", action="store_true", help="treat warnings as errors")
    parser.add_argument("--github", action="store_true", help="emit GitHub Actions annotations")
    parser.add_argument(
        "--max",
        type=int,
        default=MAX_FINDINGS,
        help=f"stop after N findings (default {MAX_FINDINGS})",
    )
    parser.add_argument("--quiet", action="store_true", help="suppress the summary line")
    parser.add_argument("--list-rules", action="store_true", help="print the rule table")
    return parser.parse_args(argv)


def main(argv: list[str]) -> int:
    args = parse_args(argv)

    if args.list_rules:
        for rule, text in RULE_HELP.items():
            print(f"{rule}  {text}")
        return 0

    findings: list[Finding] = []
    if args.stdin:
        message = sys.stdin.read()
        findings += commit_findings(message)
        findings += lint_text("<stdin>", read_stdin(message), args.strict)
    elif args.commit_log:
        log = subprocess.run(
            ["git", "log", "--no-merges", "--format=%H%x00%B%x00", args.commit_log],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        ).stdout
        parts = log.split("\x00")
        for index in range(0, len(parts) - 1, 2):
            sha = parts[index].strip()
            if not sha:
                continue
            message = parts[index + 1]
            name = sha[:12]
            findings += commit_findings(message, name)
            findings += lint_text(name, read_stdin(message), args.strict)
    else:
        if not (args.paths or args.all or args.diff):
            print("ste-lint: give paths, or --stdin/--all/--diff", file=sys.stderr)
            return 2
        if args.paths:
            targets = expand(args.paths)
            added: dict[str, set[int]] | None = None
        else:
            targets = tracked_files() if args.all else []
            added = staged_added_lines() if args.diff else None
            if added is not None:
                targets = [ROOT / name for name in added if is_lintable(ROOT / name)]
        for path in targets:
            segments = prose_lines(path, read_text(path))
            if added is not None:
                key = str(path.relative_to(ROOT)) if path.is_absolute() else str(path)
                keep = added.get(key, set())
                segments = [(ln, text) for ln, text in segments if ln in keep]
            try:
                display = str(path.relative_to(ROOT))
            except ValueError:
                display = str(path)
            findings += lint_text(display, segments, args.strict)

    findings.sort(key=lambda f: (f.path, f.line, f.col, f.severity.rank))
    for finding in findings[: args.max]:
        print(finding.github() if args.github else finding.render())

    errors = sum(1 for f in findings if f.severity is Severity.ERROR)
    overflow = len(findings) - min(len(findings), args.max)
    if not args.quiet and not args.github:
        tail = f", {overflow} not shown" if overflow > 0 else ""
        print(f"ste-lint: {len(findings)} finding(s), {errors} error(s){tail}")
    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
