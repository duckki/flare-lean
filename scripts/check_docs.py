#!/usr/bin/env python3
"""Check inline repository Markdown links and heading fragments without a network.

GitHub links to this repository's main branch are checked against the checkout.
Links to other sites and pinned historical revisions are left to their owners.
"""

from html import unescape
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

from lint import ROOT, source_files


LINK = re.compile(r'!?\[[^\]\n]*\]\(\s*(?:<([^>\n]+)>|([^\s)]+))(?:\s+"[^"\n]*")?\s*\)')
REPOSITORY = "/duckki/flare-lean/"


def prose(source):
    """Mask fenced code, comments and inline code while preserving line numbers."""
    lines = []
    fence = None
    for line in source.splitlines(keepends=True):
        marker = re.match(r" {0,3}(`{3,}|~{3,})(.*)$", line.rstrip("\n"))
        if fence is not None:
            if marker and marker[1][0] == fence[0] and len(marker[1]) >= len(fence) and not marker[2].strip():
                fence = None
            lines.append("\n" if line.endswith("\n") else "")
        elif marker:
            fence = marker[1]
            lines.append("\n" if line.endswith("\n") else "")
        else:
            lines.append(line)
    text = "".join(lines)
    text = re.sub(r"<!--.*?-->", lambda m: "\n" * m[0].count("\n"), text, flags=re.DOTALL)
    return text


def headings(source):
    """GitHub-style IDs for ATX headings, including duplicates and Unicode."""
    seen = set()
    for line in prose(source).splitlines():
        match = re.match(r" {0,3}#{1,6}\s+(.+?)(?:\s+#+)?\s*$", line)
        if not match:
            continue
        title = re.sub(r"!?\[([^]]*)\]\([^)]*\)", r"\1", match[1])
        title = unescape(re.sub(r"<[^>]*>", "", title)).lower()
        base = re.sub(r"[^\w\- ]", "", title).replace(" ", "-")
        slug = base
        count = 0
        while slug in seen:
            count += 1
            slug = f"{base}-{count}"
        seen.add(slug)
    return seen


def links(source):
    text = prose(source)
    # Inline code can contain example Markdown syntax. Heading text retains it
    # above because a code span's visible contents contribute to its heading ID.
    text = re.sub(r"(`+)(?!`)(.+?)(?<!`)\1(?!`)",
                  lambda m: "\n" * m[0].count("\n"), text)
    for match in LINK.finditer(text):
        yield text.count("\n", 0, match.start()) + 1, match[1] or match[2]


def destination(source, target, root):
    url = urlsplit(target)
    if url.scheme or url.netloc:
        if url.netloc != "github.com":
            return None
        for kind in ("blob", "tree"):
            prefix = REPOSITORY + kind + "/main/"
            if url.path.startswith(prefix):
                return (root / unquote(url.path[len(prefix):])).resolve(), unquote(url.fragment)
        return None
    path = unquote(url.path)
    if path.startswith("/"):
        resolved = root / path.lstrip("/")
    elif path:
        resolved = source.parent / path
    else:
        resolved = source
    return resolved.resolve(), unquote(url.fragment)


def check(paths, root=ROOT):
    errors = []
    count = 0
    anchors = {}
    root = root.resolve()
    for source in paths:
        source = source.resolve()
        for line, target in links(source.read_text()):
            selected = destination(source, target, root)
            if selected is None:
                continue
            count += 1
            path, fragment = selected
            prefix = f"{source.relative_to(root)}:{line}: {target}"
            if not path.is_relative_to(root):
                errors.append(prefix + " escapes the repository")
            elif not path.exists():
                errors.append(prefix + " does not exist")
            elif fragment and path.suffix.lower() == ".md":
                if path not in anchors:
                    anchors[path] = headings(path.read_text())
                if fragment not in anchors[path]:
                    errors.append(prefix + " has no matching heading")
    return count, errors


def main():
    paths = [ROOT / name for name in source_files() if name.endswith(".md")]
    count, errors = check(paths)
    if errors:
        print("\n".join(errors), file=sys.stderr)
        return 1
    print(f"Checked {len(paths)} Markdown files and {count} repository links/heading fragments.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
