"""Documentation checks reject broken navigation without inspecting code samples."""

from pathlib import Path
import tempfile
import unittest

import check_docs


class DocumentationTests(unittest.TestCase):
    def test_moved_file_and_renamed_heading_fail_with_source_locations(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "README.md"
            source.write_text("[Guide](guide.md#setup)\n[Moved](old/guide.md)\n")
            (root / "guide.md").write_text("# Guide\n\n## Installation\n")
            count, errors = check_docs.check([source], root)
            self.assertEqual(count, 2)
            self.assertEqual(len(errors), 2)
            self.assertIn("README.md:1: guide.md#setup has no matching heading", errors)
            self.assertIn("README.md:2: old/guide.md does not exist", errors)

    def test_code_examples_and_comments_are_not_navigation(self):
        source = '''# Guide
```markdown
[Example](missing.md)
## Hidden heading
```
~~~
[Example](also-missing.md)
~~~
`[Example](inline.md)` and ``[Example](inline-too.md)``
<!-- [Example](comment.md) -->
[Visible](#guide)
'''
        self.assertEqual(list(check_docs.links(source)), [(11, "#guide")])
        self.assertEqual(check_docs.headings(source), {"guide"})

    def test_encoded_paths_duplicate_headings_and_main_branch_links(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "README.md"
            (root / "My Guide.md").write_text("# Using `Float`\n## Café & bounds\n## Café & bounds\n")
            source.write_text(
                "[Code](My%20Guide.md#using-float)\n"
                "[Unicode](<My Guide.md#caf%C3%A9--bounds-1>)\n"
                "[Main](https://github.com/duckki/flare-lean/blob/main/My%20Guide.md#using-float)\n"
                "[Old](https://github.com/duckki/flare-lean/blob/old/missing.md)\n"
                "[Remote](https://example.org/missing.md)\n"
            )
            self.assertEqual(check_docs.check([source], root), (3, []))

    def test_parent_escape_is_rejected_and_local_code_fragments_are_allowed(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source = root / "README.md"
            (root / "code.py").write_text("value = 1\n")
            source.write_text("[Code](code.py#L1)\n[Outside](../outside.md)\n")
            count, errors = check_docs.check([source], root)
            self.assertEqual(count, 2)
            self.assertEqual(errors, ["README.md:2: ../outside.md escapes the repository"])


if __name__ == "__main__":
    unittest.main()
