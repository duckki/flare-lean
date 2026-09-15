"""Regression checks for lint coverage and safe formatting target selection."""

from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import fmt
import lint


class StyleTests(unittest.TestCase):
    def test_code_width_and_whitespace(self):
        self.assertTrue(lint.style_issues("X.lean", "-- " + "x" * 98 + "\n"))
        self.assertFalse(lint.style_issues("X.lean", "-- " + "x" * 97 + "\n"))
        issues = lint.style_issues("X.lean", "def x := 1 \t\n")
        self.assertTrue(any("trailing" in issue for issue in issues))
        self.assertTrue(any("tab" in issue for issue in issues))

    def test_literals_and_nested_comments_are_not_code(self):
        source = '''/- λ $ /- nested -/ still $ -/
def s := "λ $ \\"quoted\\""
def c := '$'
-- def bad__name := λ x => x $ x
def ok := 1
'''
        self.assertFalse(lint.style_issues("X.lean", source))

    def test_forbidden_code_and_private_names(self):
        issues = lint.style_issues("X.lean", "private def bad__name := λ x => x $ x\n")
        self.assertEqual(len(issues), 3)

    def test_scoped_resource_options(self):
        self.assertFalse(lint.style_issues("X.lean", "set_option maxHeartbeats 0 in\n"))
        issues = lint.style_issues("X.lean", "set_option maxHeartbeats 0 -- in a comment\n")
        self.assertTrue(any("scope" in issue for issue in issues))

    def test_markdown_is_not_lean_code(self):
        self.assertFalse(lint.style_issues("README.md", "| $ | λ | " + "x" * 100 + "\n"))
        self.assertTrue(lint.style_issues("README.md", "trailing \n"))

    def test_closure_follows_transitive_imports_and_handles_cycles(self):
        graph = {"Root": {"A"}, "A": {"B"}, "B": {"A"}, "Orphan": set()}
        self.assertEqual(lint.reachable_files(graph, {"Root"}), {"Root", "A", "B"})


class FileSelectionTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.git("init", "-q")
        self.format_root = patch.object(fmt, "ROOT", self.root)
        self.lint_root = patch.object(lint, "ROOT", self.root)
        self.format_root.start()
        self.lint_root.start()
        self.addCleanup(self.format_root.stop)
        self.addCleanup(self.lint_root.stop)

    def git(self, *args):
        return subprocess.check_output(["git", *args], cwd=self.root, stderr=subprocess.DEVNULL)

    def write(self, name, content="-- fixture\n"):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content)

    def test_initial_tree_includes_nested_untracked_and_spaces(self):
        self.write("Flare/Deep/With Space.lean")
        self.write("ignored.lean")
        self.write(".gitignore", "ignored.lean\n")
        self.assertEqual(fmt.selected_files(), ["Flare/Deep/With Space.lean"])
        self.assertIn("Flare/Deep/With Space.lean", lint.source_files())

    def test_base_includes_staged_unstaged_and_untracked_but_not_deleted(self):
        for name in ["Staged.lean", "Unstaged.lean", "Deleted.lean", "Unchanged.lean"]:
            self.write(name)
        self.git("add", ".")
        self.git("-c", "user.name=Tooling Test", "-c", "user.email=test@example.invalid",
                 "commit", "-qm", "fixture")
        self.write("Staged.lean", "-- staged\n")
        self.git("add", "Staged.lean")
        self.write("Unstaged.lean", "-- unstaged\n")
        self.write("New Name.lean")
        (self.root / "Deleted.lean").unlink()
        self.assertEqual(fmt.selected_files("HEAD"),
                         ["New Name.lean", "Staged.lean", "Unstaged.lean"])

    def test_invalid_base_fails(self):
        with self.assertRaises(subprocess.CalledProcessError):
            with patch("subprocess.check_output", side_effect=subprocess.CalledProcessError(128, "git")):
                fmt.selected_files("missing-branch")

    def test_formatter_restores_dropped_source(self):
        original = "theorem example : True := by\n  trivial\n"
        self.write("Example.lean", original)

        def corrupt(*args, **kwargs):
            self.write("Example.lean", "theorem example : True := by\n")
            return 0

        with patch("subprocess.call", side_effect=corrupt), patch("sys.stderr"):
            self.assertEqual(fmt.format_files(["Example.lean"]), 1)
        self.assertEqual((self.root / "Example.lean").read_text(), original)

    def test_formatter_accepts_whitespace_and_passes_width(self):
        self.write("Example.lean", "def example:=1\n")

        def format_source(command, **kwargs):
            self.assertEqual(command,
                             ["lake", "exe", "fmt", "--line-width", "100", "--jobs", "4",
                              "Example.lean"])
            self.write("Example.lean", "def example := 1\n")
            return 0

        with patch("subprocess.call", side_effect=format_source):
            self.assertEqual(fmt.format_files(["Example.lean"]), 0)
        self.assertEqual((self.root / "Example.lean").read_text(), "def example := 1\n")


if __name__ == "__main__":
    unittest.main()
