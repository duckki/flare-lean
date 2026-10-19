module

import Lake

/-! Lake entry point for the repository's style, import, and proof checks. -/

public def main (args : List String) : IO UInt32 := do
  let child ←
    IO.Process.spawn
      {
        cmd := "python3"
        args := #["scripts/lint.py"] ++ args.toArray
      }
  child.wait
