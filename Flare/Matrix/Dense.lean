import Flare.Matrix.Error

/-!
# Dense binary64 operations

Row-major arrays, separately rounded scalar operations, and LDLᵀ factorization
and solves. Callers supply valid shapes. Numerical success and error guarantees
are stated in the corresponding proof modules on their supported domains.
-/

namespace Flare.Matrix.Dense

/-- Reject an exceptional value immediately after an arithmetic operation. -/
def finite (x : Float) : Except Flare.Matrix.DenseError Float :=
  if x.isFinite then .ok x else .error .nonfiniteComputation

/-- Row-major entry. Caller supplies an array with the documented shape. -/
def entry (columns : Nat) (a : Array Float) (row column : Nat) : Float :=
  a.getD (row * columns + column) 0.0

/-- Entrywise division with a finite check after each operation. -/
def divide (a : Array Float) (scalar : Float) : Except Flare.Matrix.DenseError (Array Float) :=
  a.mapM fun x => finite (x / scalar)

/-- Add two d × d diagonal blocks to an existing 2d × 2d matrix. Off-diagonal
blocks are copied unchanged, including signed zeros. Shapes are caller premises. -/
def addDiagonalBlocks (d : Nat) (a first second : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let n := 2 * d
  let mut result := a
  for i in [:d] do
    for j in [:d] do
      let upper ← finite (entry d first i j + entry n a i j)
      let lower ← finite (entry d second i j + entry n a (d + i) (d + j))
      result := result.set! (i * n + j) upper
      result := result.set! ((d + i) * n + d + j) lower
  return result

/-- Row-major identity matrix. -/
def identity (n : Nat) : Array Float :=
  (Array.range (n * n)).map fun i => if i / n == i % n then 1.0 else 0.0

/-- Transpose an array of shape rows × columns. -/
def transpose (rows columns : Nat) (a : Array Float) : Array Float :=
  (Array.range (rows * columns)).map fun i => entry columns a (i % rows) (i / rows)

/-- Add the top and bottom rows × columns blocks of a 2*rows × columns array. -/
def addRowBlocks (rows columns : Nat) (a : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) :=
  (Array.range (rows * columns)).mapM
    fun i =>
      finite (a.getD i 0.0 + a.getD (rows * columns + i) 0.0)

/-- Dense product. Inner indices ascend; each multiplication and addition is
separately rounded and checked. A vector is an inner × 1 right operand. -/
def multiply (rows inner columns : Nat) (a b : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let mut result := Array.replicate (rows * columns) 0.0
  for i in [:rows] do
    for j in [:columns] do
      let mut value := 0.0
      for k in [:inner] do
        let term ← finite (entry inner a i k * entry columns b k j)
        value ← finite (value + term)
      result := result.set! (i * columns + j) value
  return result

/-- Project work storage for a unit lower triangular L and diagonal D. -/
structure Factor where
  lower : Array Float
  diagonal : Array Float

/-- Factor a symmetric n × n matrix. Read the lower triangle; a failed computed
pivot means numerical rejection, not a proof that the input is indefinite. -/
def factor (n : Nat) (a : Array Float) : Except Flare.Matrix.DenseError Factor := do
  let mut lower := Array.replicate (n * n) 0.0
  let mut diagonal := Array.replicate n 0.0
  for j in [:n] do
    let mut pivot := entry n a j j
    for k in [:j] do
      let product ← finite (entry n lower j k * diagonal.getD k 0.0)
      let term ← finite (product * entry n lower j k)
      pivot ← finite (pivot - term)
    unless 0.0 < pivot do
      throw .nonpositivePivot
    diagonal := diagonal.set! j pivot
    lower := lower.set! (j * n + j) 1.0
    for i in [j + 1:n] do
      let mut residual := entry n a i j
      for k in [:j] do
        let product ← finite (entry n lower i k * diagonal.getD k 0.0)
        let term ← finite (product * entry n lower j k)
        residual ← finite (residual - term)
      let value ← finite (residual / pivot)
      lower := lower.set! (i * n + j) value
  return ⟨lower, diagonal⟩

/-- Solve A X = B from an LDLᵀ factor. B and X are n × columns. -/
def solve (n columns : Nat) (f : Factor) (b : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  let mut forward := Array.replicate (n * columns) 0.0
  for i in [:n] do
    for j in [:columns] do
      let mut value := entry columns b i j
      for k in [:i] do
        let term ← finite (entry n f.lower i k * entry columns forward k j)
        value ← finite (value - term)
      forward := forward.set! (i * columns + j) value
  let mut result := Array.replicate (n * columns) 0.0
  for step in [:n] do
    let i := n - 1 - step
    for j in [:columns] do
      let mut value ← finite (entry columns forward i j / f.diagonal.getD i 0.0)
      for k in [i + 1:n] do
        let term ← finite (entry n f.lower k i * entry columns result k j)
        value ← finite (value - term)
      result := result.set! (i * columns + j) value
  return result

/-- Positive-definite solve, with checked factorization and substitution. -/
def solveSPD (n columns : Nat) (a b : Array Float)
    : Except Flare.Matrix.DenseError (Array Float) := do
  solve n columns (← factor n a) b

/-- Copy the lower triangle into the upper triangle. This is an explicit
rounding adaptation: it is the identity on an exactly symmetric real matrix. -/
def mirrorLower (n : Nat) (a : Array Float) : Array Float :=
  Id.run do
    let mut result := a
    for i in [:n] do
      for j in [:i] do
        result := result.set! (j * n + i) (entry n a i j)
    return result

/-- Exact numerical symmetry; signed zeros compare equal. -/
def symmetric (n : Nat) (a : Array Float) : Bool :=
  Id.run do
    for i in [:n] do
      for j in [:i] do
        if a.getD (i * n + j) 0.0 != a.getD (j * n + i) 0.0 then
          return false
    return true

end Flare.Matrix.Dense
