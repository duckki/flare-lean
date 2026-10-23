module

public import Flare.Binary64.Memory

/-! Row-major binary64 collection operations with explicit, separate rounding sites.
Shape and source/runtime correspondence belong to each caller's contract. -/

@[expose] public section

namespace Flare.Binary64.Collection

/-- Logical shape and row-major cells; a caller proves their sizes agree. -/
structure Tensor where
  shape : List Nat
  data : Array Float
deriving Inhabited

/-- Elementwise operation with scalar broadcasting only. -/
def binary (op : Float → Float → Float) (count : Nat) (left right : Array Float)
    (leftScalar rightScalar : Bool)
    : Array Float :=
  (Array.range count).map
    fun i =>
      op (left.getD (if leftScalar then 0 else i) 0.0)
        (right.getD (if rightScalar then 0 else i) 0.0)

/-- Transpose a row-major rectangular collection. -/
def transpose (rows columns : Nat) (input : Array Float) : Array Float :=
  (Array.range (rows * columns)).map
    fun i =>
      input.getD ((i % rows) * columns + i / rows) 0.0

/-- One separately rounded multiplication per output cell; no reduction. -/
def outer (rows columns : Nat) (left right : Array Float) : Array Float :=
  (Array.range (rows * columns)).map
    fun i =>
      left.getD (i / columns) 0.0 * right.getD (i % columns) 0.0

@[simp]
theorem binary_size (op : Float → Float → Float) (count : Nat) (left right : Array Float)
    (leftScalar rightScalar : Bool)
    : (binary op count left right leftScalar rightScalar).size = count := by
  simp [binary]

@[simp]
theorem transpose_size (rows columns : Nat) (input : Array Float)
    : (transpose rows columns input).size = rows * columns := by simp [transpose]

@[simp]
theorem outer_size (rows columns : Nat) (left right : Array Float)
    : (outer rows columns left right).size = rows * columns := by simp [outer]

end Flare.Binary64.Collection
