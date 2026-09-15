import Flare.Matrix.Dense

/-!
# Binary64 dense and spectral operations

Dense multiplication and LDLᵀ solves use Dense through an explicit error adapter.
The largest-pivot Jacobi iteration has a fixed stopping threshold and rotation
limit. The pseudoinverse truncates small eigenvalues. These numerical policies
are visible below; proofs retain their explicit dimension and magnitude bounds.

Shapes and domains are caller preconditions. Acceptance by checkPSD alone is
not a certificate of positive semidefiniteness in exact real arithmetic.
-/

namespace Flare.Matrix.Operations

abbrev entry := Flare.Matrix.Dense.entry
abbrev identity := Flare.Matrix.Dense.identity
abbrev transpose := Flare.Matrix.Dense.transpose
abbrev mirrorLower := Flare.Matrix.Dense.mirrorLower

/-- Adapt the two errors raised by the reused dense arithmetic kernels. -/
def adapt {α : Type} (result : Except Flare.Matrix.DenseError α) : Except Flare.Matrix.Error α :=
  match result with
  | .ok x => .ok x
  | .error .nonpositivePivot => .error .nonpositivePivot
  | .error _ => .error .nonfiniteComputation

def finite (x : Float) : Except Flare.Matrix.Error Float :=
  if x.isFinite then .ok x else .error .nonfiniteComputation

def multiply (rows inner columns : Nat) (a b : Array Float) :=
  adapt (Flare.Matrix.Dense.multiply rows inner columns a b)

def solveSPD (n columns : Nat) (a b : Array Float) :=
  adapt (Flare.Matrix.Dense.solveSPD n columns a b)

/-- Addition/subtraction with a fixed, checked operation schedule. -/
def combine (a b : Array Float) (sign : Float := 1.0) : Except Flare.Matrix.Error (Array Float) :=
  (Array.range a.size).mapM
    fun i => do
      let term ← finite (sign * b.getD i 0.0)
      finite (a.getD i 0.0 + term)

def scale (a : Array Float) (s : Float) : Except Flare.Matrix.Error (Array Float) :=
  a.mapM fun x => finite (s * x)

/-- Assemble a symmetric block matrix [A B; Bᵀ D]. -/
def blocks (n m : Nat) (a b d : Array Float) : Array Float :=
  (Array.range ((n + m) * (n + m))).map
    fun index =>
      let i := index / (n + m)
      let j := index % (n + m)
      if i < n then
        if j < n then entry n a i j else entry m b i (j - n)
      else if j < n then
        entry m b j (i - n)
      else
        entry m d (i - n) (j - n)

def maxAbs (a : Array Float) : Float :=
  a.foldl (fun s x => max s x.abs) 0.0

/-- A finite, approximate symmetric eigendecomposition A ≈ V diag(d) Vᵀ.
Values need not be sorted. No exact eigenvector relation is asserted here. -/
structure Spectrum where
  values : Array Float
  vectors : Array Float

/-- Largest-pivot Jacobi algorithm. Normalize by maximum entry magnitude, stop when
every normalized off-diagonal entry is at most 1e-14, reject after 32*n² rotations.
Each rotation copies symmetric entries explicitly. All arithmetic is binary64. -/
def jacobiEigen (n : Nat) (input : Array Float) : Except Flare.Matrix.Error Spectrum := do
  let magnitude := maxAbs input
  if magnitude == 0.0 then
    return ⟨Array.replicate n 0.0, identity n⟩
  let mut a ← input.mapM fun x => finite (x / magnitude)
  let mut v := identity n
  for step in [:32 * n * n + 1] do
    let mut largest := 0.0
    let mut p := 0
    let mut q := 0
    for i in [:n] do
      for j in [i + 1:n] do
        let size := (entry n a i j).abs
        if largest < size then
          largest := size
          p := i
          q := j
    if largest ≤ 1.0e-14 then
      let values ← (Array.range n).mapM fun i => finite (entry n a i i * magnitude)
      return ⟨values, v⟩
    if step == 32 * n * n then
      throw .eigenNotConverged
    let apq := entry n a p q
    let tau ← finite ((entry n a q q - entry n a p p) / (2.0 * apq))
    let t ← finite ((if tau < 0.0 then -1.0 else 1.0) / (tau.abs + (1.0 + tau * tau).sqrt))
    let cosine ← finite (1.0 / (1.0 + t * t).sqrt)
    let sine ← finite (t * cosine)
    let app ← finite (entry n a p p - t * apq)
    let aqq ← finite (entry n a q q + t * apq)
    a := ((a.set! (p * n + p) app).set! (q * n + q) aqq).set! (p * n + q) 0.0
    a := a.set! (q * n + p) 0.0
    for k in [:n] do
      if k != p && k != q then
        let akp := entry n a k p
        let akq := entry n a k q
        let nextP ← finite (cosine * akp - sine * akq)
        let nextQ ← finite (sine * akp + cosine * akq)
        a := (a.set! (k * n + p) nextP).set! (p * n + k) nextP
        a := (a.set! (k * n + q) nextQ).set! (q * n + k) nextQ
      let vkp := entry n v k p
      let vkq := entry n v k q
      let nextP ← finite (cosine * vkp - sine * vkq)
      let nextQ ← finite (sine * vkp + cosine * vkq)
      v := (v.set! (k * n + p) nextP).set! (k * n + q) nextQ
  throw .eigenNotConverged

/-- Approximate PSD diagnostic: no eigenvalue below -1e-8*max(1,maxAbs(A)).
Passing this check does NOT establish mathematical positive semidefiniteness. -/
def checkPSD (n : Nat) (a : Array Float) : Except Flare.Matrix.Error Unit := do
  let eigen ← jacobiEigen n a
  let tolerance ← finite (1.0e-8 * max 1.0 (maxAbs a))
  unless eigen.values.all (fun x => -tolerance ≤ x) do
    throw .negativeEigenvalue

/-- Symmetric pseudoinverse: invert eigenvalues whose absolute value exceeds
1e-10 times the largest absolute eigenvalue; discard the rest. This threshold
is a numerical policy, not an exact rank decision. -/
def symmetricPseudoInverse (n : Nat) (a : Array Float)
    : Except Flare.Matrix.Error (Array Float) := do
  let e ← jacobiEigen n a
  let cutoff ← finite (1.0e-10 * maxAbs e.values)
  let reciprocals ←
    e.values.mapM
      fun x =>
        if cutoff < x.abs then finite (1.0 / x) else pure 0.0
  let mut scaled := e.vectors
  for i in [:n] do
    for j in [:n] do
      let value ← finite (entry n e.vectors i j * reciprocals.getD j 0.0)
      scaled := scaled.set! (i * n + j) value
  return mirrorLower n (← multiply n n n scaled (transpose n n e.vectors))

end Flare.Matrix.Operations
