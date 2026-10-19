module

public import Flare.Matrix.Jacobi

/-! Proof-side extractions of the native Jacobi scan, rotation and iteration.
Execution equalities identify these proof schedules with the native operations.
Array invariants connect the scalar rounding bounds to the actual loops. -/

@[expose] public section

namespace Flare.Matrix.JacobiIteration
open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Binary64.Arithmetic Flare.Binary64.Order Std.Do

set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

/-- The scan's native state, used only for proof decomposition. -/
structure Pivot where
  magnitude : Float
  row : Nat
  column : Nat

/-- Extract the exact largest-pivot scan, including its first-maximum tie rule. -/
def largestPivot (n : Nat) (a : Array Float) : Except Flare.Matrix.Error Pivot := do
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
  return ⟨largest, p, q⟩

/-- Extract one row of the matrix/eigenvector pair-update loop. -/
def rotatePairRow (n p q k : Nat) (cosine sine : Float) (a v : Array Float)
    : Except Flare.Matrix.Error (Array Float × Array Float) := do
  let mut a := a
  let mut v := v
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
  return (a, v)

/-- Extract the pair-update loop shared by the matrix and eigenvector updates. -/
def rotatePairs (n p q : Nat) (cosine sine : Float) (a v : Array Float)
    : Except Flare.Matrix.Error (Array Float × Array Float) := do
  let mut a := a
  let mut v := v
  for k in [:n] do
    let result ← rotatePairRow n p q k cosine sine a v
    a := result.1
    v := result.2
  return (a, v)

/-- Extract one native rotation, including all exceptional-value guards and
the symmetric matrix and eigenvector array writes. -/
def rotate (n : Nat) (a v : Array Float) (p q : Nat)
    : Except Flare.Matrix.Error (Array Float × Array Float) := do
  let apq := entry n a p q
  let tau ← finite ((entry n a q q - entry n a p p) / (2.0 * apq))
  let t ← finite ((if tau < 0.0 then -1.0 else 1.0) / (tau.abs + (1.0 + tau * tau).sqrt))
  let cosine ← finite (1.0 / (1.0 + t * t).sqrt)
  let sine ← finite (t * cosine)
  let app ← finite (entry n a p p - t * apq)
  let aqq ← finite (entry n a q q + t * apq)
  let mut a := ((a.set! (p * n + p) app).set! (q * n + q) aqq).set! (p * n + q) 0.0
  a := a.set! (q * n + p) 0.0
  rotatePairs n p q cosine sine a v

/-- Decompose the native iteration into its scan and rotation without changing
its operation order, stopping test, rescaling or rotation cap. -/
def jacobiBySteps (n : Nat) (input : Array Float) : Except Flare.Matrix.Error Spectrum := do
  let magnitude := maxAbs input
  if magnitude == 0.0 then
    return ⟨Array.replicate n 0.0, identity n⟩
  let mut a ← input.mapM fun x => finite (x / magnitude)
  let mut v := identity n
  for step in [:32 * n * n + 1] do
    let pivot ← largestPivot n a
    if pivot.magnitude ≤ 1.0e-14 then
      let values ← (Array.range n).mapM fun i => finite (entry n a i i * magnitude)
      return ⟨values, v⟩
    if step == 32 * n * n then
      throw .eigenNotConverged
    let result ← rotate n a v pivot.row pivot.column
    a := result.1
    v := result.2
  throw .eigenNotConverged

universe u v

private lemma bind_if {ε : Type u} {α β : Type v} (p : Prop) [Decidable p] (x y : Except ε α)
    (f : α → Except ε β)
    : (if p then x else y) >>= f = if p then x >>= f else y >>= f := by split <;> rfl

/-- The proof-side decomposition executes the actual native eigensolver. -/
theorem jacobiEigen_eq (n : Nat) (input : Array Float)
    : jacobiEigen n input = jacobiBySteps n input := by
  unfold jacobiEigen jacobiBySteps largestPivot rotate rotatePairs rotatePairRow
  simp only [bind_assoc, pure_bind, bind_if]

private def Scan (n : Nat) (a : Array Float) (i j : Nat) (pivot : Pivot) : Prop :=
  pivot.magnitude.isFinite = true
  ∧ 0 ≤ value pivot.magnitude
  ∧ (pivot.magnitude = 0.0
      ∨ pivot.row < pivot.column
        ∧ pivot.column < n
        ∧ pivot.magnitude = (entry n a pivot.row pivot.column).abs)
  ∧ ∀ r t, r < t → t < n → r < i ∨ r = i ∧ t < j → |value (entry n a r t)| ≤ value pivot.magnitude

private lemma scan_step (n : Nat) (a : Array Float) (i j : Nat) (pivot : Pivot)
    (ha : a.all Float.isFinite = true) (hij : i < j) (hj : j < n)
    (h : Scan n a i j pivot)
    : Scan n a i (j + 1)
        (if pivot.magnitude < (entry n a i j).abs then ⟨(entry n a i j).abs, i, j⟩ else pivot) := by
  obtain ⟨hf, hv⟩ := abs_value (entry n a i j) (Flare.Matrix.Storage.getD_finite _ _ ha)
  have hcmp := lt_iff pivot.magnitude (entry n a i j).abs h.1 hf
  rw [hv] at hcmp
  split_ifs with ht
  · refine ⟨hf, by simpa only [hv] using abs_nonneg (value (entry n a i j)),
      Or.inr ⟨hij, hj, rfl⟩, ?_⟩
    intro r t hrt htn hp
    change _ ≤ value (entry n a i j).abs
    rw [hv]
    by_cases he : r = i ∧ t = j
    · rcases he with ⟨rfl, rfl⟩; rfl
    · exact (h.2.2.2 r t hrt htn (by omega)).trans ((hcmp.mp ht).le)
  · refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
    intro r t hrt htn hp
    by_cases he : r = i ∧ t = j
    · rcases he with ⟨rfl, rfl⟩
      exact le_of_not_gt (fun hlt => ht (hcmp.mpr hlt))
    · exact h.2.2.2 r t hrt htn (by omega)

private lemma scan_row_start (n : Nat) (a : Array Float) (i : Nat) (pivot : Pivot)
    (h : Scan n a i 0 pivot)
    : Scan n a i (i + 1) pivot := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro r t hrt htn hp
  exact h.2.2.2 r t hrt htn (by omega)

private lemma scan_row_end (n : Nat) (a : Array Float) (i : Nat) (pivot : Pivot)
    (h : Scan n a i n pivot)
    : Scan n a (i + 1) 0 pivot := by
  refine ⟨h.1, h.2.1, h.2.2.1, ?_⟩
  intro r t hrt htn hp
  exact h.2.2.2 r t hrt htn (by omega)

private lemma range_from_current {a n k : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:n] = pref ++ k :: suff)
    : k = a + pref.length ∧ k < n := by
  have hlist : List.range' a (n - a) = pref ++ k :: suff := by simpa [Std.Legacy.Range.size] using h
  have hlen := congrArg List.length hlist
  simp only [List.length_range', List.length_append, List.length_cons] at hlen
  have he := congrArg (fun xs => xs[pref.length]?) hlist
  simp [show pref.length < n - a by omega] at he
  omega

private theorem largestPivot_triple (n : Nat) (a : Array Float) (ha : a.all Float.isFinite = true)
    : ⦃⌜True⌝⦄ largestPivot n a ⦃⇓ pivot => ⌜Scan n a n 0 pivot⌝⦄ := by
  unfold largestPivot
  apply (Specification.except_iff _ _ _).mpr
  vcgen
    invariants
      | inv1 => fun xs _ ⟨largest, p, q⟩ => Scan n a xs.length 0 ⟨largest, p, q⟩
      | inv2 pref i suff hi state pair p q hstate =>
        fun xs _ ⟨largest, p, q⟩ => Scan n a i (i + 1 + xs.length) ⟨largest, p, q⟩
  all_goals simp_all only [SPred.down_pure_nil]
  case vc1 =>
    refine ⟨by decide, by simp only [largest, zero_value]; exact le_refl 0, Or.inl rfl, ?_⟩
    intro r t hrt htn hp
    simp at hp
  case vc2 =>
    rename_i magnitude p q pair hstate
    simpa using hstate
  case vc3 =>
    rename_i pref i suff hi magnitude p q pair hstate
    have hi' := (Flare.Matrix.Storage.forIn_range_current hi).1
    simpa only [List.length_nil, Nat.add_zero, hi']
      using scan_row_start n a pref.length ⟨magnitude, p, q⟩ hstate
  case vc4 =>
    rename_i pref i suff hi initial p0 q0 pair0 magnitude p q pair hinit hstate
    have hi' := Flare.Matrix.Storage.forIn_range_current hi
    have hend : i + 1 + (ForIn.toList [i + 1:n]).length = n := by
      simp [Std.Legacy.Range.size]
      omega
    have h := scan_row_end n a i ⟨magnitude, p, q⟩
      (by simpa only [hend] using hstate)
    simpa only [List.length_append, List.length_singleton, ← hi'.1] using h
  case vc5 | vc6 =>
    rename_i xsI i zsI hi initial p0 q0 pair0 prefJ j suffJ magnitude p q pair hinit hj hstate hcmp
    have hj' := range_from_current hj
    have h := scan_step n a i j ⟨magnitude, p, q⟩ ha (by omega) hj'.2
      (by simpa only [← hj'.1] using hstate)
    dsimp only [size] at hcmp
    simp only [hcmp, ↓reduceIte] at h
    have hidx : i + 1 + (prefJ ++ [j]).length = j + 1 := by
      simp only [List.length_append, List.length_singleton]
      omega
    simpa only [hidx] using h

/-- The actual largest-pivot scan always succeeds on finite storage. It
returns a maximum magnitude, and every nonzero maximum points to an in-range
strict upper-triangle entry with exactly that native absolute value. -/
theorem largestPivot_correct (n : Nat) (a : Array Float) (ha : a.all Float.isFinite = true)
    : ∃ pivot,
        largestPivot n a = .ok pivot
        ∧ pivot.magnitude.isFinite = true
        ∧ 0 ≤ value pivot.magnitude
        ∧ (pivot.magnitude = 0.0
            ∨ pivot.row < pivot.column
              ∧ pivot.column < n
              ∧ pivot.magnitude = (entry n a pivot.row pivot.column).abs)
        ∧ ∀ i j, i < j → j < n → |value (entry n a i j)| ≤ value pivot.magnitude := by
  have h := largestPivot_triple n a ha
  cases he : largestPivot n a with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok pivot =>
      rw [he] at h
      have hp := h True.intro
      exact ⟨
        pivot,
        rfl,
        hp.1,
        hp.2.1,
        hp.2.2.1,
        fun i j hij hj =>
          hp.2.2.2 i j hij hj (Or.inl (by omega))
      ⟩

/-- Exact native expression for the first component of a rotated row. -/
def pairP (n p q : Nat) (c s : Float) (a : Array Float) (k : Nat) : Float :=
  c * entry n a k p - s * entry n a k q

/-- Exact native expression for the second component of a rotated row. -/
def pairQ (n p q : Nat) (c s : Float) (a : Array Float) (k : Nat) : Float :=
  s * entry n a k p + c * entry n a k q

/-- Matrix entry after the first `step` row-pair updates, including symmetric writes. -/
def matrixPairEntry (n p q : Nat) (c s : Float) (a : Array Float) (step i j : Nat) : Float :=
  if i < step ∧ i ≠ p ∧ i ≠ q ∧ j = p then
    pairP n p q c s a i
  else if j < step ∧ j ≠ p ∧ j ≠ q ∧ i = p then
    pairP n p q c s a j
  else if i < step ∧ i ≠ p ∧ i ≠ q ∧ j = q then
    pairQ n p q c s a i
  else if j < step ∧ j ≠ p ∧ j ≠ q ∧ i = q then
    pairQ n p q c s a j
  else
    entry n a i j

/-- Eigenvector entry after the first `step` row-pair updates. -/
def vectorPairEntry (n p q : Nat) (c s : Float) (v : Array Float) (step i j : Nat) : Float :=
  if i < step ∧ j = p then
    pairP n p q c s v i
  else if i < step ∧ j = q then
    pairQ n p q c s v i
  else
    entry n v i j

private lemma matrixPairEntry_step (n p q k i j : Nat) (c s : Float) (a : Array Float)
    (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q)
    : matrixPairEntry n p q c s a (k + 1) i j
      = if i = k ∧ j = p ∨ i = p ∧ j = k then
          pairP n p q c s a k
        else if i = k ∧ j = q ∨ i = q ∧ j = k then
          pairQ n p q c s a k
        else
          matrixPairEntry n p q c s a k i j := by
  unfold matrixPairEntry
  split_ifs <;> first | rfl | (simp_all; all_goals omega)

private lemma matrixPairEntry_skip (n p q k i j : Nat) (c s : Float) (a : Array Float)
    (hk : k = p ∨ k = q)
    : matrixPairEntry n p q c s a (k + 1) i j = matrixPairEntry n p q c s a k i j := by
  unfold matrixPairEntry
  split_ifs <;> first | rfl | omega

private lemma vectorPairEntry_step (n p q k i j : Nat) (c s : Float) (a : Array Float) (hpq : p ≠ q)
    : vectorPairEntry n p q c s a (k + 1) i j
      = if i = k ∧ j = p then
          pairP n p q c s a k
        else if i = k ∧ j = q then
          pairQ n p q c s a k
        else
          vectorPairEntry n p q c s a k i j := by
  unfold vectorPairEntry
  split_ifs <;> first | rfl | (simp_all; all_goals omega)

private def PairState (n p q : Nat) (c s : Float) (a v : Array Float) (step : Nat)
    (result : Array Float × Array Float)
    : Prop :=
  result.1.size = n * n
  ∧ result.1.all Float.isFinite = true
  ∧ result.2.size = n * n
  ∧ result.2.all Float.isFinite = true
  ∧ (∀ i j, i < n → j < n → entry n result.1 i j = matrixPairEntry n p q c s a step i j)
  ∧ ∀ i j, i < n → j < n → entry n result.2 i j = vectorPairEntry n p q c s v step i j

private lemma symmetric_writes (n p q k i j : Nat) (a : Array Float) (P Q : Float)
    (ha : a.size = n * n) (hp : p < n) (hq : q < n) (hk : k < n) (hj : j < n)
    (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q)
    : entry n ((((a.set! (k * n + p) P).set! (p * n + k) P).set! (k * n + q) Q).set! (q * n + k) Q)
        i j
      = if i = k ∧ j = p ∨ i = p ∧ j = k then
          P
        else if i = k ∧ j = q ∨ i = q ∧ j = k then
          Q
        else
          entry n a i j := by
  unfold Flare.Matrix.Operations.entry
  rw [Flare.Matrix.Storage.entry_set n (((a.set! (k * n + p) P).set! (p * n + k) P).set! (k * n + q)
    Q)
      q k i j Q (by simpa using ha) hq hk hj,
    Flare.Matrix.Storage.entry_set n ((a.set! (k * n + p) P).set! (p * n + k) P)
      k q i j Q (by simpa using ha) hk hq hj,
    Flare.Matrix.Storage.entry_set n (a.set! (k * n + p) P) p k i j P (by simpa using ha) hp hk hj,
    Flare.Matrix.Storage.entry_set n _ k p i j P ha hk hp hj]
  split_ifs <;> first | rfl | omega

private lemma vector_writes (n p q k i j : Nat) (a : Array Float) (P Q : Float)
    (ha : a.size = n * n) (hp : p < n) (hq : q < n) (hk : k < n) (hj : j < n) (hpq : p ≠ q)
    : entry n ((a.set! (k * n + p) P).set! (k * n + q) Q) i j
      = if i = k ∧ j = p then P else if i = k ∧ j = q then Q else entry n a i j := by
  unfold Flare.Matrix.Operations.entry
  rw [Flare.Matrix.Storage.entry_set n (a.set! (k * n + p) P) k q i j Q (by simpa using ha) hk hq
    hj,
    Flare.Matrix.Storage.entry_set n _ k p i j P ha hk hp hj]
  split_ifs <;> first | rfl | omega

private lemma matrix_writes_progress (n p q k : Nat) (c s : Float) (a v : Array Float)
    (result : Array Float × Array Float) (hp : p < n) (hq : q < n) (hk : k < n)
    (hpq : p ≠ q) (hkp : k ≠ p) (hkq : k ≠ q)
    (h : PairState n p q c s a v k result)
    (hP : (pairP n p q c s a k).isFinite = true) (hQ : (pairQ n p q c s a k).isFinite = true)
    : let next :=
        (((result.1.set! (k * n + p) (pairP n p q c s a k)).set! (p * n + k)
            (pairP n p q c s a k)).set!
          (k * n + q) (pairQ n p q c s a k)).set!
          (q * n + k) (pairQ n p q c s a k)
      next.size = n * n
      ∧ next.all Float.isFinite = true
      ∧ ∀ i j, i < n → j < n → entry n next i j = matrixPairEntry n p q c s a (k + 1) i j := by
  refine ⟨by simpa using h.1, ?_, ?_⟩
  · exact Flare.Matrix.Storage.all_set _ _ _
      (Flare.Matrix.Storage.all_set _ _ _
        (Flare.Matrix.Storage.all_set _ _ _
          (Flare.Matrix.Storage.all_set _ _ _ h.2.1 hP) hP) hQ) hQ
  · intro i j hi hj
    rw [symmetric_writes n p q k i j result.1 _ _ h.1 hp hq hk hj hpq hkp hkq,
      h.2.2.2.2.1 i j hi hj, matrixPairEntry_step n p q k i j c s a hpq hkp hkq]

private lemma vector_writes_progress (n p q k : Nat) (c s : Float) (a v : Array Float)
    (result : Array Float × Array Float) (hp : p < n) (hq : q < n) (hk : k < n) (hpq : p ≠ q)
    (h : PairState n p q c s a v k result)
    (hP : (pairP n p q c s v k).isFinite = true) (hQ : (pairQ n p q c s v k).isFinite = true)
    : let next :=
        (result.2.set! (k * n + p) (pairP n p q c s v k)).set! (k * n + q) (pairQ n p q c s v k)
      next.size = n * n
      ∧ next.all Float.isFinite = true
      ∧ ∀ i j, i < n → j < n → entry n next i j = vectorPairEntry n p q c s v (k + 1) i j := by
  refine ⟨by simpa using h.2.2.1, ?_, ?_⟩
  · exact Flare.Matrix.Storage.all_set _ _ _ (Flare.Matrix.Storage.all_set _ _ _ h.2.2.2.1 hP) hQ
  · intro i j hi hj
    rw [vector_writes n p q k i j result.2 _ _ h.2.2.1 hp hq hk hj hpq,
      h.2.2.2.2.2 i j hi hj, vectorPairEntry_step n p q k i j c s v hpq]

private lemma pair_terms_finite (n p q k : Nat) (c s : Float) (a : Array Float)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (ha : a.all Float.isFinite = true)
    (habp : |value (entry n a k p)| ≤ 32) (habq : |value (entry n a k q)| ≤ 32)
    : (pairP n p q c s a k).isFinite = true ∧ (pairQ n p q c s a k).isFinite = true := by
  have hη : (2 : ℝ)^(-1022 : Int) ≤ 1 :=
    (zpow_le_one_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr (by norm_num)
  have h := Jacobi.pair_update_accuracy c s (entry n a k p) (entry n a k q) 128 hc hs
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    hcb hsb (by linarith)
    ((by norm_num : (128 : ℝ) ≤ (2 : ℝ)^(8 : Int)).trans
      (zpow_le_zpow_right₀ (by norm_num) (by norm_num)))
  exact ⟨h.1, h.2.1⟩

private theorem pair_row_progress (n p q k : Nat) (c s : Float) (a v : Array Float)
    (result : Array Float × Array Float) (hp : p < n) (hq : q < n) (hk : k < n) (hpq : p ≠ q)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ k, k < n → k ≠ p → k ≠ q → |value (entry n a k p)| ≤ 32 ∧ |value (entry n a k q)| ≤ 32)
    (hvb : ∀ k, k < n → |value (entry n v k p)| ≤ 32 ∧ |value (entry n v k q)| ≤ 32)
    (h : PairState n p q c s a v k result)
    : ∃ next,
        rotatePairRow n p q k c s result.1 result.2 = .ok next
        ∧ PairState n p q c s a v (k + 1) next := by
  have hVp : entry n result.2 k p = entry n v k p := by
    rw [h.2.2.2.2.2 k p hk hp]
    simp only [vectorPairEntry, lt_self_iff_false, false_and, ↓reduceIte]
  have hVq : entry n result.2 k q = entry n v k q := by
    rw [h.2.2.2.2.2 k q hk hq]
    simp only [vectorPairEntry, lt_self_iff_false, false_and, ↓reduceIte]
  obtain ⟨hPv, hQv⟩ := pair_terms_finite n p q k c s v hc hs hcb hsb hv (hvb k hk).1 (hvb k hk).2
  let nextV := (result.2.set! (k * n + p) (pairP n p q c s v k)).set! (k * n + q) (pairQ n p q c s v
    k)
  have hvec := vector_writes_progress n p q k c s a v result hp hq hk hpq h hPv hQv
  by_cases hrow : k ≠ p ∧ k ≠ q
  · have hAp : entry n result.1 k p = entry n a k p := by
      rw [h.2.2.2.2.1 k p hk hp]
      simp [matrixPairEntry, hrow.1, hrow.2]
    have hAq : entry n result.1 k q = entry n a k q := by
      rw [h.2.2.2.2.1 k q hk hq]
      simp [matrixPairEntry, hrow.1, hrow.2]
    obtain ⟨hPa, hQa⟩ := pair_terms_finite n p q k c s a hc hs hcb hsb ha (hab k hk hrow.1 hrow.2).1
      (hab k hk hrow.1 hrow.2).2
    let nextA := (((result.1.set! (k * n + p) (pairP n p q c s a k)).set! (p * n + k) (pairP n p q c
      s a k)).set!
      (k * n + q) (pairQ n p q c s a k)).set! (q * n + k) (pairQ n p q c s a k)
    have hmat := matrix_writes_progress n p q k c s a v result hp hq hk hpq hrow.1 hrow.2 h hPa hQa
    refine ⟨(nextA, nextV), ?_, hmat.1, hmat.2.1, hvec.1, hvec.2.1, hmat.2.2, hvec.2.2⟩
    have hguard : (k != p && k != q) = true := by simp [hrow.1, hrow.2]
    dsimp only [pairP, pairQ] at hPa hQa hPv hQv
    simp only [rotatePairRow, hguard, ↓reduceIte, hAp, hAq, hVp, hVq, finite,
      hPa, hQa, hPv, hQv, bind, Except.bind, pure, Except.pure, nextA, nextV, pairP, pairQ]
  · have hk' : k = p ∨ k = q := by omega
    refine ⟨(result.1, nextV), ?_, h.1, h.2.1, hvec.1, hvec.2.1, ?_, hvec.2.2⟩
    · have hguard : (k != p && k != q) = false := by simpa using hrow
      dsimp only [pairP, pairQ] at hPv hQv
      simp only [rotatePairRow, hguard, Bool.false_eq_true, ↓reduceIte, hVp, hVq,
        finite, hPv, hQv, bind, Except.bind, pure, Except.pure, nextV, pairP, pairQ]
    · intro i j hi hj
      rw [h.2.2.2.2.1 i j hi hj, matrixPairEntry_skip n p q k i j c s a hk']

private theorem pair_row_spec (n p q : Nat) (c s : Float) (a v : Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ k, k < n → k ≠ p → k ≠ q → |value (entry n a k p)| ≤ 32 ∧ |value (entry n a k q)| ≤ 32)
    (hvb : ∀ k, k < n → |value (entry n v k p)| ≤ 32 ∧ |value (entry n v k q)| ≤ 32)
    (k : Nat) (currentA currentV : Array Float)
    : ⦃⌜k < n ∧ PairState n p q c s a v k (currentA, currentV)⌝
      ⦄
        rotatePairRow n p q k c s currentA currentV
      ⦃⇓ result => ⌜PairState n p q c s a v (k + 1) result⌝⦄ := by
  intro ⟨hk, h⟩
  obtain ⟨next, he, hn⟩ := pair_row_progress n p q k c s a v (currentA, currentV)
    hp hq hk hpq hc hs hcb hsb ha hv hab hvb h
  simp only [he]
  exact hn

private theorem rotatePairs_triple (n p q : Nat) (c s : Float) (a v : Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (has : a.size = n * n) (hvs : v.size = n * n)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ k, k < n → k ≠ p → k ≠ q → |value (entry n a k p)| ≤ 32 ∧ |value (entry n a k q)| ≤ 32)
    (hvb : ∀ k, k < n → |value (entry n v k p)| ≤ 32 ∧ |value (entry n v k q)| ≤ 32)
    : ⦃⌜True⌝⦄ rotatePairs n p q c s a v ⦃⇓ result => ⌜PairState n p q c s a v n result⌝⦄ := by
  unfold rotatePairs
  have rowSpec (k : Nat) (currentA currentV : Array Float) :=
    (Specification.except_iff _ _ _).mp
      (pair_row_spec n p q c s a v hp hq hpq hc hs hcb hsb ha hv hab hvb k currentA currentV)
  apply (Specification.except_iff _ _ _).mpr
  vcgen [rowSpec]
    invariants
      | inv1 => fun xs _ ⟨currentA, currentV⟩ => PairState n p q c s a v xs.length (currentA,
        currentV)
  all_goals simp_all only [SPred.down_pure_nil]
  case vc1 =>
    refine ⟨has, by simpa only [has] using ha, hvs, by simpa only [hvs] using hv, ?_, ?_⟩
    · intro i j hi hj; simp [matrixPairEntry]
    · intro i j hi hj; simp [vectorPairEntry]
  case vc2 =>
    rename_i currentA currentV hstate
    simpa using hstate
  case vc3 =>
    rename_i pref k suff currentA currentV hk hstate
    have hk' := Flare.Matrix.Storage.forIn_range_current hk
    exact ⟨hk'.2, by simpa only [hk'.1] using hstate⟩
  case vc5 =>
    rename_i pref k suff currentA currentV nextA nextV hk hstate hnext
    have hk' := Flare.Matrix.Storage.forIn_range_current hk
    simpa only [List.length_append, List.length_singleton, ← hk'.1] using hnext

/-- The complete native pair-update loop succeeds on bounded finite operands.
Every returned entry is exactly the specified native expression on the original
row, including both symmetric copies; earlier writes never contaminate later
reads. The coefficient and operand bounds are explicit local loop premises. -/
theorem rotatePairs_correct (n p q : Nat) (c s : Float) (a v : Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (hc : c.isFinite = true) (hs : s.isFinite = true) (hcb : |value c| ≤ 2) (hsb : |value s| ≤ 2)
    (has : a.size = n * n) (hvs : v.size = n * n)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ k, k < n → k ≠ p → k ≠ q → |value (entry n a k p)| ≤ 32 ∧ |value (entry n a k q)| ≤ 32)
    (hvb : ∀ k, k < n → |value (entry n v k p)| ≤ 32 ∧ |value (entry n v k q)| ≤ 32)
    : ∃ result,
        rotatePairs n p q c s a v = .ok result
        ∧ result.1.size = n * n
        ∧ result.1.all Float.isFinite = true
        ∧ result.2.size = n * n
        ∧ result.2.all Float.isFinite = true
        ∧ (∀ i j, i < n → j < n → entry n result.1 i j = matrixPairEntry n p q c s a n i j)
        ∧ ∀ i j, i < n → j < n → entry n result.2 i j = vectorPairEntry n p q c s v n i j := by
  have h := rotatePairs_triple n p q c s a v hp hq hpq hc hs hcb hsb has hvs ha hv hab hvb
  cases he : rotatePairs n p q c s a v with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok result =>
      rw [he] at h; exact ⟨result, rfl, h True.intro⟩

/-- Native tangent expression for the selected pivot. Proof notation only. -/
def pivotT (n : Nat) (a : Array Float) (p q : Nat) : Float :=
  let τ := (entry n a q q - entry n a p p) / (2.0 * entry n a p q)
  (if τ < 0.0 then -1.0 else 1.0) / (τ.abs + (1.0 + τ * τ).sqrt)

/-- Native cosine expression for the selected pivot. Proof notation only. -/
def pivotC (n : Nat) (a : Array Float) (p q : Nat) : Float :=
  let t := pivotT n a p q
  1.0 / (1.0 + t * t).sqrt

/-- Native sine expression for the selected pivot. Proof notation only. -/
def pivotS (n : Nat) (a : Array Float) (p q : Nat) : Float :=
  pivotT n a p q * pivotC n a p q

/-- The four pivot-block writes performed before the pair-update loop. -/
def pivotHeader (n : Nat) (a : Array Float) (p q : Nat) : Array Float :=
  let t := pivotT n a p q
  (((a.set! (p * n + p) (entry n a p p - t * entry n a p q)).set!
      (q * n + q) (entry n a q q + t * entry n a p q)).set!
    (p * n + q) 0.0).set!
    (q * n + p) 0.0

/-- Both native diagonal writes are finite and differ from their real formulas
by at most `2⁻⁴³` on the local normalized-entry profile. -/
theorem diagonal_updates (a b d t : Float)
    (ha : a.isFinite = true) (hb : b.isFinite = true) (hd : d.isFinite = true)
    (ht : t.isFinite = true) (hab : |value a| ≤ 32) (hbb : |value b| ≤ 32)
    (hdb : |value d| ≤ 32) (htb : |value t| ≤ 2)
    : (a - t * b).isFinite = true
      ∧ (d + t * b).isFinite = true
      ∧ |value (a - t * b) - (value a - value t * value b)| ≤ (2 : ℝ) ^ (-43 : Int)
      ∧ |value (d + t * b) - (value d + value t * value b)| ≤ (2 : ℝ) ^ (-43 : Int) := by
  have hprod : |value t * value b| ≤ 64 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (value b), abs_nonneg (value t)]
  obtain ⟨hpf, hpe⟩ := mul_error t b 6 ht hb (by norm_num) (by norm_num) (by
    convert hprod using 1; norm_num)
  have hpb : |value (t * b)| ≤ 65 := by
    have h := abs_sub_le (value (t * b)) (value t * value b) 0
    simp only [sub_zero] at h
    norm_num at hpe
    linarith
  obtain ⟨haf, hae⟩ := sub_error a (t * b) 7 ha hpf (by norm_num) (by norm_num) (by
    have h := abs_sub (value a) (value (t * b)); norm_num; linarith)
  obtain ⟨hdf, hde⟩ := add_error d (t * b) 7 hd hpf (by norm_num) (by norm_num) (by
    have h := abs_add_le (value d) (value (t * b)); norm_num; linarith)
  refine ⟨haf, hdf, ?_, ?_⟩
  · have he : value (a - t * b) - (value a - value t * value b) =
        (value (a - t * b) - (value a - value (t * b))) -
          (value (t * b) - value t * value b) := by ring
    rw [he]
    have htri := abs_sub (value (a - t * b) - (value a - value (t * b)))
      (value (t * b) - value t * value b)
    norm_num at hpe hae ⊢
    linarith
  · have he : value (d + t * b) - (value d + value t * value b) =
        (value (d + t * b) - (value d + value (t * b))) +
          (value (t * b) - value t * value b) := by ring
    rw [he]
    have htri := abs_add_le (value (d + t * b) - (value d + value (t * b)))
      (value (t * b) - value t * value b)
    norm_num at hpe hde ⊢
    linarith

/-- Pointwise meaning of the initial pivot-block writes, including exact zeroes. -/
theorem pivotHeader_entry (n p q i j : Nat) (a : Array Float)
    (ha : a.size = n * n) (hp : p < n) (hq : q < n) (hj : j < n) (hpq : p ≠ q)
    : entry n (pivotHeader n a p q) i j
      = if i = p ∧ j = p then
          entry n a p p - pivotT n a p q * entry n a p q
        else if i = q ∧ j = q then
          entry n a q q + pivotT n a p q * entry n a p q
        else if i = p ∧ j = q ∨ i = q ∧ j = p then
          0.0
        else
          entry n a i j := by
  unfold pivotHeader Flare.Matrix.Operations.entry
  rw [Flare.Matrix.Storage.entry_set n _ q p i j _ (by simpa using ha) hq hp hj,
    Flare.Matrix.Storage.entry_set n _ p q i j _ (by simpa using ha) hp hq hj,
    Flare.Matrix.Storage.entry_set n _ q q i j _ (by simpa using ha) hq hq hj,
    Flare.Matrix.Storage.entry_set n _ p p i j _ ha hp hp hj]
  split_ifs <;> first | rfl | omega

private lemma pivotHeader_finite (n p q : Nat) (a : Array Float)
    (ha : a.all Float.isFinite = true)
    (hP : (entry n a p p - pivotT n a p q * entry n a p q).isFinite = true)
    (hQ : (entry n a q q + pivotT n a p q * entry n a p q).isFinite = true)
    : (pivotHeader n a p q).all Float.isFinite = true :=
  Flare.Matrix.Storage.all_set _ _ _
    (Flare.Matrix.Storage.all_set _ _ _
      (Flare.Matrix.Storage.all_set _ _ _ (Flare.Matrix.Storage.all_set _ _ _ ha hP) hQ)
      (by decide)) (by decide)

/-- One complete native rotation succeeds from bounded matrix/vector entries
and a pivot above the stopping threshold. Its scalar guards, pivot-block writes,
pair loop, finite storage and entrywise execution equations are all conclusions. -/
theorem rotate_correct (n p q : Nat) (a v : Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (has : a.size = n * n) (hvs : v.size = n * n)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hvb : ∀ i j, i < n → j < n → |value (entry n v i j)| ≤ 32)
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    : let c := pivotC n a p q
      let s := pivotS n a p q
      ∃ result,
        rotate n a v p q = .ok result
        ∧ c.isFinite = true
        ∧ s.isFinite = true
        ∧ |value c| ≤ 2
        ∧ |value s| ≤ 2
        ∧ |(value c) ^ 2 + (value s) ^ 2 - 1| ≤ (2 : ℝ) ^ (-43 : Int)
        ∧ result.1.size = n * n
        ∧ result.1.all Float.isFinite = true
        ∧ result.2.size = n * n
        ∧ result.2.all Float.isFinite = true
        ∧ (∀ i j,
            i < n
            → j < n
            → entry n result.1 i j = matrixPairEntry n p q c s (pivotHeader n a p q) n i j)
        ∧ ∀ i j, i < n → j < n → entry n result.2 i j = vectorPairEntry n p q c s v n i j := by
  have hparams := Jacobi.pivot_rotation_parameters (entry n a p p) (entry n a p q) (entry n a q q)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (hab p p hp hp) (hab p q hp hq) (hab q q hq hq) hstop
  change _ ∧ (pivotT n a p q).isFinite = true ∧ (pivotC n a p q).isFinite = true ∧
    (pivotS n a p q).isFinite = true ∧ |value (pivotT n a p q)| ≤ 2 ∧
    |value (pivotC n a p q)| ≤ 2 ∧ |value (pivotS n a p q)| ≤ 2 ∧ _ at hparams
  rcases hparams with ⟨hτ, ht, hc, hs, htb, hcb, hsb, hunit⟩
  have hd := diagonal_updates (entry n a p p) (entry n a p q) (entry n a q q) (pivotT n a p q)
    (Flare.Matrix.Storage.getD_finite _ _ ha) (Flare.Matrix.Storage.getD_finite _ _ ha)
    (Flare.Matrix.Storage.getD_finite _ _ ha) ht (hab p p hp hp) (hab p q hp hq) (hab q q hq hq) htb
  have hheader : ∀ k, k < n → k ≠ p → k ≠ q →
      |value (entry n (pivotHeader n a p q) k p)| ≤ 32 ∧
      |value (entry n (pivotHeader n a p q) k q)| ≤ 32 := by
    intro k hk hkp hkq
    rw [pivotHeader_entry n p q k p a has hp hq hp hpq,
      pivotHeader_entry n p q k q a has hp hq hq hpq]
    simpa [hkp, hkq] using And.intro (hab k p hk hp) (hab k q hk hq)
  obtain ⟨result, he, hresult⟩ := rotatePairs_correct n p q (pivotC n a p q) (pivotS n a p q)
    (pivotHeader n a p q) v hp hq hpq hc hs hcb hsb (by simpa [pivotHeader] using has) hvs
    (pivotHeader_finite n p q a ha hd.1 hd.2.1) hv hheader
    (fun k hk => ⟨hvb k p hk hp, hvb k q hk hq⟩)
  refine ⟨result, ?_, hc, hs, hcb, hsb, hunit, hresult⟩
  have hdP := hd.1
  have hdQ := hd.2.1
  simp only [pivotT, pivotC, pivotS] at ht hc hs hdP hdQ he
  simp only [rotate, finite, hτ, ht, hc, hs, hdP, hdQ, ↓reduceIte, bind, Except.bind]
  exact he

/-- Entrywise facts about a complete rotation, retained for the iteration proof.
All expressions refer to the input arrays; no intermediate native result is
assumed to satisfy these equations. This is proof-side bookkeeping. -/
structure RotationResult (n p q : Nat) (a v : Array Float) (result : Array Float × Array Float)
    : Prop where
  matrix_size : result.1.size = n * n
  matrix_finite : result.1.all Float.isFinite = true
  vectors_size : result.2.size = n * n
  vectors_finite : result.2.all Float.isFinite = true
  cosine_finite : (pivotC n a p q).isFinite = true
  sine_finite : (pivotS n a p q).isFinite = true
  cosine_bound : |value (pivotC n a p q)| ≤ 2
  sine_bound : |value (pivotS n a p q)| ≤ 2
  unit_error
    : |(value (pivotC n a p q)) ^ 2 + (value (pivotS n a p q)) ^ 2 - 1| ≤ (2 : ℝ) ^ (-43 : Int)
  pivot_zero : entry n result.1 p q = 0.0 ∧ entry n result.1 q p = 0.0
  diagonal_p : entry n result.1 p p = entry n a p p - pivotT n a p q * entry n a p q
  diagonal_q : entry n result.1 q q = entry n a q q + pivotT n a p q * entry n a p q
  matrix_pair
    : ∀ k,
        k < n
        → k ≠ p
        → k ≠ q
        → entry n result.1 k p = pairP n p q (pivotC n a p q) (pivotS n a p q) a k
          ∧ entry n result.1 p k = pairP n p q (pivotC n a p q) (pivotS n a p q) a k
          ∧ entry n result.1 k q = pairQ n p q (pivotC n a p q) (pivotS n a p q) a k
          ∧ entry n result.1 q k = pairQ n p q (pivotC n a p q) (pivotS n a p q) a k
  matrix_unchanged
    : ∀ i j, i < n → j < n → i ≠ p → i ≠ q → j ≠ p → j ≠ q → entry n result.1 i j = entry n a i j
  vectors_pair
    : ∀ k,
        k < n
        → entry n result.2 k p = pairP n p q (pivotC n a p q) (pivotS n a p q) v k
          ∧ entry n result.2 k q = pairQ n p q (pivotC n a p q) (pivotS n a p q) v k
  vectors_unchanged : ∀ i j, i < n → j < n → j ≠ p → j ≠ q → entry n result.2 i j = entry n v i j

/-- Success and explicit entry equations for an entire native rotation. -/
theorem rotate_step (n p q : Nat) (a v : Array Float)
    (hp : p < n) (hq : q < n) (hpq : p ≠ q)
    (has : a.size = n * n) (hvs : v.size = n * n)
    (ha : a.all Float.isFinite = true) (hv : v.all Float.isFinite = true)
    (hab : ∀ i j, i < n → j < n → |value (entry n a i j)| ≤ 32)
    (hvb : ∀ i j, i < n → j < n → |value (entry n v i j)| ≤ 32)
    (hstop : (1.0e-14 : Float) < (entry n a p q).abs)
    : ∃ result, rotate n a v p q = .ok result ∧ RotationResult n p q a v result := by
  obtain ⟨result, he, hc, hs, hcb, hsb, hunit, hAs, hAf, hVs, hVf, hA, hV⟩ :=
    rotate_correct n p q a v hp hq hpq has hvs ha hv hab hvb hstop
  refine ⟨result, he, hAs, hAf, hVs, hVf, hc, hs, hcb, hsb, hunit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA p q hp hq, hA q p hq hp]
    simp [matrixPairEntry, pivotHeader_entry, has, hp, hq, hpq, Ne.symm hpq]
  · rw [hA p p hp hp]
    simp [matrixPairEntry, pivotHeader_entry, has, hp, hq, hpq]
  · rw [hA q q hq hq]
    simp [matrixPairEntry, pivotHeader_entry, has, hp, hq, hpq, Ne.symm hpq]
  · intro k hk hkp hkq
    rw [hA k p hk hp, hA p k hp hk, hA k q hk hq, hA q k hq hk]
    simp [matrixPairEntry, pairP, pairQ, pivotHeader_entry, has, hp, hq, hk,
      hpq, Ne.symm hpq, hkp, hkq]
  · intro i j hi hj hip hiq hjp hjq
    rw [hA i j hi hj]
    simp [matrixPairEntry, pivotHeader_entry, has, hp, hq, hj, hpq, hip, hiq, hjp, hjq]
  · intro k hk
    rw [hV k p hk hp, hV k q hk hq]
    simp [vectorPairEntry, hk, Ne.symm hpq]
  · intro i j hi hj hjp hjq
    rw [hV i j hi hj]
    simp [vectorPairEntry, hjp, hjq]

/-- Native rotation preserves real symmetry, including inputs whose equal real
zeroes use different signed-zero encodings. -/
theorem RotationResult.symmetric (n p q : Nat) (a v : Array Float)
    (result : Array Float × Array Float) (h : RotationResult n p q a v result)
    (ha : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    : ∀ i j, i < n → j < n → value (entry n result.1 i j) = value (entry n result.1 j i) := by
  intro i j hi hj
  by_cases hij : i = j
  · subst j; rfl
  by_cases hip : i = p
  · subst i
    by_cases hjq : j = q
    · subst j; rw [h.pivot_zero.1, h.pivot_zero.2]
    · rw [(h.matrix_pair j hj (Ne.symm hij) hjq).2.1, (h.matrix_pair j hj (Ne.symm hij) hjq).1]
  by_cases hiq : i = q
  · subst i
    by_cases hjp : j = p
    · subst j; rw [h.pivot_zero.1, h.pivot_zero.2]
    · rw [(h.matrix_pair j hj hjp (Ne.symm hij)).2.2.2, (h.matrix_pair j hj hjp (Ne.symm
      hij)).2.2.1]
  by_cases hjp : j = p
  · subst j; rw [(h.matrix_pair i hi hip hiq).1, (h.matrix_pair i hi hip hiq).2.1]
  by_cases hjq : j = q
  · subst j; rw [(h.matrix_pair i hi hip hiq).2.2.1, (h.matrix_pair i hi hip hiq).2.2.2]
  rw [h.matrix_unchanged i j hi hj hip hiq hjp hjq, h.matrix_unchanged j i hj hi hjp hjq hip hiq]
  exact ha i j hi hj

end Flare.Matrix.JacobiIteration
