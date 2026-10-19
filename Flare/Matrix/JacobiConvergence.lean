import Flare.Matrix.JacobiBounds

/-! A proof-side native trajectory for the bounded Jacobi loop. Its transition
uses the actual pivot scan and rotation; total fallbacks are shown unreachable
under the energy invariant. -/

namespace Flare.Matrix.JacobiConvergence

open Flare.Matrix.Value Flare.Binary64.Value Flare.Matrix.Operations
open Flare.Matrix.JacobiIteration Flare.Matrix.JacobiEnergy Flare.Matrix.JacobiBounds
open Flare.Binary64.Arithmetic Flare.Binary64.Order
open Flare.Analysis.JacobiEnergy
open Std.Do

set_option mvcgen.warning false
-- Retain the established VC engine while using Lean 4.35.
set_option linter.deprecated.syntax false

/-- Total proof-side projection of the native scan. -/
def selectedPivot (n : Nat) (a : Array Float) : Pivot :=
  match largestPivot n a with
  | .ok pivot => pivot
  | .error _ => ⟨0.0, 0, 0⟩

/-- Total proof-side transition. After a stopping result the trajectory stays
constant. Error fallbacks are excluded by the invariant preservation theorem. -/
def advance (n : Nat) (a v : Array Float) : Array Float × Array Float :=
  let pivot := selectedPivot n a
  if pivot.magnitude ≤ (1.0e-14 : Float) then
    (a, v)
  else
    match rotate n a v pivot.row pivot.column with
    | .ok result => result
    | .error _ => (a, v)

/-- Native scan/rotation trajectory, used only to reason about loop prefixes. -/
def trajectory (n : Nat) (a v : Array Float) : Nat → Array Float × Array Float
  | 0 => (a, v)
  | k + 1 =>
      let prev := trajectory n a v k;
      advance n prev.1 prev.2

/-- The native stopping branch's final eigenvalue rescaling. -/
def finish (n : Nat) (magnitude : Float) (a v : Array Float)
    : Except Flare.Matrix.Error Spectrum := do
  let values ← (Array.range n).mapM fun i => finite (entry n a i i * magnitude)
  return ⟨values, v⟩

/-- Extract the exact bounded outer loop, including its early return and cap. -/
def iterations (n : Nat) (magnitude : Float) (initialA initialV : Array Float)
    : Except Flare.Matrix.Error Spectrum := do
  let mut a := initialA
  let mut v := initialV
  for step in [:32 * n * n + 1] do
    let pivot ← largestPivot n a
    if pivot.magnitude ≤ 1.0e-14 then
      return ← finish n magnitude a v
    if step == 32 * n * n then
      throw .eigenNotConverged
    let result ← rotate n a v pivot.row pivot.column
    a := result.1
    v := result.2
  throw .eigenNotConverged

/-- The extracted bounded loop and rescaling branch execute the native
eigensolver after its normalization and zero-input branch. -/
theorem jacobiBySteps_eq (n : Nat) (input : Array Float)
    : jacobiBySteps n input
      = (do
          let magnitude := maxAbs input
          if magnitude == 0.0 then
            return ⟨Array.replicate n 0.0, identity n⟩
          let a ← input.mapM fun x => finite (x / magnitude)
          iterations n magnitude a (identity n)) := by
  unfold jacobiBySteps iterations finish
  simp only [bind_assoc, pure_bind]

/-- Storage guarantees for a returned native spectrum. Proof-side bookkeeping. -/
structure Stored (n : Nat) (result : Spectrum) : Prop where
  values_size : result.values.size = n
  values_finite : result.values.all Float.isFinite = true
  vectors_size : result.vectors.size = n * n
  vectors_finite : result.vectors.all Float.isFinite = true

/-- Finalization returns the native rescaled diagonal and the stored
eigenvectors, with no reordering or additional numerical transformation. -/
theorem finish_entries (n : Nat) (magnitude : Float) (a v : Array Float)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ) ^ (500 : Int))
    (ha : a.all Float.isFinite = true) (hE : energy (matrix n n a) ≤ 1024)
    (hvs : v.size = n * n) (hv : v.all Float.isFinite = true)
    : ∃ result,
        finish n magnitude a v = .ok result
        ∧ Stored n result
        ∧ result.vectors = v
        ∧ ∀ i, i < n → result.values.getD i 0.0 = entry n a i i * magnitude := by
  have hb := entries_of_energy n a hE
  have hterm (i : Nat) (hi : i < n) : (entry n a i i * magnitude).isFinite = true := by
    apply (mul_error (entry n a i i) magnitude 505 (Flare.Matrix.Storage.getD_finite _ _ ha)
            hm (by norm_num) (by norm_num) ?_).1
    rw [abs_mul]
    calc
      _ ≤ 32 * (2 : ℝ) ^ (500 : Int) := mul_le_mul (hb i i hi hi) hmb (abs_nonneg _) (by norm_num)
      _ = _ := by rw [show (505 : Int) = 5 + 500 by norm_num, zpow_add₀ (by norm_num)]; norm_num
  have hmap : (Array.range n).mapM (fun i => finite (entry n a i i * magnitude)) =
      .ok ((Array.range n).map (fun i => entry n a i i * magnitude)) := by
    apply Flare.Matrix.Multiplication.mapM_eq_ok_map
    intro i hi
    have hi' : i < n := by simpa using hi
    simp only [finite, hterm i hi', ↓reduceIte]
  refine ⟨
    ⟨(Array.range n).map (fun i => entry n a i i * magnitude), v⟩,
    ?_,
    ⟨by simp, ?_, hvs, hv⟩,
    rfl,
    ?_
  ⟩
  · simp only [finish, hmap, bind, Except.bind, pure, Except.pure]
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < n := by simpa using hi
    simpa [hi'] using hterm i hi'
  · intro i hi
    simp [hi]

/-- The actual stopping branch rescales without overflow on a bounded input
scale and the proved local energy profile. -/
theorem finish_correct (n : Nat) (magnitude : Float) (a v : Array Float)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ) ^ (500 : Int))
    (ha : a.all Float.isFinite = true) (hE : energy (matrix n n a) ≤ 1024)
    (hvs : v.size = n * n) (hv : v.all Float.isFinite = true)
    : ∃ result, finish n magnitude a v = .ok result ∧ Stored n result := by
  obtain ⟨result, he, hstored, _⟩ := finish_entries n magnitude a v hm hmb ha hE hvs hv
  exact ⟨result, he, hstored⟩

/-- The scan fallback is unreachable for finite arrays, and the selected
magnitude controls the complete off-diagonal energy of a symmetric matrix. -/
theorem selectedPivot_correct (n : Nat) (a : Array Float) (ha : a.all Float.isFinite = true)
    (hsym : ∀ i j, i < n → j < n → value (entry n a i j) = value (entry n a j i))
    : let pivot := selectedPivot n a
      largestPivot n a = .ok pivot
      ∧ pivot.magnitude.isFinite = true
      ∧ 0 ≤ value pivot.magnitude
      ∧ (pivot.magnitude = 0.0
          ∨ pivot.row < pivot.column
            ∧ pivot.column < n
            ∧ pivot.magnitude = (entry n a pivot.row pivot.column).abs)
      ∧ offEnergy (matrix n n a) ≤ (n : ℝ) * (n - 1) * (value pivot.magnitude) ^ 2 := by
  obtain ⟨pivot, he, h⟩ := largestPivot_energy n a ha hsym
  simpa only [selectedPivot, he] using And.intro he h

/-- A non-stopping maximum selects an in-range, nonzero pivot above the actual
native threshold. This excludes the scan's zero-initialized indices. -/
theorem selectedPivot_ready (n : Nat) (a : Array Float) (pivot : Pivot)
    (hf : pivot.magnitude.isFinite = true)
    (hselected
      : pivot.magnitude = 0.0
        ∨ pivot.row < pivot.column
          ∧ pivot.column < n
          ∧ pivot.magnitude = (entry n a pivot.row pivot.column).abs)
    (hstop : ¬pivot.magnitude ≤ (1.0e-14 : Float))
    : pivot.row < pivot.column
      ∧ pivot.column < n
      ∧ pivot.magnitude = (entry n a pivot.row pivot.column).abs
      ∧ (1.0e-14 : Float) < (entry n a pivot.row pivot.column).abs := by
  have hlt : (1.0e-14 : Float) < pivot.magnitude := by
    apply (lt_iff _ _ (by decide) hf).mpr
    exact lt_of_not_ge (fun hle => hstop ((le_iff _ _ hf (by decide)).mpr hle))
  rcases hselected with hzero | ⟨hpq, hq, hpivot⟩
  · have ht := (lt_iff _ _ (by decide) hf).mp hlt
    rw [hzero, zero_value] at ht
    have hpos := Jacobi.stopping_threshold_bounds.1
    have hε : 0 < (2 : ℝ)^(-47 : Int) := by positivity
    linarith
  · exact ⟨hpq, hq, hpivot, by simpa only [hpivot] using hlt⟩

private theorem state_mono (n k l : Nat) (a v : Array Float) (hkl : k ≤ l) (h : State n k a v)
    : State n l a v := by
  have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ l by exact_mod_cast hkl)
    (show 0 ≤ (2 : ℝ)^(-20 : Int) by positivity)
  refine {
    h with
      matrix_energy := h.matrix_energy.trans ?_, vectors_energy := h.vectors_energy.trans ?_
  }
  · exact add_le_add le_rfl hmul
  · exact add_le_add le_rfl hmul

/-- The total trajectory transition preserves the invariant, and when it
continues, its actual rotation satisfies the off-diagonal energy recurrence. -/
theorem advance_correct (n k : Nat) (a v : Array Float) (hn : n ≤ 18)
    (hk : k ≤ 32 * n * n) (h : State n k a v)
    : State n (k + 1) (advance n a v).1 (advance n a v).2
      ∧ (¬(selectedPivot n a).magnitude ≤ (1.0e-14 : Float)
          → rotate n a v (selectedPivot n a).row (selectedPivot n a).column = .ok (advance n a v)
            ∧ offEnergy (matrix n n (advance n a v).1)
              ≤ (1 + (2 : ℝ) ^ (-36 : Int)) * offEnergy (matrix n n a)
                - 2 * (value (selectedPivot n a).magnitude) ^ 2) := by
  have hs := selectedPivot_correct n a h.matrix_finite h.symmetric
  by_cases hstop : (selectedPivot n a).magnitude ≤ (1.0e-14 : Float)
  · simp only [advance, hstop, ↓reduceIte]
    exact ⟨state_mono n k (k + 1) a v (by omega) h, fun hn => (hn True.intro).elim⟩
  obtain ⟨hpq, hq, hpivot, hlt⟩ := selectedPivot_ready n a (selectedPivot n a) hs.2.1 hs.2.2.2.1
    hstop
  obtain ⟨result, he, hstate, henergy⟩ := state_rotate n k (selectedPivot n a).row (selectedPivot n
    a).column
    a v hn hk (hpq.trans hq) hq (Nat.ne_of_lt hpq) h hlt
  have habs := (abs_value (entry n a (selectedPivot n a).row (selectedPivot n a).column)
    (Flare.Matrix.Storage.getD_finite _ _ h.matrix_finite)).2
  have hstep : advance n a v = result := by simp only [advance, hstop, ↓reduceIte, he]
  rw [hstep]
  refine ⟨hstate, fun _ => ⟨he, ?_⟩⟩
  rw [hpivot, habs, sq_abs]
  exact henergy

/-- Every prefix in the runtime rotation allowance retains finite storage,
symmetry and bounded matrix/vector energy. -/
theorem trajectory_state (n : Nat) (a v : Array Float) (hn : n ≤ 18) (h : State n 0 a v)
    (k : Nat) (hk : k ≤ 32 * n * n)
    : State n k (trajectory n a v k).1 (trajectory n a v k).2 := by
  induction k with
  | zero => exact h
  | succ k ih =>
      have hprev := ih (by omega)
      exact (advance_correct n k _ _ hn (by omega) hprev).1

/-- The actual native scan/rotation trajectory reaches its stopping test within
the runtime allowance. Its initial energy bounds are the normalization goals;
no intermediate finiteness, magnitude, energy-step or success premise is assumed. -/
theorem trajectory_stops (n : Nat) (a v : Array Float) (hn : 2 ≤ n) (hn' : n ≤ 18)
    (h : State n 0 a v)
    (hstart : offEnergy (matrix n n a) ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    : ∃ k,
        k < 32 * n * n
        ∧ (selectedPivot n (trajectory n a v k).1).magnitude ≤ (1.0e-14 : Float) := by
  by_contra hnone
  have hrun : ∀ k, k < 32 * n * n →
      ¬(selectedPivot n (trajectory n a v k).1).magnitude ≤ (1.0e-14 : Float) := by
    intro k hk hstop
    exact hnone ⟨k, hk, hstop⟩
  let E := fun k => offEnergy (matrix n n (trajectory n a v k).1)
  let P := fun k => value (selectedPivot n (trajectory n a v k).1).magnitude
  have hmax (k : Nat) (hk : k < 32 * n * n) : E k ≤ (n * (n - 1) : Nat) * (P k)^2 := by
    have hstate := trajectory_state n a v hn' h k hk.le
    have hscan := selectedPivot_correct n _ hstate.matrix_finite hstate.symmetric
    simpa only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_one] using hscan.2.2.2.2
  have hstep (k : Nat) (hk : k < 32 * n * n) (_ : (99 / 10000000000000000 : ℝ) < P k) :
      E (k + 1) ≤ (1 + (2 : ℝ)^(-36 : Int)) * E k - 2 * (P k)^2 := by
    have hstate := trajectory_state n a v hn' h k hk.le
    exact ((advance_correct n k _ _ hn' hk.le hstate).2 (hrun k hk)).2
  obtain ⟨k, hk, hsmall⟩ := Flare.Analysis.Jacobi.energy_convergence n E P hn hn'
    (fun k _ => offEnergy_nonneg _) hstart hmax hstep
  have hstate := trajectory_state n a v hn' h k hk.le
  have hscan := selectedPivot_correct n _ hstate.matrix_finite hstate.symmetric
  exact hrun k hk
    ((le_iff _ _ hscan.2.1 (by decide)).mpr (hsmall.trans Jacobi.stopping_threshold_bounds.2))

@[spec]
private theorem largestPivot_spec (n : Nat) (a : Array Float)
    : ⦃⌜a.all Float.isFinite = true⌝
      ⦄ largestPivot n a
      ⦃⇓ pivot => ⌜pivot = selectedPivot n a⌝⦄ := by
  intro ha
  obtain ⟨pivot, he, _⟩ := largestPivot_correct n a ha
  simp only [he, selectedPivot]
  rfl

@[spec]
private theorem finish_spec (n : Nat) (magnitude : Float) (a v : Array Float)
    : ⦃
        ⌜
          magnitude.isFinite = true
          ∧ |value magnitude| ≤ (2 : ℝ) ^ (500 : Int)
          ∧ a.all Float.isFinite = true
          ∧ energy (matrix n n a) ≤ 1024
          ∧ v.size = n * n
          ∧ v.all Float.isFinite = true
          ⌝
      ⦄ finish n magnitude a v
      ⦃⇓ result => ⌜Stored n result ∧ finish n magnitude a v = .ok result⌝⦄ := by
  intro ⟨hm, hmb, ha, hE, hvs, hv⟩
  obtain ⟨result, he, hstored⟩ := finish_correct n magnitude a v hm hmb ha hE hvs hv
  simp only [he]
  exact ⟨hstored, rfl⟩

@[spec]
private theorem rotate_spec (n : Nat) (a v : Array Float) (p q : Nat)
    : ⦃
        ⌜
          n ≤ 18
          ∧ ∃ k,
              k ≤ 32 * n * n
              ∧ State n k a v
              ∧ p = (selectedPivot n a).row
              ∧ q = (selectedPivot n a).column
              ∧ ¬(selectedPivot n a).magnitude ≤ (1.0e-14 : Float)
          ⌝
      ⦄ rotate n a v p q
      ⦃⇓ result => ⌜result = advance n a v⌝⦄ := by
  intro hpre
  rcases hpre with ⟨hn, k, hk, hstate, hp, hq, hstop⟩
  subst p q
  have h := ((advance_correct n k a v hn hk hstate).2 hstop).1
  simp only [h]
  rfl

private def LoopInvariant (n : Nat) (a v : Array Float) (stop k : Nat) (post : Spectrum → Prop)
    (state : Option Spectrum × Array Float × Array Float)
    : Prop :=
  if k < 32 * n * n + 1 then
    state.1 = none
    ∧ state.2.1 = (trajectory n a v k).1
    ∧ state.2.2 = (trajectory n a v k).2
    ∧ k ≤ stop
  else
    ∃ result, state.1 = some result ∧ post result

private theorem iterations_triple (n : Nat) (magnitude : Float) (a v : Array Float)
    (hn : n ≤ 18) (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ) ^ (500 : Int))
    (hstate : State n 0 a v) (stop : Nat) (hstop : stop < 32 * n * n)
    (hstopAt : (selectedPivot n (trajectory n a v stop).1).magnitude ≤ (1.0e-14 : Float))
    (post : Spectrum → Prop)
    (hpost
      : ∀ k,
          k ≤ stop
          → (selectedPivot n (trajectory n a v k).1).magnitude ≤ (1.0e-14 : Float)
          → ∀ result,
              finish n magnitude (trajectory n a v k).1 (trajectory n a v k).2 = .ok result
              → Stored n result
              → post result)
    : ⦃⌜True⌝⦄ iterations n magnitude a v ⦃⇓ result => ⌜post result⌝⦄ := by
  have active (pref : List Nat) (cur : Nat) (suff : List Nat)
      (hcur : [:32 * n * n + 1].toList = pref ++ cur :: suff)
      (b : Option Spectrum × Array Float × Array Float) (hb : LoopInvariant n a v stop pref.length
        post b) :
      State n pref.length b.2.1 b.2.2 ∧ b.2.1 = (trajectory n a v pref.length).1 ∧
        b.2.2 = (trajectory n a v pref.length).2 ∧ pref.length ≤ stop := by
    have hc := Flare.Matrix.Storage.range_current hcur
    have hpref : pref.length < 32 * n * n + 1 := by omega
    rw [LoopInvariant, ite_eq_left hpref] at hb
    refine ⟨?_, hb.2⟩
    rw [hb.2.1, hb.2.2.1]
    exact trajectory_state n a v hn hstate pref.length (by omega)
  unfold iterations
  -- Specialize the unused monad/universe parameters in Lean's Except spec.
  have throwSpec {α : Type} (e : Flare.Matrix.Error) (Q : PostCond α (.except Flare.Matrix.Error
    .pure)) :
      Triple (ps := .except Flare.Matrix.Error .pure) (MonadExceptOf.throw e : Except
        Flare.Matrix.Error α) (spred(Q.2.1 e)) Q :=
    Spec.throw_Except.{0, 0, 0} (m := Id) (ps := .pure)
  mvcgen [-Spec.throw_Except, throwSpec]
    invariants
      | inv1 => ⇓ ⟨xs, state⟩ => ⌜LoopInvariant n a v stop xs.prefix.length post state⌝
    with
      | vc1 =>
        rename_i pref cur suff hcur b pair currentA currentV hinv
        exact (active pref cur suff hcur b hinv).1.matrix_finite
      | vc2 =>
        rename_i pref cur suff hcur b pair currentA currentV hinv pivot htest hpivot
        have hactive := active pref cur suff hcur b hinv
        have he := state_energy_bound n pref.length currentA currentV hn (by omega) hactive.1
        exact ⟨
          hm,
          hmb,
          hactive.1.matrix_finite,
          he.1,
          hactive.1.vectors_size,
          hactive.1.vectors_finite
        ⟩
      | vc3 =>
        rename_i pref cur suff hcur b pair currentA currentV hinv pivot htest hpivot result hstored
        have hactive := active pref cur suff hcur b hinv
        have hAeq : currentA = (trajectory n a v pref.length).1 := hactive.2.1
        have hVeq : currentV = (trajectory n a v pref.length).2 := hactive.2.2.1
        have hstopped : (selectedPivot n (trajectory n a v pref.length).1).magnitude ≤ (1.0e-14 :
          Float) := by
          rw [hpivot, hAeq] at htest
          exact htest
        have hfinished := hstored.2
        change finish n magnitude currentA currentV = .ok result at hfinished
        rw [hAeq, hVeq] at hfinished
        have hresult := hpost pref.length hactive.2.2.2 hstopped result hfinished hstored.1
        simpa [LoopInvariant, Std.Legacy.Range.toList] using hresult
      | vc4 =>
        rename_i pref cur suff hcur b pair currentA currentV hinv pivot htest jp hcap hpivot
        have hactive := active pref cur suff hcur b hinv
        have hc := Flare.Matrix.Storage.range_current hcur
        have he : cur = 32 * n * n := by simpa using hcap
        have hlen := hactive.2.2.2
        exact False.elim (by omega)
      | vc5 =>
        rename_i pref cur suff hcur b pair currentA currentV hinv pivot htest jp hcap hpivot
        have hactive := active pref cur suff hcur b hinv
        have hlen := hactive.2.2.2
        refine ⟨hn, pref.length, by omega, hactive.1, ?_, ?_, ?_⟩
        · exact congrArg Pivot.row hpivot
        · exact congrArg Pivot.column hpivot
        · simpa only [hpivot] using htest
      | vc6 =>
        rename_i pref cur suff hcur b pair currentA currentV hinv pivot htest jp hcap hpivot result
          hresult
        have hactive := active pref cur suff hcur b hinv
        have hlen := hactive.2.2.2
        have hlt : pref.length < stop := by
          by_contra hnot
          have heq : pref.length = stop := by omega
          have hpa : currentA = (trajectory n a v stop).1 := by simpa only [heq] using hactive.2.1
          apply htest
          rw [hpivot, hpa]
          exact hstopAt
        have hnext : (pref ++ [cur]).length < 32 * n * n + 1 := by
          simp only [List.length_append, List.length_singleton]; omega
        rw [LoopInvariant, ite_eq_left hnext]
        refine ⟨rfl, ?_, ?_, by simp only [List.length_append, List.length_singleton]; omega⟩
        · change result.1 = _
          rw [hresult]
          change (advance n b.2.1 b.2.2).1 = _
          rw [hactive.2.1, hactive.2.2.1]
          simp only [List.length_append, List.length_singleton, trajectory]
        · change result.2 = _
          rw [hresult]
          change (advance n b.2.1 b.2.2).2 = _
          rw [hactive.2.1, hactive.2.2.1]
          simp only [List.length_append, List.length_singleton, trajectory] | vc7
                                                                              => simp [
                                                                                    LoopInvariant,
                                                                                    trajectory
                                                                                  ]
      | vc8 =>
        rename_i result output houtput hinv
        simpa [LoopInvariant, Std.Legacy.Range.toList, houtput] using hinv
      | vc9 =>
        rename_i result houtput hinv
        simp [LoopInvariant, Std.Legacy.Range.toList, houtput] at hinv

private theorem stopping_index (n : Nat) (a v : Array Float)
    (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hstate : State n 0 a v)
    (hstart : offEnergy (matrix n n a) ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    : ∃ k,
        k < 32 * n * n
        ∧ (selectedPivot n (trajectory n a v k).1).magnitude ≤ (1.0e-14 : Float) := by
  by_cases hn2 : 2 ≤ n
  · exact trajectory_stops n a v hn2 hn' hstate hstart
  · have hn1 : n = 1 := by omega
    subst n
    have hscan := selectedPivot_correct 1 a hstate.matrix_finite hstate.symmetric
    have hzero : (selectedPivot 1 a).magnitude = 0.0 := by
      rcases hscan.2.2.2.1 with hz | ⟨hpq, hq, _⟩
      · exact hz
      · omega
    refine ⟨0, by norm_num, ?_⟩
    change (selectedPivot 1 a).magnitude ≤ (1.0e-14 : Float)
    rw [hzero]
    apply (le_iff _ _ (by decide) (by decide)).mpr
    rw [zero_value]
    exact (show 0 ≤ (2 : ℝ)^(-47 : Int) by positivity).trans Jacobi.stopping_threshold_bounds.1

/-- The actual outer loop returns the finalization of a stopped native
trajectory prefix. This execution trace transfers prefix error bounds to the
returned spectrum, including an early return before the known stopping index. -/
theorem iterations_trace (n : Nat) (magnitude : Float) (a v : Array Float)
    (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ) ^ (500 : Int))
    (hstate : State n 0 a v)
    (hstart : offEnergy (matrix n n a) ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    : ∃ result,
        iterations n magnitude a v = .ok result
        ∧ Stored n result
        ∧ ∃ k,
            k < 32 * n * n
            ∧ (selectedPivot n (trajectory n a v k).1).magnitude ≤ (1.0e-14 : Float)
            ∧ finish n magnitude (trajectory n a v k).1 (trajectory n a v k).2 = .ok result := by
  obtain ⟨stop, hstop, hstopAt⟩ := stopping_index n a v hn hn' hstate hstart
  let post := fun result => Stored n result ∧ ∃ k, k < 32 * n * n ∧
    (selectedPivot n (trajectory n a v k).1).magnitude ≤ (1.0e-14 : Float) ∧
    finish n magnitude (trajectory n a v k).1 (trajectory n a v k).2 = .ok result
  have h := iterations_triple n magnitude a v hn' hm hmb hstate stop hstop hstopAt
    post (fun k hk hst result he hstored => ⟨hstored, k, hk.trans_lt hstop, hst, he⟩)
  cases he : iterations n magnitude a v with
  | error e =>
      rw [he] at h; exact False.elim (h True.intro)
  | ok result =>
      rw [he] at h; exact ⟨result, rfl, h True.intro⟩

/-- The actual bounded outer loop returns finite spectrum storage, including
the final rescaling. The singleton case needs no rotation. Normalized input
energy and a bounded finite rescaling factor are the only numerical premises. -/
theorem iterations_success (n : Nat) (magnitude : Float) (a v : Array Float)
    (hn : 1 ≤ n) (hn' : n ≤ 18)
    (hm : magnitude.isFinite = true) (hmb : |value magnitude| ≤ (2 : ℝ) ^ (500 : Int))
    (hstate : State n 0 a v)
    (hstart : offEnergy (matrix n n a) ≤ (1001 / 1000 : ℝ) * (n * (n - 1) : Nat))
    : ∃ result, iterations n magnitude a v = .ok result ∧ Stored n result := by
  obtain ⟨result, he, hstored, _⟩ := iterations_trace n magnitude a v hn hn' hm hmb hstate hstart
  exact ⟨result, he, hstored⟩

end Flare.Matrix.JacobiConvergence
