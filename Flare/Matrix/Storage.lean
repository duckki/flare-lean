module

public import Flare.Matrix.Dense
public import Std.Tactic.Do
public import Mathlib.Tactic.SplitIfs
public import Flare.Matrix.Specification

/-! Representation invariants of the checked native matrix operations. -/

@[expose] public section

namespace Flare.Matrix.Storage

open Std.Do Flare.Matrix.Dense

-- The tactic produces ordinary kernel-checked proofs; no additional trust axiom.
set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

@[simp] theorem zero_finite : (0.0 : Float).isFinite = true := by decide

theorem all_set (a : Array Float) (i : Nat) (x : Float)
    (ha : a.all Float.isFinite = true) (hx : x.isFinite = true)
    : (a.set! i x).all Float.isFinite = true := by
  simp only [← Array.all_toList, Array.toList_set!, List.all_eq_true] at *
  intro y hy
  rcases List.mem_or_eq_of_mem_set hy with hy | rfl
  · exact ha y hy
  · exact hx

theorem storage_set (a : Array Float) (i : Nat) (x : Float) (N : Nat)
    (ha : a.size = N ∧ a.all Float.isFinite = true) (hx : x.isFinite = true)
    : (a.set! i x).size = N ∧ (a.set! i x).all Float.isFinite = true :=
  ⟨(Array.size_set! _ _ _).trans ha.1, all_set a i x ha.2 hx⟩

theorem replicate_storage (n : Nat)
    : (Array.replicate n (0.0 : Float)).size = n
      ∧ (Array.replicate n (0.0 : Float)).all Float.isFinite = true := by
  constructor
  · exact Array.size_replicate ..
  · rw [Array.all_eq_true]
    simp

@[spec]
theorem finite_spec (x : Float) : ⦃⌜True⌝⦄ finite x ⦃⇓? y => ⌜y.isFinite = true⌝⦄ := by
  apply (Specification.except_iff _ _ _).mpr
  vcgen [finite] with finish

open scoped Std.WP in
/-- Native `vcgen` form of the finiteness guarantee, allowing checked rejection. -/
@[spec]
theorem finite_wp_spec (x : Float)
    : Std.WP.Triple (finite x) True (fun y => y.isFinite = true) (fun _ => True) :=
  (Specification.except_iff _ _ _).mp (finite_spec x)

open scoped Std.WP in
/-- A finite input passes the check unchanged, with exceptional outcomes excluded. -/
theorem finite_wp_exact (x : Float)
    : Std.WP.Triple (finite x) (x.isFinite = true) (fun y => y = x) (fun _ => False) := by
  vcgen [finite] with finish

@[spec]
theorem multiply_spec (rows inner columns : Nat) (a b : Array Float)
    : ⦃⌜True⌝
      ⦄ multiply rows inner columns a b
      ⦃⇓? result => ⌜result.size = rows * columns ∧ result.all Float.isFinite = true⌝⦄ := by
  apply (Specification.except_iff _ _ _).mpr
  vcgen [multiply] invariants
  · fun _ _ result => result.size = rows * columns ∧ result.all Float.isFinite = true
  · fun _ _ result => result.size = rows * columns ∧ result.all Float.isFinite = true
  · fun _ _ value => value.isFinite = true
  all_goals simp only [SPred.down_pure_nil] at *
  all_goals first
  | (solve | exact zero_finite)
  | (solve | apply storage_set <;> assumption)
  | (solve | exact replicate_storage _)
  | (solve | grind)

@[spec]
theorem solve_spec (n columns : Nat) (f : Factor) (b : Array Float)
    : ⦃⌜True⌝
      ⦄ solve n columns f b
      ⦃⇓? result => ⌜result.size = n * columns ∧ result.all Float.isFinite = true⌝⦄ := by
  apply (Specification.except_iff _ _ _).mpr
  vcgen [solve] invariants
  · fun _ _ _ => True
  · fun _ _ result => result.size = n * columns ∧ result.all Float.isFinite = true
  · fun _ _ result => result.size = n * columns ∧ result.all Float.isFinite = true
  · fun _ _ value => value.isFinite = true
  · fun _ _ _ => True
  · fun _ _ _ => True
  all_goals simp only [SPred.down_pure_nil] at *
  all_goals first
  | (solve | apply storage_set <;> assumption)
  | (solve | exact replicate_storage _)
  | (solve | grind)

@[spec]
theorem solveSPD_spec (n columns : Nat) (a b : Array Float)
    : ⦃⌜True⌝
      ⦄ solveSPD n columns a b
      ⦃⇓? result => ⌜result.size = n * columns ∧ result.all Float.isFinite = true⌝⦄ := by
  unfold solveSPD
  cases factor n a with
  | error e =>
      apply (Specification.except_iff _ _ _).mpr
      vcgen with finish
  | ok f => exact solve_spec n columns f b

theorem getD_finite (a : Array Float) (i : Nat) (ha : a.all Float.isFinite = true)
    : (a.getD i 0.0).isFinite = true := by
  rw [Array.all_eq_true] at ha
  simp only [Array.getD_eq_getD_getElem?, Array.getD_getElem?]
  split
  · exact ha _ _
  · exact zero_finite

theorem flat_index_eq {n r c i j : Nat} (hc : c < n) (hj : j < n)
    : r * n + c = i * n + j ↔ r = i ∧ c = j := by
  constructor
  · intro h
    have hmod := congrArg (· % n) h
    have hdiv := congrArg (· / n) h
    have hn : 0 < n := by omega
    simp only [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hj] at hmod
    simp only [Nat.add_comm (r * n) c, Nat.add_comm (i * n) j,
      Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hj, Nat.zero_add] at hdiv
    exact ⟨hdiv, hmod⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem entry_set (n : Nat) (a : Array Float) (i j r c : Nat) (x : Float) {rows : Nat}
    (ha : a.size = rows * n) (hi : i < rows) (hj : j < n) (hc : c < n)
    : entry n (a.set! (i * n + j) x) r c = if r = i ∧ c = j then x else entry n a r c := by
  have hidx : i * n + j < a.size := by
    have := Nat.mul_le_mul_right n (show i + 1 ≤ rows by omega)
    rw [Nat.add_mul] at this
    omega
  by_cases h : r = i ∧ c = j
  · rcases h with ⟨rfl, rfl⟩
    simp [entry, Array.set!_eq_setIfInBounds, hidx]
  · have hne : i * n + j ≠ r * n + c := fun he => h ((flat_index_eq hc hj).mp he.symm)
    simp only [entry, Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne hne, h, ↓reduceIte]

/-- Proof-only progress predicate: columns below k and the first l entries of
column k have received their lower-triangle copies. -/
private def MirrorState (n : Nat) (a : Array Float) (k l : Nat) (result : Array Float) : Prop :=
  result.size = n * n
  ∧ result.all Float.isFinite = true
  ∧ ∀ r c,
      r < n
      → c < n
      → entry n result r c
        = if r < c ∧ (c < k ∨ c = k ∧ r < l) then entry n a c r else entry n a r c

private theorem mirror_start (n : Nat) (a : Array Float)
    (ha : a.size = n * n ∧ a.all Float.isFinite = true)
    : MirrorState n a 0 0 a := by
  refine ⟨ha.1, ha.2, ?_⟩
  intros
  simp

private theorem mirror_step (n : Nat) (a result : Array Float) (k l : Nat)
    (ha : a.all Float.isFinite = true) (hk : k < n) (hl : l < k)
    (hs : MirrorState n a k l result)
    : MirrorState n a k (l + 1) (result.set! (l * n + k) (entry n a k l)) := by
  refine ⟨(Array.size_set! ..).trans hs.1, all_set _ _ _ hs.2.1 (getD_finite a _ ha), ?_⟩
  intro r c hr hc
  rw [entry_set n result l k r c _ hs.1 (by omega) hk hc]
  rw [hs.2.2 r c hr hc]
  split_ifs <;> first | rfl | (congr 1 <;> omega)

private theorem mirror_row_complete (n : Nat) (a result : Array Float) (k : Nat)
    (hs : MirrorState n a k k result)
    : MirrorState n a (k + 1) 0 result := by
  refine ⟨hs.1, hs.2.1, ?_⟩
  intro r c hr hc
  rw [hs.2.2 r c hr hc]
  split_ifs <;> first | rfl | omega

theorem range_current {n i : Nat} {pref suff : List Nat} (h : [:n].toList = pref ++ i :: suff)
    : i = pref.length ∧ i < n := by
  have h' : List.range n = pref ++ i :: suff := by
    simpa [Std.Legacy.Range.toList, ← List.range_eq_range'] using h
  have hi : pref.length < n := by
    have := congrArg List.length h'
    simp only [List.length_range, List.length_append, List.length_cons] at this
    omega
  have he := congrArg (fun xs => xs[pref.length]?) h'
  have he' : i = pref.length := by simpa [hi] using he.symm
  exact ⟨he', he' ▸ hi⟩

/-- Cursor facts for the container representation used by `vcgen`. -/
theorem forIn_range_current {n i : Nat} {pref suff : List Nat}
    (h : ForIn.toList [:n] = pref ++ i :: suff)
    : i = pref.length ∧ i < n := by
  apply range_current (n := n) (i := i) (pref := pref) (suff := suff)
  simpa [Std.Legacy.Range.toList] using h

theorem mirrorLower_spec (n : Nat) (a : Array Float)
    : Triple (m := Id) (mirrorLower n a) (⌜a.size = n * n ∧ a.all Float.isFinite = true⌝)
        (⇓ result
          =>
            ⌜
              result.size = n * n
              ∧ result.all Float.isFinite = true
              ∧ ∀ r c,
                  r < n
                  → c < n
                  → entry n result r c = if r < c then entry n a c r else entry n a r c
              ⌝) := by
  apply (Specification.id_iff _ _ _).mpr
  unfold mirrorLower Id.run
  vcgen invariants
  | inv1 => fun pref _ result => MirrorState n a pref.length 0 result
  | inv2 ha pref i suff h result hs =>
    fun pref' _ result => MirrorState n a i pref'.length result
  all_goals first
  | (solve | grind [MirrorState, mirror_start, mirror_step, mirror_row_complete, range_current])

theorem finite_beq_self (x : Float) (hx : x.isFinite = true) : (x == x) = true := by
  change x.toModel.unpack.isFinite = true at hx
  change Float.Model.UnpackedFloat.beq x.toModel.unpack x.toModel.unpack = true
  cases h : x.toModel.unpack with
  | notANumber => simp [h, Float.Model.UnpackedFloat.isFinite] at hx
  | infinity s => simp [h, Float.Model.UnpackedFloat.isFinite] at hx
  | zero s => rfl
  | finite s m e hm =>
      cases s <;> simp [Float.Model.UnpackedFloat.beq, Float.Model.UnpackedFloat.compare]

theorem symmetric_true (n : Nat) (a : Array Float)
    (h : ∀ i j, i < n → j < i → (entry n a i j == entry n a j i) = true)
    : Flare.Matrix.Dense.symmetric n a = true := by
  let prog : Id Bool := Flare.Matrix.Dense.symmetric n a
  have htriple : Std.WP.Triple prog True
      (fun b => b = true) Std.WP.EStackEnd.mk := by
    simp only [entry] at h
    unfold prog Flare.Matrix.Dense.symmetric Id.run
    vcgen invariants
    · fun _ _ result => result.1 = none
    · fun _ _ result => result.1 = none
    all_goals grind [range_current, bne]
  exact htriple.le_wp True.intro

theorem mirrorLower_properties (n : Nat) (a : Array Float)
    (ha : a.size = n * n ∧ a.all Float.isFinite = true)
    : (mirrorLower n a).size = n * n
      ∧ (mirrorLower n a).all Float.isFinite = true
      ∧ Flare.Matrix.Dense.symmetric n (mirrorLower n a) = true := by
  have hm : (mirrorLower n a).size = n * n ∧ (mirrorLower n a).all Float.isFinite = true ∧
      ∀ r c, r < n → c < n → entry n (mirrorLower n a) r c =
        if r < c then entry n a c r else entry n a r c := by
    exact mirrorLower_spec n a ha
  refine ⟨hm.1, hm.2.1, symmetric_true n _ ?_⟩
  intro i j hi hj
  rw [hm.2.2 i j hi (by omega), hm.2.2 j i (by omega) hi]
  simp only [show ¬i < j by omega, hj, ↓reduceIte]
  exact finite_beq_self _ (getD_finite a _ ha.2)

end Flare.Matrix.Storage
