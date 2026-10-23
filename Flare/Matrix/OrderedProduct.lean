module

public import Flare.Matrix.Multiplication
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Ordered matrix product semantics

Successful dense multiplication has the same entries as an ascending fold with
separately rounded multiplication and addition. This bridge exposes operation
order to source adapters without identifying reassociated or fused arithmetic.
-/

@[expose] public section

namespace Flare.Matrix.OrderedProduct

open Flare.Matrix.Dense Std.Do

set_option experimental.vcgen true

attribute [local instance] Std.Internal.Order.instPartialOrderProp
  Std.Internal.Order.instCompleteLatticeProp

/-- The first `count` terms of the native, ascending dot product. -/
def dot (inner columns : Nat) (a b : Array Float) (i j count : Nat) : Float :=
  (List.range count).foldl (fun s k => s + entry inner a i k * entry columns b k j) 0.0

/-- Each entry is an ordered dot product; shape premises belong to the caller. -/
def product (rows inner columns : Nat) (a b : Array Float) : Array Float :=
  (Array.range (rows * columns)).map
    fun k => dot inner columns a b (k / columns) (k % columns) inner

private def Progress (rows inner columns : Nat) (a b : Array Float)
    (row column : Nat) (result : Array Float)
    : Prop :=
  result.size = rows * columns
  ∧ ∀ i j,
      i < rows
      → j < columns
      → i < row ∨ i = row ∧ j < column
      → entry columns result i j = dot inner columns a b i j inner

private theorem start (rows inner columns : Nat) (a b : Array Float)
    : Progress rows inner columns a b 0 0 (Array.replicate (rows * columns) 0.0) := by
  refine ⟨by simp, ?_⟩
  intros
  omega

private theorem update (rows inner columns : Nat) (a b result : Array Float) (i j : Nat)
    (hi : i < rows) (hj : j < columns)
    (hs : Progress rows inner columns a b i j result)
    : Progress rows inner columns a b i (j + 1)
        (result.set! (i * columns + j) (dot inner columns a b i j inner)) := by
  refine ⟨(Array.size_set! ..).trans hs.1, ?_⟩
  intro r c hr hc hp
  rw [Flare.Matrix.Storage.entry_set columns result i j r c _ hs.1 hi hj hc]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    rfl
  · exact hs.2 r c hr hc (by omega)

private theorem row_complete (rows inner columns : Nat) (a b result : Array Float) (i : Nat)
    (hs : Progress rows inner columns a b i columns result)
    : Progress rows inner columns a b (i + 1) 0 result := by
  refine ⟨hs.1, ?_⟩
  intro r c hr hc hp
  exact hs.2 r c hr hc (by omega)

@[local spec]
private theorem finite_returns (x : Float)
    : Std.WP.Triple (finite x) True (fun y => y = x) (fun _ => True) := by
  vcgen [finite] with finish

/-- A successful checked loop returns the ordered product. Errors are allowed
by this partial-correctness statement; numerical contracts establish success. -/
theorem multiply_eq (rows inner columns : Nat) (a b result : Array Float)
    (h : Flare.Matrix.Dense.multiply rows inner columns a b = .ok result)
    : result = product rows inner columns a b := by
  have ht : ⦃⌜True⌝⦄ Flare.Matrix.Dense.multiply rows inner columns a b
      ⦃⇓? r => ⌜Progress rows inner columns a b rows 0 r⌝⦄ := by
    unfold Flare.Matrix.Dense.multiply
    apply (Specification.except_iff _ _ _).mpr
    have range_length (n : Nat) : (ForIn.toList [:n]).length = n := by simp
    vcgen [-Flare.Matrix.Storage.finite_wp_spec, -Flare.Matrix.Storage.finite_wp_exact,
      finite_returns] invariants
    | inv1 => fun pref _ r => Progress rows inner columns a b pref.length 0 r
    | inv2 pref i suff hi result hs =>
      fun pref' _ r => Progress rows inner columns a b i pref'.length r
    | inv3 pref i suff hi initial hs pref' j suff' hj result hs' =>
      fun pref'' _ s => s = dot inner columns a b i j pref''.length
    all_goals simp_all only [SPred.down_pure_nil]
    all_goals subst_vars
    all_goals first
    | (solve | trivial)
    | (solve | exact start ..)
    | (solve |
      rename_i prefI i suffI hi initial hinit prefJ j suffJ hj current hcurrent
      have hj' := Flare.Matrix.Storage.forIn_range_current hj
      simpa only [List.length_append, List.length_singleton, ← hj'.1]
        using update rows inner columns a b current i j
          (Flare.Matrix.Storage.forIn_range_current hi).2 hj'.2
          (by simpa only [hj'.1] using hcurrent))
    | (solve |
      rename_i pref i suff hi result hs
      simpa only [(Flare.Matrix.Storage.forIn_range_current hi).1, List.length_nil] using hs)
    | (solve |
      rename_i pref i suff hi initial hinit result hs
      have hi' := (Flare.Matrix.Storage.forIn_range_current hi).1
      simpa only [List.length_append, List.length_singleton, ← hi'] using
        row_complete rows inner columns a b result i (by simpa only [range_length] using hs))
    | (solve |
      rename_i prefI i suffI hi initial hinit prefJ j suffJ hj current hcurrent prefK k suffK hk
      have hk' := Flare.Matrix.Storage.forIn_range_current hk
      simp only [List.length_append, List.length_singleton, ← hk'.1, dot, List.range_succ,
        List.foldl_append, List.foldl_cons, List.foldl_nil])
  rw [h] at ht
  have hs := ht True.intro
  apply Array.ext
  · simpa [product] using hs.1
  · intro k hk hk'
    have hc : 0 < columns := by
      rw [hs.1] at hk
      by_contra hn
      have : columns = 0 := by omega
      simp [this] at hk
    have hr : k / columns < rows := Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hs.1 ▸ hk)
    have hm := hs.2 (k / columns) (k % columns) hr (Nat.mod_lt _ hc) (Or.inl hr)
    have hind : k / columns * columns + k % columns = k := by
      simpa [Nat.mul_comm] using Nat.div_add_mod k columns
    simpa [product, entry, hind, Array.getD_eq_getD_getElem?, hk] using hm

end Flare.Matrix.OrderedProduct
