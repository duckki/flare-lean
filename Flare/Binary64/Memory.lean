module

public import Mathlib.Tactic

/-! Checked access to initialized binary64 cells and finite disjoint regions. -/

@[expose] public section

namespace Flare.Binary64.Memory

abbrev Heap := Array Float

/-- A half-open region fits within the finite heap of typed cells. -/
def valid (heap : Heap) (base length : Nat) : Prop := base + length ≤ heap.size

/-- Disjoint half-open regions; read-only regions need not be disjoint. -/
def separated (left leftLength right rightLength : Nat) : Prop :=
  left + leftLength ≤ right ∨ right + rightLength ≤ left

def load (heap : Heap) (index : Nat) : Option Float :=
  if index < heap.size then some heap[index]! else none

def store (heap : Heap) (index : Nat) (value : Float) : Option Heap :=
  if index < heap.size then some (heap.set! index value) else none

theorem load_eq (heap : Heap) (index : Nat) (h : index < heap.size)
    : load heap index = some heap[index]! := by simp [load, h]

theorem store_eq (heap : Heap) (index : Nat) (value : Float) (h : index < heap.size)
    : store heap index value = some (heap.set! index value) := by simp [store, h]

theorem set_frame (heap : Heap) (index other : Nat) (value : Float) (h : index ≠ other)
    : (heap.set! index value)[other]! = heap[other]! :=
  Array.getElem!_set!_ne heap index other value h

theorem region_index (heap : Heap) (base length index : Nat)
    (h : valid heap base length) (hi : index < length)
    : base + index < heap.size := by
  simp only [valid] at h
  omega

theorem separated_indices (left leftLength right rightLength i j : Nat)
    (h : separated left leftLength right rightLength) (hi : i < leftLength)
    (hj : j < rightLength)
    : left + i ≠ right + j := by
  simp only [separated] at h
  omega

end Flare.Binary64.Memory
