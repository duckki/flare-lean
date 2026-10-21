module

public import Flare.Binary64.Division
public import Flare.Binary64.Order

/-! Signed compositional bounds for actual native binary64 operations. The
independent ideal operand is propagated at every node; it is never reset to a
rounded intermediate. Bounds include finite execution and gradual underflow. -/

@[expose] public section

namespace Flare.Binary64.Pipeline

open Flare.Binary64.Value Flare.Binary64.Arithmetic

structure Bounds (C W I E n i : ℝ) : Prop where
  centre : |n - C| ≤ W
  ideal : |i| ≤ I
  error : |n - i| ≤ E

structure NativeBounds (C W I E : ℝ) (n : Float) (i : ℝ) : Prop where
  finite : n.isFinite = true
  bounds : Bounds C W I E (value n) i

theorem native_bound {C W I E n i : ℝ} (h : Bounds C W I E n i) : |n| ≤ |C| + W := by
  have ht := abs_add_le (n - C) C
  rw [sub_add_cancel] at ht
  linarith [h.centre]

theorem weaken {C W I E n i C' W' I' E' : ℝ} (h : Bounds C W I E n i)
    (hw : W + |C - C'| ≤ W') (hi : I ≤ I') (he : E ≤ E')
    : Bounds C' W' I' E' n i := by
  refine ⟨?_, h.ideal.trans hi, h.error.trans he⟩
  have ht := abs_add_le (n - C) (C - C')
  rw [sub_add_sub_cancel] at ht
  linarith [h.centre]

theorem native_weaken {C W I E i C' W' I' E' : ℝ} {n : Float}
    (h : NativeBounds C W I E n i)
    (hw : W + |C - C'| ≤ W') (hi : I ≤ I') (he : E ≤ E')
    : NativeBounds C' W' I' E' n i :=
  ⟨h.finite, weaken h.bounds hw hi he⟩

theorem ideal_refine {C W I E n i I' : ℝ} (h : Bounds C W I E n i) (hi : |C| + W + E ≤ I')
    : Bounds C W I' E n i := by
  refine ⟨h.centre, ?_, h.error⟩
  have ht := abs_add_le (i - n) n
  rw [sub_add_cancel, abs_sub_comm i n] at ht
  linarith [native_bound h, h.error]

theorem native_ideal_refine {C W I E i I' : ℝ} {n : Float}
    (h : NativeBounds C W I E n i) (hi : |C| + W + E ≤ I')
    : NativeBounds C W I' E n i :=
  ⟨h.finite, ideal_refine h.bounds hi⟩

theorem same (x : Float) (C W I : ℝ) (hf : x.isFinite = true)
    (hw : |value x - C| ≤ W) (hi : |value x| ≤ I)
    : NativeBounds C W I 0 x (value x) := by exact ⟨hf, hw, hi, by simp⟩

theorem add_bounds {C W I E D V J F n i p j : ℝ} (a : Bounds C W I E n i) (b : Bounds D V J F p j)
    : Bounds (C + D) (W + V) (I + J) (E + F) (n + p) (i + j) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show n + p - (C + D) = (n - C) + (p - D) by ring]
    exact (abs_add_le _ _).trans (add_le_add a.centre b.centre)
  · exact (abs_add_le _ _).trans (add_le_add a.ideal b.ideal)
  · rw [show n + p - (i + j) = (n - i) + (p - j) by ring]
    exact (abs_add_le _ _).trans (add_le_add a.error b.error)

theorem neg_bounds {C W I E n i : ℝ} (a : Bounds C W I E n i) : Bounds (-C) W I E (-n) (-i) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [neg_sub_neg, abs_sub_comm] using a.centre
  · simpa only [abs_neg] using a.ideal
  · simpa only [neg_sub_neg, abs_sub_comm] using a.error

theorem sub_bounds {C W I E D V J F n i p j : ℝ} (a : Bounds C W I E n i) (b : Bounds D V J F p j)
    : Bounds (C - D) (W + V) (I + J) (E + F) (n - p) (i - j) :=
  add_bounds a (neg_bounds b)

theorem abs_product {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem mul_bounds {C W I E D V J F n i p j : ℝ} (a : Bounds C W I E n i) (b : Bounds D V J F p j)
    : Bounds (C * D) (W * (|D| + V) + |C| * V) (I * J) (E * (|D| + V) + I * F) (n * p) (i * j) := by
  refine ⟨?_, abs_product a.ideal b.ideal, ?_⟩
  · rw [show n * p - C * D = (n - C) * p + C * (p - D) by ring]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_product a.centre (native_bound b))
        (abs_product (le_refl |C|) b.centre))
  · rw [show n * p - i * j = (n - i) * p + i * (p - j) by ring]
    exact (abs_add_le _ _).trans
      (add_le_add (abs_product a.error (native_bound b)) (abs_product a.ideal b.error))

theorem abs_div_upper {a A b B : ℝ} (ha : |a| ≤ A) (hB : 0 < B) (hb : B ≤ b) : |a / b| ≤ A / B := by
  rw [abs_div, abs_of_pos (hB.trans_le hb)]
  exact div_le_div₀ ((abs_nonneg _).trans ha) ha hB hb

theorem quotient_difference (n i p j : ℝ) (hp : p ≠ 0) (hj : j ≠ 0)
    : n / p - i / j = (n - i) / p + i * (j - p) / (p * j) := by
  field_simp
  ring

theorem div_bounds {C W I E D V J F n i p j : ℝ}
    (a : Bounds C W I E n i) (b : Bounds D V J F p j)
    (hp : 0 < D - V) (hj : 0 < D - V - F)
    : Bounds (C / D) (W / (D - V) + |C| * V / ((D - V) * D))
        (I / (D - V - F)) (E / (D - V) + I * F / ((D - V) * (D - V - F)))
        (n / p) (i / j) := by
  have hp' : D - V ≤ p := by linarith [(abs_le.mp b.centre).1]
  have hj' : D - V - F ≤ j := by linarith [(abs_le.mp b.error).2]
  have hD : 0 < D := by linarith [abs_nonneg (p - D), b.centre]
  have hp0 : p ≠ 0 := (hp.trans_le hp').ne'
  have hj0 : j ≠ 0 := (hj.trans_le hj').ne'
  refine ⟨?_, abs_div_upper a.ideal hj hj', ?_⟩
  · rw [quotient_difference _ _ _ _ hp0 hD.ne']
    have hb : |C * (D - p)| ≤ |C| * V := by
      rw [abs_mul, abs_sub_comm D p]
      exact mul_le_mul_of_nonneg_left b.centre (abs_nonneg _)
    have hd : (D - V) * D ≤ p * D := mul_le_mul_of_nonneg_right hp' hD.le
    exact (abs_add_le _ _).trans (add_le_add (abs_div_upper a.centre hp hp')
      (abs_div_upper hb (mul_pos hp hD) hd))
  · rw [quotient_difference _ _ _ _ hp0 hj0]
    have hb : |i * (j - p)| ≤ I * F := by
      rw [abs_mul, abs_sub_comm j p]
      exact mul_le_mul a.ideal b.error (abs_nonneg _) ((abs_nonneg _).trans a.ideal)
    have hd : (D - V) * (D - V - F) ≤ p * j :=
      mul_le_mul hp' hj' hj.le (hp.trans_le hp').le
    exact (abs_add_le _ _).trans (add_le_add (abs_div_upper a.error hp hp')
      (abs_div_upper hb (mul_pos hp hj) hd))

theorem rounded {C W I E n i t rho : ℝ} (a : Bounds C W I E n i) (hr : |t - n| ≤ rho)
    : Bounds C (W + rho) I (E + rho) t i := by
  refine ⟨?_, a.ideal, ?_⟩
  · have ht := abs_add_le (t - n) (n - C)
    rw [sub_add_sub_cancel] at ht
    linarith [a.centre]
  · have ht := abs_add_le (t - n) (n - i)
    rw [sub_add_sub_cancel] at ht
    linarith [a.error]

theorem native_add {C W I E D V J F i j : ℝ} {n p : Float}
    (a : NativeBounds C W I E n i) (b : NativeBounds D V J F p j)
    (N : Int) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hm : |value n + value p| ≤ (2 : ℝ) ^ N)
    : NativeBounds (C + D) (W + V + (2 : ℝ) ^ (N - 52)) (I + J)
        (E + F + (2 : ℝ) ^ (N - 52)) (n + p) (i + j) := by
  obtain ⟨hf, he⟩ := add_error n p N a.finite b.finite hN hN' hm
  exact ⟨hf, rounded (add_bounds a.bounds b.bounds) he⟩

theorem native_sub {C W I E D V J F i j : ℝ} {n p : Float}
    (a : NativeBounds C W I E n i) (b : NativeBounds D V J F p j)
    (N : Int) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hm : |value n - value p| ≤ (2 : ℝ) ^ N)
    : NativeBounds (C - D) (W + V + (2 : ℝ) ^ (N - 52)) (I + J)
        (E + F + (2 : ℝ) ^ (N - 52)) (n - p) (i - j) := by
  obtain ⟨hf, he⟩ := sub_error n p N a.finite b.finite hN hN' hm
  exact ⟨hf, rounded (sub_bounds a.bounds b.bounds) he⟩

theorem native_mul {C W I E D V J F i j : ℝ} {n p : Float}
    (a : NativeBounds C W I E n i) (b : NativeBounds D V J F p j)
    (N : Int) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hm : |value n * value p| ≤ (2 : ℝ) ^ N)
    : NativeBounds (C * D) (W * (|D| + V) + |C| * V + (2 : ℝ) ^ (N - 52))
        (I * J) (E * (|D| + V) + I * F + (2 : ℝ) ^ (N - 52)) (n * p) (i * j) := by
  obtain ⟨hf, he⟩ := mul_error n p N a.finite b.finite hN hN' hm
  exact ⟨hf, rounded (mul_bounds a.bounds b.bounds) he⟩

theorem native_div {C W I E D V J F i j : ℝ} {n p : Float}
    (a : NativeBounds C W I E n i) (b : NativeBounds D V J F p j)
    (hp : 0 < D - V) (hj : 0 < D - V - F)
    (N : Int) (hN : -1022 ≤ N) (hN' : N ≤ 1022)
    (hm : |value n / value p| ≤ (2 : ℝ) ^ N)
    : NativeBounds (C / D) (W / (D - V) + |C| * V / ((D - V) * D) + (2 : ℝ) ^ (N - 51))
        (I / (D - V - F))
        (E / (D - V) + I * F / ((D - V) * (D - V - F)) + (2 : ℝ) ^ (N - 51))
        (n / p) (i / j) := by
  have hp0 : value p ≠ 0 := by linarith [(abs_le.mp b.bounds.centre).1]
  obtain ⟨hf, he⟩ := Flare.Binary64.Division.div_error n p N a.finite b.finite hp0 hN hN' hm
  exact ⟨hf, rounded (div_bounds a.bounds b.bounds hp hj) he⟩

theorem native_neg {C W I E i : ℝ} {n : Float} (a : NativeBounds C W I E n i)
    : NativeBounds (-C) W I E (-n) (-i) := by
  obtain ⟨hf, he⟩ := Flare.Binary64.Order.neg_value n a.finite
  exact ⟨hf, he ▸ neg_bounds a.bounds⟩

end Flare.Binary64.Pipeline
