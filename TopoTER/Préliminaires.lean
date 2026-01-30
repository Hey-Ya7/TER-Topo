import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.SetNotation
import Mathlib.Tactic
import TopoTER.SetElem

-- Préliminaires

open TER

instance : Coe ℕ ℝ where
  coe := fun n => n

instance : Coe ℤ ℝ where
  coe := fun k => k

instance : Coe ℚ ℝ where
  coe := fun q => q

abbrev R : Set ℝ := Set.univ

abbrev R_star : Set ℝ := {x : ℝ | x ≠ 0}
notation "Rˣ" => R_star

abbrev R_pos : Set ℝ := {x : ℝ | x ≥ 0}
notation "R₊" => R_pos

abbrev R_neg : Set ℝ := {x : ℝ | x ≤ 0}
notation "R₋" => R_neg

abbrev R_star_pos : Set ℝ := {x : ℝ | x > 0}
notation "R₊ˣ" => R_star_pos

abbrev R_star_neg : Set ℝ := {x : ℝ | x < 0}
notation "R₋ˣ" => R_star_neg

abbrev C : Set ℂ := Set.univ

abbrev C_star : Set ℂ := {x : ℂ | x ≠ 0}
notation "Cˣ" => C_star

notation "ℝ.0" => (0 : ℝ)
notation "ℂ.0" => (0 : ℂ)

open Real Complex

theorem Complex.norm_eq_zero (z : ℂ) : ‖z‖ = 0 ↔ z = 0 := by
  dsimp [instNorm]; rw [sqrt_eq_zero, normSq_eq_zero]; apply normSq_nonneg

theorem Complex.norm_nonneg (z : ℂ) : ‖z‖ ≥ 0 := by apply sqrt_nonneg

theorem Complex.norm_symm (z : ℂ) : ‖z‖ = ‖-z‖ := by
  dsimp [instNorm, normSq]; rw [neg_mul_neg, neg_mul_neg]

lemma Complex.norm_add_one (z : ℂ) : ‖z + 1‖ ≤ ‖z‖ + 1 := by
  dsimp [instNorm, normSq]; apply le_of_sq_le_sq
  · rw [add_sq, sq_sqrt, sq_sqrt, sq, mul_one, one_mul]
    · rw [add_zero, add_mul_self_eq, mul_one, one_mul]
      have ineq : 2 * z.re ≤ 2 * √(z.re * z.re + z.im * z.im) := by
        apply mul_le_mul_of_nonneg_left (ha := zero_le_two)
        apply le_sqrt_of_sq_le; rw [sq]
        apply le_add_of_nonneg_right; apply mul_self_nonneg
      let re2 := z.re * z.re; let im2 := z.im * z.im; refold_let re2 im2
      calc re2 + 2 * z.re + 1 + im2
      _ = re2 + im2 + 1 + 2 * z.re := by ring
      _ ≤ re2 + im2 + 1 + 2 * √(re2 + im2) := by apply add_le_add_right ineq
      _ = re2 + im2 + 2 * √(re2 + im2) + 1 := by ring
    · apply normSq_nonneg
    · apply normSq_nonneg (z + 1)
  · apply add_nonneg (hb := zero_le_one); apply sqrt_nonneg

open Complex in
theorem Complex.norm_ineq (z : ℂ) (w : ℂ) : ‖z + w‖ ≤ ‖z‖ + ‖w‖ := by
  by_cases eq_zero : ‖w‖ = 0
  · rw [eq_zero, add_zero]; rw [norm_eq_zero] at eq_zero
    rw [eq_zero, add_zero]; apply le_refl
  · have pos : ‖w‖ > 0 := by
      apply lt_of_le_of_ne (norm_nonneg w)
      rw [ne_comm, ne_eq]; exact eq_zero
    apply (div_le_div_iff_of_pos_right pos).mp
    rw [←Complex.norm_div]; repeat rw [add_div, div_self]
    · rw [←Complex.norm_div]; apply norm_add_one
    · rw [ne_eq]; exact eq_zero
    · intro eq; rw [←norm_eq_zero] at eq; exact eq_zero eq

-- toute partie non vide majorée admet une borne supérieure:

-- TODO
