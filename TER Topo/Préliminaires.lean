import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Basic
import Mathlib.Order.SetNotation
import Mathlib.Tactic

-- Préliminaires

-- quelques bases sur ℝˣ, ℝ₊, ℝ₋
-- dans la suite, ℝ désigne un Type, et R désigne un ensemble de ℝ

def R : Set ℝ := Set.univ

def R_star : Set ℝ := {x : ℝ | x ≠ 0}
def ℝ_star : Type _ := {x : ℝ // x ≠ 0}
notation "Rˣ" => R_star
notation "ℝˣ" => ℝ_star

def R_pos : Set ℝ := {x : ℝ | x ≥ 0}
def ℝ_pos : Type _ := {x : ℝ // x ≥ 0}
notation "R₊" => R_pos
notation "ℝ₊" => ℝ_pos

def R_neg : Set ℝ := {x : ℝ | x ≤ 0}
def ℝ_neg : Type _ := {x : ℝ // x ≤ 0}
notation "R₋" => R_neg
notation "ℝ₋" => ℝ_neg

namespace prelim_R

@[coe, simp] def R_star.toReal : ℝˣ → ℝ := fun x => x.val
instance : Coe ℝˣ ℝ := ⟨R_star.toReal⟩

@[coe, simp] def R_pos.toReal : ℝ₊ → ℝ := fun x => x.val
instance : Coe ℝ₊ ℝ := ⟨R_pos.toReal⟩

@[coe, simp] def R_neg.toReal : ℝ₋ → ℝ := fun x => x.val
instance : Coe ℝ₋ ℝ := ⟨R_neg.toReal⟩

@[coe, simp] def Real.toPos : ℝ → ℝ₊ := fun x => ⟨|x|, abs_nonneg x⟩
instance : Coe ℝ ℝ₊ := ⟨Real.toPos⟩

@[coe, simp] def Nat.toPos : Nat → ℝ₊ := fun n => ⟨(n : ℝ), Nat.cast_nonneg n⟩
instance : Coe Nat ℝ₊ := ⟨Nat.toPos⟩
instance {n} : OfNat ℝ₊ n := ⟨Nat.toPos n⟩

lemma Nat.ofPos (n : Nat) : (n : ℝ) ∈ R₊ := by unfold R_pos; simp
instance {n} : OfNat R₊ n := ⟨(n : ℝ), Nat.ofPos n⟩

-- on veut que le compilateur puisse reconnaître les opérations dans les ensembles de R

instance : HAdd R R ℝ where
  hAdd := fun x => fun y => (x : ℝ) + (y : ℝ)

instance : HSub R R ℝ where
  hSub := fun x => fun y => (x : ℝ) - (y : ℝ)

instance : HMul R R ℝ where
  hMul := fun x => fun y => (x : ℝ) * (y : ℝ)

instance : HAdd R₊ R₊ ℝ where
  hAdd := fun x => fun y => (x : ℝ) + (y : ℝ)

instance : HSub R₊ R₊ ℝ where
  hSub := fun x => fun y => (x : ℝ) - (y : ℝ)

instance : HMul R₊ R₊ ℝ where
  hMul := fun x => fun y => (x : ℝ) * (y : ℝ)

instance : HAdd R₋ R₋ ℝ where
  hAdd := fun x => fun y => (x : ℝ) + (y : ℝ)

instance : HSub R₋ R₋ ℝ where
  hSub := fun x => fun y => (x : ℝ) - (y : ℝ)

instance : HMul R₋ R₋ ℝ where
  hMul := fun x => fun y => (x : ℝ) * (y : ℝ)

instance : HAdd Rˣ Rˣ ℝ where
  hAdd := fun x => fun y => (x : ℝ) + (y : ℝ)

instance : HSub Rˣ Rˣ ℝ where
  hSub := fun x => fun y => (x : ℝ) - (y : ℝ)

instance : HMul Rˣ Rˣ ℝ where
  hMul := fun x => fun y => (x : ℝ) * (y : ℝ)

-- on fait de même pour la relation d'ordre

instance : LE Rˣ where
  le := fun x => fun y => (x : ℝ) ≤ (y : ℝ)

instance : LE R₊ where
  le := fun x => fun y => (x : ℝ) ≤ (y : ℝ)

instance : LE R₋ where
  le := fun x => fun y => (x : ℝ) ≤ (y : ℝ)

@[simp] def R_star_le : Rˣ → ℝ → Prop := fun x => fun y => (x : ℝ) ≤ y
notation x " ≤ " y => R_star_le x y

@[simp] def R_pos_le : R₊ → ℝ → Prop := fun x => fun y => (x : ℝ) ≤ y
notation x " ≤ " y => R_pos_le x y

@[simp] def R_neg_le : R₋ → ℝ → Prop := fun x => fun y => (x : ℝ) ≤ y
notation x " ≤ " y => R_neg_le x y

@[simp] lemma coe_zero_pos : (0 : R₊) = ⟨((0 : ℕ) : ℝ), Nat.ofPos 0⟩ := by simp [OfNat.ofNat]

@[simp] lemma R_pos_eq (x : R₊) (y : R₊) : x = y ↔ x.val = y.val := by rw [SetCoe.ext_iff]

@[simp] lemma R_coe (x : R) (y : R) : x = y ↔ (x : ℝ) = (y : ℝ) := by rw [SetCoe.ext_iff]

@[simp] lemma R_pos_coe (x : R₊) (y : R₊) : x = y ↔ (x : ℝ) = (y : ℝ) := by rw [SetCoe.ext_iff]

-- toute partie non vide majorée admet une borne supérieure:

-- TODO

end prelim_R
