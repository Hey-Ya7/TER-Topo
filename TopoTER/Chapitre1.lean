import TopoTER.Préliminaires

open TER

-- 1. Espaces métriques

namespace Metrique

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

variable {α : Type*} {X : Set α}

def nneg (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y ≥ 0

def sep (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y = 0 ↔ x = y

def symm (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y = d y x

def ineq (X : Set α) (d : α → α → ℝ) := ∀ x y z ∈ X, d x z ≤ d x y + d y z

structure estDistance (X : Set α) (d : α → α → ℝ) where
  nneg : nneg X d
  sep : sep X d
  symm : symm X d
  ineq : ineq X d

structure EspaceMetrique (α : Type*) where
  X : Set α
  d : α → α → ℝ
  is_dist : estDistance X d

-- Exemple 1.2.

-- 1.
@[simp] def abs_dist : ℝ → ℝ → ℝ := x ↦ y ↦ |x - y|

lemma abs_nneg : nneg R abs_dist := by
  intro x _ y _; apply abs_nonneg

lemma abs_sep : sep R abs_dist := by
  intro x _ y _; dsimp; rw [abs_eq_zero, sub_eq_zero]

lemma abs_symm : symm R abs_dist := by
  intro x _ y _; dsimp; rw [abs_sub_comm]

lemma abs_ineq : ineq R abs_dist := by
  intro x _ y _ z _; dsimp; apply abs_sub_le

def R_usuelle : EspaceMetrique ℝ where
  X := R
  d := abs_dist
  is_dist := ⟨
    abs_nneg, abs_sep,
    abs_symm, abs_ineq
  ⟩

-- 2.
noncomputable section Complex
open Complex

@[simp] def module_dist : ℂ → ℂ → ℝ := x ↦ y ↦ ‖x - y‖ᵢ

lemma module_nneg : nneg C module_dist := by
  intro x _ y _; apply norm_nonneg

lemma module_sep : sep C module_dist := by
  intro x _ y _; dsimp; rw [norm_eq_zero, sub_eq_zero]

lemma module_symm : symm C module_dist := by
  intro x _ y _; dsimp; rw [norm_symm, neg_sub]

lemma module_ineq : ineq C module_dist := by
  intro x _ y _ z _; unfold module_dist
  have eq : x - z = (x - y) + (y - z) := by ring
  rw [eq]; apply norm_ineq

def C_usuelle : EspaceMetrique ℂ where
  X := C
  d := module_dist
  is_dist := ⟨
    module_nneg, module_sep,
    module_symm, module_ineq
  ⟩

end Complex

-- 3.
noncomputable section Euclidean
open VectorSpace
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [Euclidean E]

@[simp] def euclid_dist : E → E → ℝ := x ↦ y ↦ ‖x - y‖ₑ

lemma euclid_nneg : nneg E↑ euclid_dist := by
  intro x _ y _; apply norm_nonneg

lemma euclid_sep : sep E↑ euclid_dist := by
  intro x _ y _; dsimp; rw [norm_eq_zero, sub_eq_zero]

lemma euclid_symm : symm E↑ euclid_dist := by
  intro x _ y _; dsimp; rw [norm_symm, neg_sub]

lemma euclid_ineq : ineq E↑ euclid_dist := by
  intro x _ y _ z _; dsimp
  have eq : x - z = (x - y) + (y - z) := by abel
  rw [eq]; apply norm_ineq

def Euclid : EspaceMetrique E where
  X := E↑
  d := euclid_dist
  is_dist := ⟨
    euclid_nneg, euclid_sep,
    euclid_symm, euclid_ineq
  ⟩

end Euclidean

-- 4.
noncomputable section Discrete
open Classical in
@[simp] def discrete_dist : α → α → ℝ := x ↦ y ↦ ite (x = y) 0 1

lemma discrete_nneg : nneg X discrete_dist := by
  intro x _ y _; dsimp; split
  · case isTrue => rfl
  · case isFalse => linarith

lemma discrete_sep : sep X discrete_dist := by
  intro x _ y _; dsimp; split
  · case isTrue h => simp only [h]
  · case isFalse h => simp only [one_ne_zero, h]

lemma discrete_symm : symm X discrete_dist := by
  intro x _ y _; dsimp; rw [@Eq.comm α]

open Classical in
lemma discrete_ineq : ineq X discrete_dist := by
  intro x h1 y h2 z h3; dsimp; split
  · case isTrue => apply add_nonneg (discrete_nneg x h1 y h2)
                   apply discrete_nneg y h2 z h3
  · case isFalse h =>
    split
    · case isTrue h' =>
      have eq : ite (y = z) (0 : ℝ) 1 = 1 := by
        apply if_neg; rw [←h']; exact h
      rw [eq]; apply le_add_of_nonneg_left (le_refl 0)
    · case isFalse => apply le_add_of_nonneg_right
                      apply discrete_nneg y h2 z h3

def Discrete (X : Set α) : EspaceMetrique α where
  X := X
  d := discrete_dist
  is_dist := ⟨
    discrete_nneg, discrete_sep,
    discrete_symm, discrete_ineq
  ⟩

end Discrete

-- 5.
variable {A : Set α} {d : α → α → ℝ}

lemma induite_dist (h : A ⊆ X) (h' : estDistance X d) : estDistance A d := by
  rcases h' with ⟨nneg, sep, symm, ineq⟩; constructor
  · case nneg => intro x hx y hy; apply nneg x (h hx) y (h hy)
  · case sep => intro x hx y hy; apply sep x (h hx) y (h hy)
  · case symm => intro x hx y hy; apply symm x (h hx) y (h hy)
  · case ineq => intro x hx y hy z hz; apply ineq x (h hx) y (h hy) z (h hz)

def Induite {M : EspaceMetrique α} (h : A ⊆ M.X) : EspaceMetrique α where
  X := A
  d := M.d
  is_dist := induite_dist h M.is_dist

end Metrique

-- Définition 1.3.

namespace EspaceNorme
open VectorSpace

variable {K : Type*} [Field K] [ValuationField K] {E : Type*} [AddCommGroup E]
  [Module K E]

def nneg (N : E → ℝ) := ∀ x, N x ≥ 0

def definie (N : E → ℝ) := ∀ x, N x = 0 ↔ x = 0

def homogen (N : E → ℝ) := ∀ x, ∀ a : K, N (a • x) = |a| * N x

def ineq (N : E → ℝ) := ∀ x y, N (x + y) ≤ N x + N y

structure estNorme (N : E → ℝ) where
  nneg : nneg N
  definie : definie N
  homogen : homogen (K := K) N
  ineq : ineq N

class EspaceNorme' (E : Type*) where
  norm : E → ℝ

scoped notation "‖"u"‖" => EspaceNorme'.norm u

class EspaceVecNorme (K : Type*) [Field K] [ValuationField K] (E : Type*)
  [AddCommGroup E] extends Module K E where
  norm : E → ℝ
  is_norm : estNorme (K := K) norm

instance [V : EspaceVecNorme K E] : EspaceNorme' E where


-- Proposition 1.4.

open Metrique

theorem dist_of_norme (K : Type*) [Field K] [ValuationField K] (E : Type*)
  [AddCommGroup E] [V : EspaceVecNorme K E] :
  let d : E → E → ℝ := x ↦ y ↦ ‖x - y‖; estDistance E↑ d := by
  rcases V.is_norm with ⟨nneg, defi, homo, ineq⟩; constructor
  · case nneg => intro x _ y _; apply nneg
  · case sep => intro x _ y _; rw [defi, sub_eq_zero]
  · case symm => intro x _ y _; dsimp; rw [←neg_sub]
                 rw [←neg_one_smul K, homo, abs_neg_one, one_mul]
  · case ineq => intro x _ y _ z _; dsimp
                 have eq : x - z = (x - y) + (y - z) := by abel
                 rw [eq]; apply ineq

--instance [V : EspaceVecNorme K E] : Coe E (EspaceMetrique E) := fromNorm

end EspaceNorme
