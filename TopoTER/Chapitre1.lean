import TopoTER.Préliminaires

open TER

-- 1. Espaces métriques

namespace Metric

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

variable {α : Type*} {X : Set α}

def nneg (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y ≥ 0

def sep (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y = 0 ↔ x = y

def symm (X : Set α) (d : α → α → ℝ) := ∀ x y ∈ X, d x y = d y x

def ineq (X : Set α) (d : α → α → ℝ) := ∀ x y z ∈ X, d x z ≤ d x y + d y z

structure Distance (X : Set α) where
  dist : α → α → ℝ
  nneg : nneg X dist
  sep : sep X dist
  symm : symm X dist
  ineq : ineq X dist

structure MetricSpace (α : Type*) where
  X : Set α
  d : Distance X

-- Exemple 1.2.

-- 1.
def abs_dist : ℝ → ℝ → ℝ := x ↦ y ↦ |x - y|

lemma abs_nneg : nneg R abs_dist := by
  intro x _ y _; apply abs_nonneg

lemma abs_sep : sep R abs_dist := by
  intro x _ y _; unfold abs_dist; rw [abs_eq_zero, sub_eq_zero]

lemma abs_symm : symm R abs_dist := by
  intro x _ y _; unfold abs_dist; rw [abs_sub_comm]

lemma abs_ineq : ineq R abs_dist := by
  intro x _ y _ z _; unfold abs_dist; apply abs_sub_le

def r_usuelle : Distance R where
  dist := abs_dist
  nneg := abs_nneg
  sep := abs_sep
  symm := abs_symm
  ineq := abs_ineq

def R_usuelle : MetricSpace ℝ where
  X := R
  d := r_usuelle

-- 2.
section Complex
open Complex

noncomputable def module_dist : ℂ → ℂ → ℝ := x ↦ y ↦ ‖x - y‖

lemma module_nneg : nneg C module_dist := by
  intro x _ y _; apply norm_nonneg

lemma module_sep : sep C module_dist := by
  intro x _ y _; unfold module_dist; rw [norm_eq_zero, sub_eq_zero]

lemma module_symm : symm C module_dist := by
  intro x _ y _; unfold module_dist; rw [norm_symm, neg_sub]

lemma module_ineq : ineq C module_dist := by
  intro x _ y _ z _; unfold module_dist
  have eq : x - z = (x - y) + (y - z) := by ring
  rw [eq]; apply norm_ineq

noncomputable def c_usuelle : Distance C where
  dist := module_dist
  nneg := module_nneg
  sep := module_sep
  symm := module_symm
  ineq := module_ineq

noncomputable def C_usuelle : MetricSpace ℂ where
  X := C
  d := c_usuelle

end Complex

-- 3.
section Euclidean
open VectorSpace
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [R_Euclidean E]

noncomputable def euclid_dist : E → E → ℝ := x ↦ y ↦ √⟨x - y, x - y⟩

lemma euclid_nneg : nneg E** euclid_dist := by
  intro x _ y _; apply norm_nonneg

lemma euclid_sep : sep E** euclid_dist := by
  intro x _ y _; unfold euclid_dist; rw [←norm, norm_eq_zero, sub_eq_zero]

lemma euclid_symm : symm E** euclid_dist := by
  intro x _ y _; unfold euclid_dist; rw [←norm, ←norm, norm_symm, neg_sub]

lemma euclid_ineq : ineq E** euclid_dist := by
  intro x _ y _ z _; unfold euclid_dist; repeat rw [←norm]
  have eq : x - z = (x - y) + (y - z) := by abel
  rw [eq]; apply norm_ineq

noncomputable def euclid : Distance E** where
  dist := euclid_dist
  nneg := euclid_nneg
  sep := euclid_sep
  symm := euclid_symm
  ineq := euclid_ineq

noncomputable def Euclid : MetricSpace E where
  X := E**
  d := euclid

end Euclidean

-- 4.
open Classical in
noncomputable def discrete_dist : α → α → ℝ := x ↦ y ↦ ite (x = y) 0 1

lemma discrete_nneg : nneg X discrete_dist := by
  intro x _ y _; unfold discrete_dist; split
  · case isTrue => rfl
  · case isFalse => linarith

lemma discrete_sep : sep X discrete_dist := by
  intro x _ y _; unfold discrete_dist; split
  · case isTrue h => simp only [h]
  · case isFalse h => simp only [one_ne_zero, h]

lemma discrete_symm : symm X discrete_dist := by
  intro x _ y _; unfold discrete_dist; rw [@Eq.comm α]

open Classical in
lemma discrete_ineq : ineq X discrete_dist := by
  intro x h1 y h2 z h3; unfold discrete_dist; split
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

noncomputable def discrete (X : Set α) : Distance X where
  dist := discrete_dist
  nneg := discrete_nneg
  sep := discrete_sep
  symm := discrete_symm
  ineq := discrete_ineq

noncomputable def Discrete (X : Set α) : MetricSpace α where
  X := X
  d := discrete X

-- 5.
lemma induite_nneg {X : Set α} {X' : Set α} {d : α → α → ℝ} (h : X ⊆ X')
  (h' : nneg X' d) : nneg X d := by
  intro x hx y hy; apply h at hx; apply h at hy; apply h' x hx y hy

lemma induite_sep {X : Set α} {X' : Set α} {d : α → α → ℝ} (h : X ⊆ X')
  (h' : sep X' d) : sep X d := by
  intro x hx y hy; apply h at hx; apply h at hy; apply h' x hx y hy

lemma induite_symm {X : Set α} {X' : Set α} {d : α → α → ℝ} (h : X ⊆ X')
  (h' : symm X' d) : symm X d := by
  intro x hx y hy; apply h at hx; apply h at hy; apply h' x hx y hy

lemma induite_ineq {X : Set α} {X' : Set α} {d : α → α → ℝ} (h : X ⊆ X')
  (h' : ineq X' d) : ineq X d := by
  intro x hx y hy z hz; apply h at hx; apply h at hy; apply h at hz
  apply h' x hx y hy z hz

def induite {X : Set α} {X' : Set α} (h : X ⊆ X') (d : Distance X') :
  Distance X where
  dist := d.dist
  nneg := induite_nneg h d.nneg
  sep := induite_sep h d.sep
  symm := induite_symm h d.symm
  ineq := induite_ineq h d.ineq

def Induite {A : Set α} (M : MetricSpace α) (h : A ⊆ M.X) : MetricSpace α where
  X := A
  d := induite h M.d

end Metric
