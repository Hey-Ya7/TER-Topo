import «TER Topo».Préliminaires

-- 1. Espaces métriques

namespace Metric

-- 1.1. Définition, premiers exemples

-- Définition 1.1.

def sep {α} {X : Set α} (d : X → X → R₊) : Prop := ∀ x y, d x y = 0 ↔ x = y

def symm {α} {X : Set α} (d : X → X → R₊) : Prop := ∀ x y, d x y = d y x

def ineq {α} {X : Set α} (d : X → X → R₊) : Prop := ∀ x y z, d x z ≤ d x y + d y z

def isDistance {α} {X : Set α} (d : X → X → R₊) : Prop := sep d ∧ symm d ∧ ineq d

structure MetricSpace (α : Type) where
  X : Set α
  d : X → X → R₊
  is_dist : isDistance d

-- un constructeur plus pratique à utiliser:

structure isMetricSpace (α : Type) extends MetricSpace α where
  dist : X → X → ℝ
  dist_pos : ∀ x y, dist x y ≥ 0
  d := fun x => fun y => ⟨dist x y, dist_pos x y⟩

  dist_sep : sep d
  dist_symm : symm d
  dist_ineq : ineq d
  is_dist := And.intro dist_sep (And.intro dist_symm dist_ineq)

-- Exemple 1.2.

-- 1.
def R_usuelle : isMetricSpace ℝ where
  X := R
  dist := fun x => fun y => |x - y|
  dist_pos := by intro x y; exact abs_nonneg (x - y : ℝ)

  dist_sep := by {
    intro x y; simp [sub_eq_zero]
  }

  dist_symm := by {
    intro x y; simp [abs_sub_comm]
  }

  dist_ineq := by {
    intro x y z; simp [abs_sub_le]
  }

end Metric
