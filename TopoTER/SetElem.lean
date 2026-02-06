import Mathlib.Data.Set.Basic

namespace TER

variable {α β : Type u} {S : Set α}

@[coe] def coe_type : α → @Set.univ α := fun e => ⟨e, Set.mem_univ e⟩
@[simp, norm_cast] lemma coe_coe_type (e : α) : ↑(coe_type e) = e := by rfl

instance [HAdd α α α] : HAdd S S α where
  hAdd := fun x => fun y => (x : α) + (y : α)

instance [HSub α α α] : HSub S S α where
  hSub := fun x => fun y => (x : α) - (y : α)

instance [HMul α α α] : HMul S S α where
  hMul := fun x => fun y => (x : α) * (y : α)

instance [HDiv α α α] : HDiv S S α where
  hDiv := fun x => fun y => (x : α) / (y : α)

class TypeLE (α : Type _) (β : Type _) where
  le : α → β → Prop

class TypeLT (α : Type _) (β : Type _) where
  lt : α → β → Prop

instance [LE α] : TypeLE α α := ⟨LE.le⟩
instance [LT α] : TypeLT α α := ⟨LT.lt⟩

instance {β} [LE α] [Coe β α] : TypeLE α β where
  le := fun x => fun y => LE.le x (y : α)

instance {β} [LT α] [Coe β α] : TypeLT α β where
  lt := fun x => fun y => LT.lt x (y : α)

instance [LE α] : TypeLE S α where
  le := fun x => fun y => LE.le (x : α) y

instance [LT α] : TypeLT S α where
  lt := fun x => fun y => LT.lt (x : α) y

scoped syntax (name := setfun) term " ↦ " term : term
macro_rules (kind := setfun)
  | `($x ↦ $desc) => `(fun $x => $desc)

scoped infix:50 (priority := high) " ≤ " => TypeLE.le

scoped infix:50 (priority := high) " < " => TypeLT.lt

variable {x y : S} {z : α}

@[simp] lemma elem_eq : x = y ↔ x.val = y.val := by rw [SetCoe.ext_iff]

@[simp] lemma elem_le [LE α] : x ≤ z ↔ x.val ≤ z := by rfl

@[simp] lemma elem_lt [LT α] : x < z ↔ x.val < z := by rfl

@[simp] lemma elem_add [HAdd α α α] : (@HAdd.hAdd S S α) x y = x.val + y.val := by rfl

@[simp] lemma elem_sub [HSub α α α] : (@HSub.hSub S S α) x y = x.val - y.val := by rfl

@[simp] lemma elem_mul [HMul α α α] : (@HMul.hMul S S α) x y = x.val * y.val := by rfl

@[simp] lemma elem_div [HDiv α α α] : (@HDiv.hDiv S S α) x y = x.val / y.val := by rfl

-- une version du simplificateur restreinte aux lemmes définies ici:
syntax (name := cleanup) "cleanup" : tactic
macro_rules (kind := cleanup)
  | `(tactic| cleanup) => `(tactic| simp only [coe_type, elem_eq, elem_le, elem_lt,
                                               elem_add, elem_sub, elem_mul, elem_div])

end TER
