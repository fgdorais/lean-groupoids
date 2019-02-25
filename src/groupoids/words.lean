/-
Copyright © 2019 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

namespace groupoid
universes u v
variables {α : Type u} (γ : α → α → Sort v)

inductive expr : α → α → Sort (max (u+1) v)
| id {} (x : α) : expr x x
| inv {x y : α} : expr x y → expr y x
| comp {x y z : α} : expr x y → expr y z → expr x z
| intro {x y : α} : γ x y → expr x y

inductive word : α → α → Sort (max (u+1) v)
| id {} (x : α) : word x x
| gapp {x y z : α} : γ x y → word y z → word x z
| iapp {x y z : α} : γ y x → word y z → word x z

namespace word
variable {γ}

definition to_expr : Π {x y : α}, word γ x y → expr γ x y
| _ _ (word.id _) := expr.id _
| _ _ (word.gapp g p) := expr.comp (expr.intro g) p.to_expr
| _ _ (word.iapp g p) := expr.comp (expr.inv (expr.intro g)) p.to_expr

definition comp : Π {x y z : α}, word γ x y → word γ y z → word γ x z
| _ _ _ (word.id _) q := q
| _ _ _ (word.gapp g p) q := word.gapp g (comp p q)
| _ _ _ (word.iapp g p) q := word.iapp g (comp p q)

definition inv : Π {x y : α}, word γ x y → word γ y x
| _ _ (word.id _) := word.id _
| _ _ (word.gapp g p) := word.comp (inv p) (word.iapp g (word.id _))
| _ _ (word.iapp g p) := word.comp (inv p) (word.gapp g (word.id _))

definition eval (Γ : groupoid γ) : Π {x y : α}, word γ x y → γ x y
| _ _ (word.id _) := Γ.id _
| _ _ (word.gapp g p) := Γ.comp g (eval p)
| _ _ (word.iapp g p) := Γ.comp (Γ.inv g) (eval p)

lemma eval_comp {Γ : groupoid γ} [is_lawful Γ] : ∀ {x y z} (p : word γ x y) (q : word γ y z), word.eval Γ (word.comp p q) = Γ.comp (p.eval Γ) (q.eval Γ)
| _ _ _ (word.id _) q :=
  begin
  dunfold word.comp,
  dunfold word.eval,
  rw [is_lawful.id_comp],
  end
| x y z (word.gapp g p) q :=
  begin
  dunfold word.comp,
  dunfold word.eval,
  rw [eval_comp],
  rw [comp_assoc],
  end
| _ _ _ (word.iapp g p) q :=
  begin
  dunfold word.comp,
  dunfold word.eval,
  rw [eval_comp],
  rw [comp_assoc],
  end

lemma eval_inv {Γ : groupoid γ} [is_lawful Γ] : ∀ {x y} (p : word γ x y), word.eval Γ p.inv = Γ.inv (p.eval Γ)
| _ _ (word.id _) :=
  begin
  dunfold word.inv,
  dunfold word.eval,
  rw [inv_of_id],
  end
| _ _ (word.gapp g p) :=
  begin
  dunfold word.inv,
  rw [eval_comp],
  dunfold word.eval,
  rw [eval_inv],
  rw [inv_of_comp],
  rw [comp_id],
  end
| _ _ (word.iapp g p) :=
  begin
  dunfold word.inv,
  rw [eval_comp],
  dunfold word.eval,
  rw [eval_inv],
  rw [inv_of_comp],
  rw [comp_id],
  rw [inv_of_inv],
  end

inductive equiv : Π {x y : α}, word γ x y → word γ x y → Sort (max (u+1) v)
| id (x : α) : equiv (word.id x) (word.id x)
| gapp {x y z : α} (g : γ x y) {p q : word γ y z} : equiv p q → equiv (word.gapp g p) (word.gapp g q)
| iapp {x y z : α} (g : γ y x) {p q : word γ y z} : equiv p q → equiv (word.iapp g p) (word.iapp g q)
| inv_app {x y z : α} (g : γ x y) {p q : word γ y z} : equiv p q → equiv (word.iapp g (word.gapp g p)) q
| app_inv {x y z : α} (g : γ y x) {p q : word γ y z} : equiv p q → equiv (word.gapp g (word.iapp g p)) q
| euclid {x y : α} (p q r : word γ x y) : equiv p q → equiv p r → equiv q r

namespace equiv

lemma refl : Π {x y : α} (p : word γ x y), equiv p p
| _ _ (word.id _) := equiv.id _
| _ _ (word.gapp _ p) := equiv.gapp _ (refl p)
| _ _ (word.iapp _ p) := equiv.iapp _ (refl p)

lemma symm {x y : α} (p q : word γ x y) : equiv p q → equiv q p :=
λ H, equiv.euclid p q p H (equiv.refl p)

lemma trans {x y : α} (p q r : word γ x y) : equiv p q → equiv q r → equiv p r :=
λ H₁ H₂, equiv.euclid q p r (equiv.symm p q H₁) H₂

variable (γ)

instance to_setoid (x y : α) : setoid (word γ x y) :=
{ r := λ p q, nonempty (equiv p q)
, iseqv := mk_equivalence _
  (λ p, nonempty.intro (equiv.refl p))
  (λ p q H, nonempty.elim H (λ H, nonempty.intro (equiv.symm p q H)))
  (λ p q r H₁ H₂, nonempty.elim H₁ (λ H₁, nonempty.elim H₂ (λ H₂, nonempty.intro (equiv.trans p q r H₁ H₂))))
}

definition quotient (x y : α) : Sort (max (u+1) v) := quotient (equiv.to_setoid γ x y)

end equiv

end word

namespace expr
variables {γ}

definition to_word : Π {x y : α}, expr γ x y → word γ x y
| _ _ (expr.id _) := word.id _
| _ _ (expr.inv e) := word.inv e.to_word
| _ _ (expr.comp e f) := word.comp e.to_word f.to_word
| _ _ (expr.intro g) := word.gapp g (word.id _)

definition eval (Γ : groupoid γ) : Π {x y : α}, expr γ x y → γ x y
| _ _ (expr.id x) := Γ.id x
| _ _ (expr.inv g) := Γ.inv (eval g)
| _ _ (expr.comp g h) := Γ.comp (eval g) (eval h)
| _ _ (expr.intro g) := g

end expr

section eval
variables {γ} {Γ : groupoid γ}

lemma word_eval_eq_expr_eval : ∀ {x y} (p : word γ x y), p.eval Γ = p.to_expr.eval Γ
| _ _ (word.id _) := rfl
| _ _ (word.gapp _ _) :=
  begin
  dunfold word.eval,
  dunfold word.to_expr,
  dunfold expr.eval,
  rw [word_eval_eq_expr_eval],
  end
| _ _ (word.iapp _ _) :=
  begin
  dunfold word.eval,
  dunfold word.to_expr,
  dunfold expr.eval,
  rw [word_eval_eq_expr_eval],
  end

lemma eval_expr_eq_eval_word [is_lawful Γ] : ∀ {x y} (e : expr γ x y), e.eval Γ = e.to_word.eval Γ
| _ _ (expr.id _) := rfl
| _ _ (expr.inv e) :=
  begin
  dunfold expr.eval,
  dunfold expr.to_word,
  rw [word.eval_inv],
  rw [eval_expr_eq_eval_word],
  end
| _ _ (expr.comp e f) :=
  begin
  dunfold expr.eval,
  dunfold expr.to_word,
  rw [word.eval_comp],
  rw [eval_expr_eq_eval_word],
  rw [eval_expr_eq_eval_word],
  end 
| _ _ (expr.intro g) := 
  begin
  dunfold expr.eval,
  dunfold expr.to_word,
  dunfold word.eval,
  rw [comp_id],
  end

end eval

namespace expr

inductive equiv : Π {x y : α}, expr γ x y → expr γ x y → Sort (max (u+1) v)
| eucl {x y : α} (f g h : expr γ x y) : equiv f g → equiv f h → equiv g h
| id {} (x : α) : equiv (expr.id x) (expr.id x)
| inv {x y : α} {g h : expr γ x y} : equiv g h → equiv (expr.inv g) (expr.inv h)
| comp {x y z : α} {g₁ h₁ : expr γ x y} {g₂ h₂ : expr γ y z} : equiv g₁ h₁ → equiv g₂ h₂ → equiv (expr.comp g₁ g₂) (expr.comp h₁ h₂)
| intro {x y : α} {g h : γ x y} : g = h → equiv (expr.intro g) (expr.intro h)

namespace equiv
variable {γ}

definition refl : Π {x y : α} (g : expr γ x y), equiv γ g g
| _ _ (expr.id _) := equiv.id _
| _ _ (expr.inv g) := equiv.inv (refl g)
| _ _ (expr.comp g h) := equiv.comp (refl g) (refl h)
| _ _ (expr.intro g) := equiv.intro rfl

definition symm {x y : α} {g h : expr γ x y} : equiv γ g h → equiv γ h g :=
λ H, equiv.eucl g h g H (equiv.refl g)

definition trans {x y : α} {f g h : expr γ x y} : equiv γ f g → equiv γ g h → equiv γ f h :=
λ H₁ H₂, equiv.eucl g f h (equiv.symm H₁) H₂

lemma eval (Γ : groupoid γ) : Π {x y : α} {g h : expr γ x y}, equiv γ g h → g.eval Γ = h.eval Γ
| _ _ (expr.intro _) (expr.intro _) (equiv.intro H) := eq.rec_on H rfl
| _ _ _ _ (equiv.id _) := rfl
| _ _ (expr.inv _) (expr.inv _) (equiv.inv H) :=
  begin
  dunfold expr.eval,
  apply congr_arg,
  exact eval H,
  end
| _ _ (expr.comp _ _) (expr.comp _ _) (equiv.comp H₁ H₂) :=
  begin
  dunfold expr.eval,
  apply congr,
  apply congr_arg,
  exact eval H₁,
  exact eval H₂,
  end
| _ _ _ _ (equiv.eucl f _ _ H₁ H₂) :=
  begin
  transitivity (f.eval Γ),
  symmetry,
  exact eval H₁,
  exact eval H₂,
  end

end equiv

end expr

end groupoid
