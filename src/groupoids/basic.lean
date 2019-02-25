/-
Copyright © 2019 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

structure {u v} groupoid_ {α : Type u} (γ : α → α → Sort v) : Sort (max (u+1) v)
structure {u v} groupoid {α : Type u} (γ : α → α → Sort v) extends groupoid_ γ : Sort (max (u+1) v) :=
(id (x : α) : γ x x)
(inv {x y : α} : γ x y → γ y x)
(comp {x y z : α} : γ x y → γ y z → γ x z)

definition groupoid.hid {α : Type*} {γ : α → α → Sort*} (Γ : groupoid γ) : Π {x y : α}, x = y → γ x y
| _ _ rfl := Γ.id _

definition groupoid.hcomp {α : Type*} {γ : α → α → Sort*} (Γ : groupoid γ) : Π {w x y z : α}, x = y → γ w x → γ y z → γ w z
| _ _ _ _ rfl g h := Γ.comp g h

class groupoid.is_lawful {α : Type*} {γ : α → α → Sort*} (Γ : groupoid γ) : Prop :=
(id_comp {x y : α} (g : γ x y) : Γ.comp (Γ.id x) g = g)
(comp_id {x y : α} (g : γ x y) : Γ.comp g (Γ.id y) = g)
(inv_comp {x y : α} (g : γ x y) : Γ.comp (Γ.inv g) g = Γ.id y)
(comp_inv {x y : α} (g : γ x y) : Γ.comp g (Γ.inv g) = Γ.id x)
(comp_assoc {w x y z : α} (f : γ w x) (g : γ x y) (h : γ y z) : Γ.comp (Γ.comp f g) h = Γ.comp f (Γ.comp g h))

namespace groupoid
variables {α : Type*} {γ : α → α → Sort*} (Γ : groupoid γ) [H : is_lawful Γ]
include H

lemma id_comp {x y : α} (g : γ x y) : Γ.comp (Γ.id x) g = g := is_lawful.id_comp Γ g

lemma comp_id {x y : α} (g : γ x y) : Γ.comp g (Γ.id y) = g := is_lawful.comp_id Γ g

lemma inv_comp {x y : α} (g : γ x y) : Γ.comp (Γ.inv g) g = Γ.id y := is_lawful.inv_comp Γ g

lemma comp_inv {x y : α} (g : γ x y) : Γ.comp g (Γ.inv g) = Γ.id x := is_lawful.comp_inv Γ g

lemma comp_assoc {w x y z : α} (f : γ w x) (g : γ x y) (h : γ y z) : Γ.comp (Γ.comp f g) h = Γ.comp f (Γ.comp g h) := is_lawful.comp_assoc Γ f g h

lemma comp_inv_cancel_left {x y z : α} (g : γ y x) (h : γ y z) : Γ.comp g (Γ.comp (Γ.inv g) h) = h :=
begin
rw [← comp_assoc],
rw [comp_inv],
rw [id_comp],
end

lemma inv_comp_cancel_right {x y z : α} (g : γ x y) (h : γ z y) : Γ.comp (Γ.comp g (Γ.inv h)) h = g :=
begin
rw [comp_assoc],
rw [inv_comp],
rw [comp_id],
end

lemma inv_comp_cancel_left {x y z : α} (g : γ x y) (h : γ y z) : Γ.comp (Γ.inv g) (Γ.comp g h) = h :=
begin
rw [← comp_assoc],
rw [inv_comp],
rw [id_comp],
end

lemma comp_inv_cancel_right {x y z : α} (g : γ x y) (h : γ y z) : Γ.comp (Γ.comp g h) (Γ.inv h) = g :=
begin
rw [comp_assoc],
rw [comp_inv],
rw [comp_id],
end

lemma eq_inv_of_comp_eq_id {x y : α} (g : γ x y) (h : γ y x) : Γ.comp g h = Γ.id x → g = Γ.inv h :=
begin
intro H,
transitivity Γ.comp g (Γ.comp h (Γ.inv h)),
rw [comp_inv],
rw [comp_id],
rw [← comp_assoc],
rw [H],
rw [id_comp],
end

lemma inv_eq_of_comp_eq_id {x y : α} (g : γ x y) (h : γ y x) : Γ.comp g h = Γ.id x → Γ.inv g = h :=
begin
intro H,
symmetry,
transitivity Γ.comp (Γ.inv g) (Γ.comp g h),
rw [← comp_assoc],
rw [inv_comp],
rw [id_comp],
rw [H],
rw [comp_id],
end

lemma inv_of_id {x : α} : Γ.inv (Γ.id x) = Γ.id x :=
begin
apply inv_eq_of_comp_eq_id,
rw [comp_id],
end

lemma inv_of_inv {x y : α} (g : γ x y) : Γ.inv (Γ.inv g) = g :=
begin
apply inv_eq_of_comp_eq_id,
rw [inv_comp],
end

lemma inv_of_comp {x y z : α} (g : γ x y) (h : γ y z): Γ.inv (Γ.comp g h) = Γ.comp (Γ.inv h) (Γ.inv g) :=
begin
apply inv_eq_of_comp_eq_id,
rw [← comp_assoc],
rw [comp_inv_cancel_right],
rw [comp_inv],
end

end groupoid
