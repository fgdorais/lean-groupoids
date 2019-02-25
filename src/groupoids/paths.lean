/-
Copyright © 2019 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .basic

structure {u v} path {α : Type u} {γ : α → α → Type v} (Γ : groupoid γ) : Type (max u v) := (cod dom : α) (map : γ cod dom)
attribute [pp_using_anonymous_constructor] path

namespace path
variables {α : Type*} {γ : α → α → Type*} (Γ : groupoid γ)

@[reducible, pattern]
definition make {x y : α} (g : γ x y) : path Γ := {cod := x, dom := y, map := g}

definition id (x : α) : path Γ := path.make Γ (Γ.id x) 

definition inv (p : path Γ) : path Γ := path.make Γ (Γ.inv p.map)

definition comp : Π (p q : path Γ), p.dom = q.cod → path Γ
| (path.make _ g) (path.make _ h) rfl := path.make Γ (Γ.comp g h)

definition pcomp [decidable_eq α] (p q : path Γ) : option (path Γ) :=
if H : p.dom = q.cod 
then some (path.comp Γ p q H)
else none

end path

definition path_state {α : Type*} {γ : α → α → Type*} (Γ : groupoid γ) := list (path Γ)

namespace path_state
variables {α : Type*} {γ : α → α → Type*} {Γ : groupoid γ} [da : decidable_eq α]
include da

definition rep (x : α) : path_state Γ → psigma (λ y, γ y x)
| [] := ⟨x, Γ.id x⟩
| (p::ps) := 
  if H : p.dom = x 
  then ⟨p.cod, eq.rec_on H p.map⟩
  else rep ps

definition remap (r : path Γ) : path_state Γ → path_state Γ
| [] := []
| (p::ps) := 
  if H : r.dom = p.cod 
  then path.comp Γ r p H :: ps
  else p :: ps

definition intro_ (r : path Γ) (ps : path_state Γ) : path_state Γ :=
let ⟨x, g⟩ := ps.rep r.dom in
r :: ps.remap (path.make Γ (Γ.comp r.map (Γ.inv g)))

definition intro (r : path Γ) (ps : path_state Γ) : path_state Γ :=
let ⟨z, g⟩ := ps.rep r.cod in
ps.intro_ (path.make Γ (Γ.comp g r.map))

definition find (x y : α) (ps : path_state Γ) : option (γ x y) :=
let ⟨x, g⟩ := ps.rep x in
let ⟨y, h⟩ := ps.rep y in
if H : x = y
then some (Γ.hcomp H (Γ.inv g) h)
else none

end path_state
