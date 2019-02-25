/-
Copyright © 2019 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import .groupoids.paths

namespace tactic

meta def match_ne' : expr → tactic (expr × expr)
| `(%%a ≠ %%b) := return (a,b)
| `(¬ %%a = %%b) := return (a,b)
| _ := failed

meta def eq_groupoid : groupoid (λ x y : expr, tactic expr) :=
{ id := mk_eq_refl
, inv := λ _ _ g, g >>= mk_eq_symm
, comp := λ _ _ _ g h, g >>= λ g, h >>= λ h, mk_eq_trans g h
}

meta def eq_state := path_state eq_groupoid

meta def eq_gather : list expr → tactic eq_state
| [] := return []
| (e :: es) :=
  do {
    `(%%a = %%b) ← infer_type e,
    eq_gather es >>= λ ps, return $ path_state.intro (path.mk eq_groupoid a b (return e)) ps
  } <|> eq_gather es

meta def eq_find (eqs : eq_state) : expr → expr → tactic expr := 
λ a b, eqs.find a b >>= λ e, e

meta def eq_solve (eqs : eq_state) : tactic unit :=
do {
  `(%%a = %%b) ← target,
  eq_find eqs a b >>= exact
}

meta def eq_rewrite : eq_state → tactic unit
| [] := skip
| (p :: ps) := repeat (p.map >>= λ e, rewrite_target e {symm:=tt}) >> eq_rewrite ps

meta def eq_contra (eqs : eq_state) : list expr → tactic unit
| [] := failed
| (h :: hs) :=
  do {
    (a,b) ← infer_type h >>= match_ne',
    e ← eq_find eqs a b,
    to_expr ``(absurd %%e %%h) >>= exact
  } <|> eq_contra hs

meta def eq_path_to_string : path eq_groupoid → tactic string
| ⟨_,a,b,e⟩ := e >>= λ e, return $ to_string a ++ " = " ++ to_string b ++ " := " ++ to_string e

meta def eq_state_to_string : eq_state → tactic string
| [] := return ""
| (p :: ps) := eq_path_to_string p >>= λ s, eq_state_to_string ps >>= λ t, return $ s ++ "; " ++ t

meta def eq_trace (eqs : eq_state) : tactic unit :=
eq_state_to_string eqs >>= trace

meta def interactive.eq_trace : tactic unit := 
local_context >>= eq_gather >>= eq_trace

meta def interactive.eq_solve : tactic unit := 
local_context >>= eq_gather >>= eq_solve

meta def interactive.eq_rewrite : tactic unit := 
local_context >>= eq_gather >>= eq_rewrite

meta def interactive.eq_contradiction : tactic unit :=
do {
  by_contradiction,
  ctx ← local_context,
  eqs ← eq_gather ctx,
  eq_contra eqs ctx
}

end tactic