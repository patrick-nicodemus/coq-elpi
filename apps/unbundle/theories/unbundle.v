From elpi Require Import elpi.

Elpi Db record.expand.db lp:{{
  % This data base will contain all the expansions performed previously.
  % For example, if f was expandded to f1 we would have this clause:

  % expand (app[f, R | L]) (app[f1, V1, V2 | L1]) :-
  %   expand R (app[k, V1, V2]), std.map L expand L1.

% [expand A B] can be used to perform a replacement, eg
%   (expand (const "foo") (const "bar") :- !) ==> expand A B
pred expand i:term, o:term.

}}.

Elpi Accumulate record.expand.db lp:{{
shorten std.{ map }.

:name "expand:start"
expand (global _ as C) C :- !.
expand (pglobal _ _ as C) C :- !.
expand (sort _ as C) C :- !.
expand (fun N T F) (fun N T1 F1) :- !,
  expand T T1, pi x\ expand x x ==> expand (F x) (F1 x).
expand (let N T B F) (let N T1 B1 F1) :- !,
  expand T T1, expand B B1, pi x\ expand x x ==> expand (F x) (F1 x).
expand (prod N T F) (prod N T1 F1) :- !,
  expand T T1, (pi x\ expand x x ==> expand (F x) (F1 x)).
expand (app L) (app L1) :- !, map L expand L1.
expand (fix N Rno Ty F) (fix N Rno Ty1 F1) :- !,
  expand Ty Ty1, pi x\ expand x x ==> expand (F x) (F1 x).
expand (match T Rty B) (match T1 Rty1 B1) :- !,
  expand T T1, expand Rty Rty1, map B expand B1.
expand (primitive _ as C) C :- !.
}}.

From elpi.apps.unbundle.elpi Extra Dependency "unbundle.elpi" as unbundle.
Elpi Command record.expand.
Elpi Accumulate Db record.expand.db.
Elpi Accumulate File unbundle.

Set Universe Polymorphism.
Record r := { T :> Type; X := T; op : T -> X -> bool }.

Definition f b (t : r) (q := negb b) := fix rec (l1 l2 : list t) :=
  match l1, l2 with
  | nil, nil => b
  | cons x xs, cons y ys => andb (op _ x y) (rec xs ys)
  | _, _ => q
  end.

Elpi record.expand r f "expanded_". 
Print f.
Print expanded_f.

(* so that we can see the new "expand" clause *)
Elpi Print record.expand "elpi_examples/record.expand".

Definition g t l s h := (forall x y, op t x y = false) /\ f true t l s = h.

Elpi record.expand r g "expanded_".
Print expanded_g.