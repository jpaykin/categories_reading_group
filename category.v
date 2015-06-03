(* My dependently-typed formulation of categories. -WM *)

Set Implicit Arguments.

Class Category := { object : Type; arrow : object -> object -> Type;
   comp : forall a b c, arrow b c -> arrow a b -> arrow a c;
   id (a : object) : arrow a a;
   associativity a b c d (f : arrow a b) (g : arrow b c) (h : arrow c d) :
     comp h (comp g f) = comp (comp h g) f;
   unit_r a b (f : arrow a b) : comp f (id a) = f;
   unit_l a b (f : arrow a b) : comp (id b) f = f }.
Arguments comp {Category} [a] [b] [c] _ _.

(* A couple of simple instances. *)
Instance c1 : Category := {| object := unit; arrow := fun x y => unit;
  comp := fun _ _ _ _ _ => tt; id := fun _ => tt |}.
Proof.
  - auto.
  - destruct f; auto.
  - destruct f; auto.
Defined.

(* This works very badly if this definition isn't made in advance. *)
Definition arrow2 (x y : bool) :=
  if x then unit else if y then Empty_set else unit.

Instance c2 : Category := {| object := bool; arrow := arrow2;
  comp := fun a b c =>
    match a, b with
    | true, false => fun g f => match c with _ => f end
    | false, true => fun g f => match f with end
    | _, _ => fun g f => g
    end; id := fun a => match a with true | false => tt end |}.
Proof.
  - intros; destruct a, b, c, f; auto.
    destruct h; auto.
  - destruct a; auto.
  - destruct a, b, f; auto.
Defined.

Instance c0 : Category := {| object := Empty_set; arrow := fun _ _ => Empty_set;
  comp := fun a _ _ _ _ => match a with end; id := fun a => match a with end |}.
Proof.
  - intros; inversion a.
  - intros; inversion a.
  - intros; inversion a.
Defined.

(* Functors *)
Class Functor (C : Category) (D : Category) := { omap : @object C -> @object D;
  amap : forall a b, arrow a b -> arrow (omap a) (omap b);
  (* dependent types make the first condition implicit! *)
  preserves_id : forall a, amap _ _ (id a) = id (omap a);
  preserves_comp : forall a b c (f : arrow a b) (g : arrow b c),
    amap _ _ (comp g f) = comp (amap _ _ g) (amap _ _ f) }.
Arguments amap {C} {D} {Functor} [a] [b] _.

Instance id_functor C : Functor C C :=
  {| omap := fun o => o; amap := fun _ _ a => a |}.
Proof.
  - auto.
  - auto.
Defined.

Instance comp_functor {C D E : Category} (F : Functor C D) (G : Functor D E)
  : Functor C E :=
  {| omap := fun c => omap (omap c); amap := fun _ _ a => amap (amap a) |}.
Proof.
  - intro; repeat rewrite preserves_id; auto.
  - intros; repeat rewrite preserves_comp; auto.
Defined.

Definition isomorphism a b (f : arrow a b) :=
  exists g, comp g f = id a /\ comp f g = id b.

Lemma inv_unique : forall a b f g g', comp g f = id a /\ comp f g = id b /\
  comp g' f = id a /\ comp f g' = id b -> g = g'.
Proof.
  intros ? ? ? ? ? [Hga [Hgb [Hg'a Hg'b]]].
  rewrite <- unit_l.
  rewrite <- Hga.
  rewrite <- associativity.
  rewrite Hg'b.
  rewrite unit_r; auto.
Qed.