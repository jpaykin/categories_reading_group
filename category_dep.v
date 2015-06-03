Set Implicit Arguments.

Class Category (Object : Type) (Arrow : Type) :=
  { object : Object -> Prop; arrow : Arrow -> Prop;
    dom : Arrow -> Object; cod : Arrow -> Object;
    doms_exist : forall f (Hf : arrow f), object (dom f) /\ object (cod f);
    comp (f : Arrow) (g : Arrow) : Arrow;
    comp_exists : forall f g (Hf : arrow f) (Hg : arrow g) (H : dom g = cod f),
      arrow (comp g f) /\ dom (comp g f) = dom f /\ cod (comp g f) = cod g;
    I : Object -> Arrow;
    id_exists : forall A (HA : object A),
      arrow (I A) /\ dom (I A) = A /\ cod (I A) = A;
    comp_assoc : forall f g h (Hfg : cod f = dom g) (Hgh : cod g = dom h),
      comp h (comp g f) = comp (comp h g) f;
    unit_A : forall A f (H : dom f = A), comp f (I A) = f;
    unit_B : forall B f (H : cod f = B), comp (I B) f = f }.

Instance c1 : Category unit unit := {| object := fun _ => True;
  arrow := fun _ => True; dom := fun _ => tt; cod := fun _ => tt;
  comp := fun _ _ => tt; I := fun _ => tt |}.
Proof.
  - auto.
  - auto.
  - destruct A; auto.
  - auto.
  - destruct f; auto.
  - destruct f; auto.
Defined.

Definition empty_fun A (e : Empty_set) : A := match e with end.

Instance c0 : Category Empty_set Empty_set := {| object := empty_fun _;
  arrow := empty_fun _; dom := empty_fun _; cod := empty_fun _;
  comp := fun _ => empty_fun _; I := empty_fun _ |}.
Proof.
  - destruct f.
  - destruct f.
  - destruct A.
  - destruct f.
  - destruct f.
  - destruct f.
Defined.

Class Functor {C CA D DA} (CC : Category C CA) (CD : Category D DA) :=
{ omap : C -> D; amap : CA -> DA;
  preserves_dom : forall f, dom (amap f) = omap (dom f);
  preserves_cod : forall f, cod (amap f) = omap (cod f);
  preserves_id : forall a, amap (I a) = I (omap a);
  preserves_comp : forall f g, amap (comp g f) = comp (amap g) (amap f) }.

Instance id_functor `(C : Category) : Functor C C :=
  {| omap := @id _; amap := @id _ |}.
Proof.
  - auto.
  - auto.
  - auto.
  - auto.
Defined.

Instance comp_functor `{C : Category} `{D : Category} `{E : Category}
  (G : Functor D E) (F : Functor C D) : Functor C E :=
  {| omap := fun c => omap (omap c); amap := fun a => amap (amap a) |}.
Proof.
  - intro; repeat rewrite preserves_dom; auto.
  - intro; repeat rewrite preserves_cod; auto.
  - intro; repeat rewrite preserves_id; auto.
  - intros; repeat rewrite preserves_comp; auto.
Defined.

Section Cayley.

  Context `(c : Category).

  Definition CObj := Arrow -> Prop.
  Definition CObj_of (A : Object) (f : Arrow) := arrow f /\ cod f = A.

  Inductive CArrow := CA (A : CObj) (B : CObj) : (Arrow -> Arrow) -> CArrow.
  Definition is_CArrow_of (g : Arrow) (gb : CArrow) :=
    exists h, CA (CObj_of (dom g)) (CObj_of (cod g)) h = gb /\
    forall f (Hf : arrow f) (H : dom g = cod f), h f = comp g f.

  Definition compose {A B C} (g : B -> C) (f : A -> B) x := g (f x).

  Lemma cong : forall {A B} (f g : A -> B) x, f = g -> f x = g x.
  Proof. intros; rewrite H; auto. Qed.

  Lemma CObj_inj : forall A B (HA : object A), CObj_of A = CObj_of B -> A = B.
  Proof.
    unfold CObj_of; intros.
    generalize (cong (I A) H); intro Heq.
    generalize (id_exists _ HA); intros [? [? Hcod]].
    assert (arrow (I A) /\ cod (I A) = A) as HI by auto.
    rewrite Heq, Hcod in HI; destruct HI; auto.
  Qed.

  Definition Cayley_comp gb fb := match gb, fb with
    CA B C hg, CA A B' hf => CA A C (compose hg hf) end.

(*  Require Import FunctionalExtensionality.*)

  Instance Cayley : Category CObj CArrow :=
    {| object := fun Ab => exists A, object A /\ Ab = CObj_of A;
       arrow := fun gb => exists g, arrow g /\ is_CArrow_of g gb;
       dom := fun gb => match gb with CA A _ _ => A end;
       cod := fun gb => match gb with CA _ B _ => B end;
       comp := Cayley_comp;
       I := fun A => CA A A (fun x => x) |}.
  Proof.
    - destruct f; intros [g [Hg Hf]].
      unfold is_CArrow_of in Hf; destruct Hf as [h [Heq Hh]]; inversion Heq;
        subst.
      generalize (doms_exist _ Hg); intros [? ?]; split; eauto.
    - destruct f as [A B hf], g as [? C hg]; intros; subst; split; auto.
      destruct Hf as [f0 [Hf0 Hf]], Hg as [g0 [Hg0 Hg]].
      unfold is_CArrow_of in *; destruct Hf as [? [Heqf Hhf]],
        Hg as [? [Heqg Hhg]]; inversion Heqf; inversion Heqg; subst;
        clear Heqf Heqg.
      assert (dom g0 = cod f0) as Hdoms.
      { apply CObj_inj; auto; apply doms_exist; auto. }
      generalize (comp_exists _ _ Hf0 Hg0 Hdoms); intros [Harr [Hdom Hcod]].
      exists (comp g0 f0); rewrite Hdom, Hcod; split; auto.
      unfold Cayley_comp; eexists; split; eauto; intros.
      unfold compose; rewrite Hhg; rewrite Hhf; auto.
      + rewrite comp_assoc; auto.
      + apply comp_exists; auto.
      + generalize (comp_exists _ _ Hf Hf0 H); intros [? [? Hcod']];
          rewrite Hcod'; auto.
    - intro; split; auto.
      destruct HA as [A0 [HA0 ?]]; subst.
      generalize (id_exists _ HA0); intros [? [Hdom Hcod]].
      exists (I A0); unfold is_CArrow_of; split; auto.
      rewrite Hdom, Hcod.
      eexists; split; eauto; intros.
      rewrite unit_B; auto.
    - destruct f, g, h; auto.
    - destruct f; intros; subst; auto.
    - destruct f; intros; subst; auto.
  Qed.

End Cayley.