Require Import List.
Require Import Program.

Lemma exists_Forall2_fw A B (R : A -> B -> Prop) x1 l1 l2 : In x1 l1 -> Forall2 (fun x1 x2 => R x1 x2) l1 l2 ->
    exists x2, R x1 x2 /\ In x2 l2.
  revert l2.
  induction l1.
    easy.
  destruct l2.
    easy.
  intros.
  dependent destruction H0.
  destruct H.
    exists b.
    split.
      rewrite <- H.
      auto.
    left.
    auto.
  destruct (IHl1 l2); auto.
  exists x.
  destruct H2.
  split.
    auto.
  right.
  auto.
Qed.

Lemma exists_Forall2_bw A B (R : A -> B -> Prop) x2 l1 l2 : In x2 l2 -> Forall2 (fun x1 x2 => R x1 x2) l1 l2 ->
    exists x1, R x1 x2 /\ In x1 l1.
  revert l1.
  induction l2.
    easy.
  destruct l1.
    easy.
  intros.
  dependent destruction H0.
  destruct H.
    exists a0.
    split.
      rewrite <- H.
      auto.
    left.
    auto.
  destruct (IHl2 l1); auto.
  exists x.
  destruct H2.
  split.
    auto.
  right.
  auto.
Qed.

Lemma Forall2_map_com A B C D (R : C -> D -> Prop) (F1 : A -> C) (F2 : B -> D) l1 l2 :
    Forall2 R (map F1 l1) (map F2 l2) <-> Forall2 (fun x1 x2 => R (F1 x1) (F2 x2)) l1 l2.
  split; intro.
    dependent induction H.
      destruct l1; try easy.
      destruct l2; try easy.
    destruct l1; try easy.
    destruct l2; try easy.
    simplify_eq x1.
    simplify_eq x.
    intros.
    apply Forall2_cons.
      rewrite <- H1.
      rewrite <- H3.
      auto.
    auto.
  dependent induction H.
    apply Forall2_nil.
  apply Forall2_cons; auto.
Qed.

Lemma Forall2_self A (R : A -> A -> Prop) l : (forall x, In x l -> R x x) -> Forall2 (fun x1 x2 => R x1 x2) l l.
  rewrite <- Forall_forall.
  induction 1.
    easy.
  apply Forall2_cons; easy.
Qed.

Lemma Forall2_map A B C (R : B -> C -> Prop) (F1 : A -> B) (F2 : A -> C) l :
    (forall x, In x l -> R (F1 x) (F2 x)) -> Forall2 R (map F1 l) (map F2 l).
  rewrite <- Forall_forall.
  intro.
  dependent induction H.
    apply Forall2_nil.
  apply Forall2_cons; auto.
Qed.

Lemma repeat_app_com A (x : A) n1 n2 : repeat x n1 ++ repeat x n2 = repeat x (n1 + n2).
  induction n1; auto.
  simpl.
  rewrite IHn1.
  auto.
Qed.
