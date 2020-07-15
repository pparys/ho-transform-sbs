Require Import Program.

Definition type_cast {T1 T2 : Set} (H : T1 = T2) (x : T1) : T2 := eq_rect T1 (fun T3 : Set => T3) x T2 H.
Definition type_castT {T1 T2 : Type} (H : T1 = T2) (x : T1) : T2 := eq_rect T1 (fun T3 : Type => T3) x T2 H.

Lemma type_cast_type_cast_is_id A B (c1 : A = B) (c2 : B = A) x : type_cast c1 (type_cast c2 x) = x.
  dependent destruction c1.
  dependent destruction c2.
  auto.
Qed.

Lemma type_cast_invariance {A B} (eq1 eq2 : A = B) x : type_cast eq1 x = type_cast eq2 x.
  dependent destruction eq1.
  dependent destruction eq2.
  auto.
Qed.
