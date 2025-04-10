(* In this file we provide a solution to the exercise in Coq based
 on a definition of PreImage using an inductive type and part of the standard library. *)

Require Import Coq.Sets.Image.

Section Preimage.
  Variables U V : Type.

  Inductive Pre (Y:Ensemble V) (f:U -> V) : Ensemble U :=
    Pre_intro : forall y:V, In _ Y y -> forall x:U, y = f x -> In _ (Pre Y f) x.

  Lemma Pre_def :
    forall (Y:Ensemble V) (f:U -> V) (x:U), In _ Y (f x) -> In _ (Pre Y f) x.
  Proof.
    intros Y f x H.
    apply Pre_intro with (f x).
    - exact H.
    - reflexivity.
  Qed.

  Lemma In_Pre_elim :
    forall (B:Ensemble V) (f:U -> V),
      forall x:U, In _ (Pre B f) x -> In _ B (f x).
  Proof.
    intros B f x H.
    destruct H as [* H0]; subst.
    exact H0.
  Qed.

End Preimage.

#[global]
Hint Resolve Pre_def : sets.

Section Exercise.

  Variable (A B: Type).

  Theorem subset_preimage_image {f: A -> B} (C:Ensemble A):
    Included _ C (Pre _ _ (Im _ _ C f) f).
  Proof.
    intros x hx.
    apply Pre_def.
    apply Im_def.
    exact hx.
  Qed.

  Theorem preimage_image_subset {f: A -> B} (C:Ensemble A) :
    injective _ _ f -> Included _ (Pre _ _ (Im _ _ C f) f) C.
  Proof.
    intros hf x hx.
    apply In_Pre_elim in hx.
    apply In_Image_elim in hx.
    - exact hx.
    - exact hf.
  Qed.

  Theorem eq_preimage_image {f: A -> B} (C:Ensemble A) :
    injective _ _ f -> Pre _ _ (Im _ _ C f) f = C.
  Proof.
    intro hf.
    apply Extensionality_Ensembles.
    split.
    - apply (preimage_image_subset _ hf).
    - apply subset_preimage_image.
  Qed.

End Exercise.
