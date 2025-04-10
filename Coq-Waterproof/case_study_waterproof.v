(* Example writen by Kelana Saint Marc. *)

Require Import Waterproof.AllTactics.
Require Import Waterproof.notations.notations.
Require Import Waterproof.load_database.RealsAndIntegers.
Require Import Waterproof.theory.analysis.sup_and_inf_new_definitions.

Definition Ens {E : Type} := E -> Prop.
Definition In {E : Type} (A :@Ens E) (x:E) := A x.
Notation "x ∈ A" := (In A x) (at level 60).

(* Inclusion relation *)
Definition incl {E: Type} (A B: Ens) :=
  ∀ x: E, x ∈ A → x ∈ B.
Notation "A ⊆ B" := (incl A B) (at level 80).

(* Image of a set by a function *)
Definition im {E F: Type} (f: E → F) (A: Ens): Ens :=
  fun (y: F) => ∃ x, x ∈ A ∧ y = f x.

(* Inverse image of a set by a function *)
Definition pre {E F: Type} (f: E → F) (B: Ens): Ens :=
  fun (x: E) => f x ∈ B.

(* Injective function *)
Definition injective {E F: Type} (f: E -> F) :=
  ∀ (x x': E), f x = f x' → x = x'.


Theorem direct_inclusion :
  forall {E F: Set} (f: E → F),
    ∀ A, A ⊆ pre f (im f A).
Proof.
Take E, F : Set.
Take f : (E → F).
Take A : ((@Ens)(E)).
Expand the definition of incl.
That is, write the goal as (for all x : E,
      x ∈ A
      ⇨ x
        ∈ (@pre)(E, F, f, 
        (@im)(E, F, f, A))).
Take x : E.
Assume that (x ∈ A) (H0).
Expand the definition of pre.
That is, write the goal as (x ∈ fun (x: E) => (f(x) ∈ (@im)(E, F, f, A))).
Expand the definition of In.
That is, write the goal as ((@im)(E, F, f, A, f(x))).
Expand the definition of im.
 That is, write the goal as (there exists x0 : E,
      x0 ∈ A ∧ f(x) = f(x0)).
Choose x0 := x.
We show both statements.
We conclude that (x0 ∈ A).
We conclude that (f(x) = f(x0)).
Qed.

Theorem reverse_inclusion :
  forall {E F: Set} (f: E -> F),
    injective f -> 
      forall A, incl (pre f (im f A)) A.
Proof.
Take E, F : Set.
Take f : (E → F).
Assume that ((@injective)(E, F, f)) (H0).
Take A : ((@Ens)(E)).
Expand the definition of incl.
That is, write the goal as (for all x : E,
      x ∈ (@pre)(E, F, f, (@im)(E, F, f, A))
      ⇨ x ∈ A).
Take x : E.
Assume that (x ∈ (@pre)(E, F, f, (@im)(E, F, f, A))) (H1).
Expand the definition of pre in (H1).
That is, write (H1) as (x ∈ (x) ↦ (f(x) ∈ (@im)(E, F, f, A))).
Expand the definition of In in (H1).
That is, write (H1) as ((@im)(E, F, f, A, f(x))).
Expand the definition of im in (H1).
That is, write (H1) as (there exists x0 : E,
                               x0 ∈ A ∧ f(x) = f(x0)).
Obtain x0 according to (H1), so for x0 : E it holds that (x0 ∈ A ∧ f(x) = f(x0)) (H2).
Because (H2) both (x0 ∈ A)(H21) and (f(x) = f(x0))(H22).
Expand the definition of injective in (H0).
That is, write (H0) as (for all x x' : E,
                               f(x) = f(x') ⇨ x = x').
By (H1) it holds that (f(x0) = f(x) ⇨ x0 = x)(H10).
We claim that (x=x0)(H3).
We conclude that (x=x0).
rewrite H3.
  We conclude that (x0 ∈ A).
Qed.






