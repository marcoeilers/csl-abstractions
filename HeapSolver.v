Require Import HahnBase.
Require Import Heaps.
Require Import Permissions.
Require Import Prelude.


(** * Heap solver *)

(** This section contains tactics that provide more
    proof automation for working with heaps, in particular
    for doing proofs that involve heap (cell) validity
    and disjointness. *)

Module Type HeapSolver
  (domains : Domains)
  (heaps : Heaps domains).

Export domains heaps.


(** ** Permission heap cells *)

(** The following tactic, [phcsolve], gives some proof automation
    for simple (but often occuring) properties on validity
    and disjointness of permission heaps. *)

(** This tactic is defined simply as a table of patterns,
    and matching proofs for these patterns. *)

Ltac phcsolve :=
  clarify; match goal with
    | [|- phcValid PHCfree] => apply phcValid_free
    | [|- phcDisj PHCfree PHCfree] => by apply phcDisj_free_l, phcValid_free
    | [|- phcDisj ?x PHCfree] => apply phcDisj_free_l; phcsolve
    | [|- phcDisj PHCfree ?x] => apply phcDisj_free_r; phcsolve
    | [H: phcDisj ?x ?y |- phcDisj ?x ?y] => exact H
    | [H: phcDisj ?x ?y |- phcDisj ?y ?x] => symmetry; exact H
    | [H: phDisj ?x ?y |- phcDisj (?x ?v) (?y ?v)] => by apply H
    | [H: phDisj ?y ?x |- phcDisj (?x ?v) (?y ?v)] => symmetry; by apply H
    | [H1: phcDisj ?x ?y, H2: phcDisj (phcUnion ?x ?y) ?z |- phcDisj ?y ?z] => apply phcDisj_union_l with x; [exact H1|exact H2]
    | [H1: phcDisj ?y ?z, H2: phcDisj ?x (phcUnion ?y ?z) |- phcDisj ?x ?y] => apply phcDisj_union_r with z; [exact H1|exact H2]
    | [H1: phcDisj ?x ?y, H2: phcDisj (phcUnion ?x ?y) ?z |- phcDisj ?x (phcUnion ?y ?z)] => apply phcDisj_assoc_l; [exact H1|exact H2]
    | [H1: phcDisj ?y ?z, H2: phcDisj ?x (phcUnion ?y ?z) |- phcDisj (phcUnion ?x ?y) ?z] => apply phcDisj_assoc_r; [exact H1|exact H2]
    | [H: phcDisj ?x ?y |- phcValid (phcUnion ?x ?y)] => by apply phcUnion_valid
    | [H: phcDisj ?y ?x |- phcValid (phcUnion ?x ?y)] => symmetry in H; by apply phcUnion_valid
    | [H: phcDisj ?x ?y |- phcValid ?x] => by apply phcDisj_valid_l with y
    | [H: phcDisj ?x ?y |- phcValid ?y] => by apply phcDisj_valid_r with x
    | [H: phcDisj ?x ?y |- phcValid ?x /\ phcValid ?y] => by apply phcDisj_valid
    | [H: phcDisj ?y ?x |- phcValid ?x /\ phcValid ?y] => apply phcDisj_valid; by symmetry
    | [H1: phcDisj ?y ?x, H2: phcDisj (phcUnion ?x ?y) ?z |- phcDisj ?y ?z] => apply phcDisj_union_l with x; [symmetry; exact H1|exact H2]
    | [H1: phcDisj ?x ?y, H2: phcDisj (phcUnion ?y ?x) ?z |- phcDisj ?y ?z] => apply phcDisj_union_l with x; [exact H1|by rewrite phcUnion_comm]
    | [H1: phcDisj ?x ?y, H2: phcDisj (phcUnion ?x ?y) ?z |- phcDisj ?z ?y] => symmetry; apply phcDisj_union_l with x; [exact H1|exact H2]
    | [H1: phcDisj ?z ?y, H2: phcDisj ?x (phcUnion ?y ?z) |- phcDisj ?x ?y] => apply phcDisj_union_r with z; [symmetry; exact H1|exact H2]
    | [H1: phcDisj ?y ?z, H2: phcDisj ?x (phcUnion ?z ?y) |- phcDisj ?x ?y] => apply phcDisj_union_r with z; [exact H1|by rewrite phcUnion_comm]
    | [H1: phcDisj ?y ?z, H2: phcDisj ?x (phcUnion ?y ?z) |- phcDisj ?y ?x] => symmetry; by apply phcDisj_union_r with z
    | [H1: phcDisj ?y ?x, H2: phcDisj (phcUnion ?x ?y) ?z |- phcDisj ?x (phcUnion ?y ?z)] => apply phcDisj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: phcDisj ?x ?y, H2: phcDisj (phcUnion ?y ?x) ?z |- phcDisj ?x (phcUnion ?y ?z)] => apply phcDisj_assoc_l; [exact H1|by rewrite phcUnion_comm]
    | [H1: phcDisj ?x ?y, H2: phcDisj (phcUnion ?x ?y) ?z |- phcDisj ?x (phcUnion ?z ?y)] => rewrite phcUnion_comm; by apply phcDisj_assoc_l
    | [H1: phcDisj ?z ?y, H2: phcDisj ?x (phcUnion ?y ?z) |- phcDisj (phcUnion ?x ?y) ?z] => apply phcDisj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: phcDisj ?y ?z, H2: phcDisj ?x (phcUnion ?z ?y) |- phcDisj (phcUnion ?x ?y) ?z] => apply phcDisj_assoc_r; [exact H1|by rewrite phcUnion_comm]
    | [H1: phcDisj ?y ?z, H2: phcDisj ?x (phcUnion ?y ?z) |- phcDisj (phcUnion ?y ?x) ?z] => rewrite phcUnion_comm; by apply phcDisj_assoc_r
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj ?y ?z] => symmetry in H2; by apply phcDisj_union_l with x
    | [H1: phcDisj ?y ?x, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj ?y ?z] => symmetry in H1; symmetry in H2; by apply phcDisj_union_l with x
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?y ?x) |- phcDisj ?y ?z] => symmetry in H2; apply phcDisj_union_l with x; auto; rewrite phcUnion_comm; auto; fail
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj ?z ?y] => symmetry; symmetry in H2; apply phcDisj_union_l with x; auto; fail
    | [H1: phcDisj ?y ?z, H2: phcDisj (phcUnion ?y ?z) ?x |- phcDisj ?x ?y] => symmetry in H2; by apply phcDisj_union_r with z
    | [H1: phcDisj ?z ?y, H2: phcDisj (phcUnion ?y ?z) ?x |- phcDisj ?x ?y] => symmetry in H1; symmetry in H2; by apply phcDisj_union_r with z
    | [H1: phcDisj ?y ?z, H2: phcDisj (phcUnion ?z ?y) ?x |- phcDisj ?x ?y] => symmetry in H2; apply phcDisj_union_r with z; auto; by rewrite phcUnion_comm
    | [H1: phcDisj ?y ?z, H2: phcDisj (phcUnion ?y ?z) ?x |- phcDisj ?y ?x] => symmetry; symmetry in H2; by apply phcDisj_union_r with z
    | [H1: phcDisj ?y ?x, H2: phcDisj (phcUnion ?y ?x) ?z |- phcDisj ?x (phcUnion ?z ?y)] => rewrite phcUnion_comm in H2; rewrite phcUnion_comm; apply phcDisj_assoc_l; [by symmetry|exact H2]
    | [H1: phcDisj ?z ?y, H2: phcDisj ?x (phcUnion ?z ?y) |- phcDisj (phcUnion ?y ?x) ?z] => rewrite phcUnion_comm in H2; rewrite phcUnion_comm; apply phcDisj_assoc_r; [by symmetry|exact H2]
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj ?x (phcUnion ?y ?z)] => symmetry in H2; by apply phcDisj_assoc_l
    | [H1: phcDisj ?y ?x, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj ?x (phcUnion ?y ?z)] => symmetry in H1; symmetry in H2; by apply phcDisj_assoc_l
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?y ?x) |- phcDisj ?x (phcUnion ?y ?z)] => apply phcDisj_assoc_l; [exact H1|symmetry; by rewrite phcUnion_comm]
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj ?x (phcUnion ?z ?y)] => rewrite phcUnion_comm; apply phcDisj_assoc_l; [exact H1|by symmetry]
    | [H1: phcDisj ?y ?x, H2: phcDisj ?z (phcUnion ?y ?x) |- phcDisj ?x (phcUnion ?y ?z)] => apply phcDisj_assoc_l; [by symmetry|]; symmetry; rewrite phcUnion_comm; auto; by symmetry
    | [H1: phcDisj ?y ?x, H2: phcDisj ?z (phcUnion ?y ?x) |- phcDisj ?x (phcUnion ?z ?y)] => rewrite phcUnion_comm in H2; rewrite phcUnion_comm; apply phcDisj_assoc_l; auto; by symmetry
    | [H1: phcDisj ?y ?x, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj (phcUnion ?y ?z) ?x] => symmetry; apply phcDisj_assoc_l; by symmetry
    | [H1: phcDisj ?x ?y, H2: phcDisj ?z (phcUnion ?x ?y) |- phcDisj (phcUnion ?z ?y) ?x] => apply phcDisj_assoc_r; [by symmetry|by rewrite phcUnion_comm]
    | [|- phcUnion ?x (phcUnion ?y ?z) = phcUnion (phcUnion ?x ?y) ?z] => by apply phcUnion_assoc
    | [|- phcUnion (phcUnion ?x ?y) ?z = phcUnion ?x (phcUnion ?y ?z)] => symmetry; by apply phcUnion_assoc
    | [|- phcUnion ?x ?y = phcUnion ?y ?x] => by apply phcUnion_comm
    | [|- phcUnion ?x PHCfree = ?x] => by apply phcUnion_free_l
    | [|- phcUnion PHCfree ?x = ?x] => by apply phcUnion_free_r
    | [|- ?x = phcUnion ?x PHCfree] => symmetry; by apply phcUnion_free_l
    | [|- ?x = phcUnion PHCfree ?x] => symmetry; by apply phcUnion_free_r
    | [|- phcUnion ?x (phIden _) = ?x] => unfold phIden; by apply phcUnion_free_l
    | [|- phcUnion (phIden _) ?x = ?x] => unfold phIden; by apply phcUnion_free_r
    | [|- phcUnion ?x (phcUnion ?y ?z) = phcUnion ?y (phcUnion ?x ?z)] => by apply phcUnion_swap_l
    | [|- phcUnion (phcUnion ?x ?y) ?z = phcUnion (phcUnion ?x ?z) ?y] => by apply phcUnion_swap_r
    | [|- phcUnion (phcUnion ?x ?z) (phcUnion ?y ?w) = phcUnion (phcUnion ?x ?y) (phcUnion ?z ?w)] => by apply phcUnion_compat
    | [H: phcEntire ?x |- phcEntire (phcUnion ?x ?y)] => apply phcEntire_union; [clear H; phcsolve|by left]
    | [H: phcEntire ?y |- phcEntire (phcUnion ?x ?y)] => apply phcEntire_union; [clear H; phcsolve|by right]
    | [H: phcEntire (?x ?v) |- phcEntire (phUnion ?x ?y ?v)] => apply phcEntire_union; [clear H; phcsolve|by left]
    | [H: phcEntire (?y ?v) |- phcEntire (phUnion ?x ?y ?v)] => apply phcEntire_union; [clear H; phcsolve|by right]
    | _ => fail
  end.


(** *** Unit tests *)

(** Below several unit tests are given for [phcsolve]. *)

Goal phcValid PHCfree.
Proof. phcsolve. Qed.
Goal phcDisj PHCfree PHCfree.
Proof. phcsolve. Qed.
Goal forall x, phcValid x -> phcDisj x PHCfree.
Proof. intros. phcsolve. Qed.
Goal forall x, phcValid x -> phcDisj PHCfree x.
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcDisj y x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj (phcUnion x y) z -> phcDisj y z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj x (phcUnion y z) -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj (phcUnion x y) z -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj x (phcUnion y z) -> phcDisj (phcUnion x y) z.
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcValid (phcUnion x y).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj y x -> phcValid (phcUnion x y).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcValid x.
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcValid y.
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcValid x /\ phcValid y.
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj y x -> phcValid x /\ phcValid y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj (phcUnion x y) z -> phcDisj y z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj (phcUnion y x) z -> phcDisj y z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj (phcUnion x y) z -> phcDisj z y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj z y -> phcDisj x (phcUnion y z) -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj x (phcUnion z y) -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj x (phcUnion y z) -> phcDisj y x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj (phcUnion x y) z -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj (phcUnion y x) z -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj (phcUnion x y) z -> phcDisj x (phcUnion z y).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj z y -> phcDisj x (phcUnion y z) -> phcDisj (phcUnion x y) z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj x (phcUnion z y) -> phcDisj (phcUnion x y) z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj x (phcUnion y z) -> phcDisj (phcUnion y x) z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion x y) -> phcDisj y z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion x y) -> phcDisj y z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion y x) -> phcDisj y z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion x y) -> phcDisj z y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj (phcUnion y z) x -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj z y -> phcDisj (phcUnion y z) x -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj (phcUnion z y) x -> phcDisj x y.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y z -> phcDisj (phcUnion y z) x -> phcDisj y x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj (phcUnion y x) z -> phcDisj x (phcUnion z y).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj z y -> phcDisj x (phcUnion z y) -> phcDisj (phcUnion y x) z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion x y) -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj z y -> phcDisj x (phcUnion z y) -> phcDisj (phcUnion y x) z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion x y) -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion y x) -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion x y) -> phcDisj x (phcUnion z y).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion y x) -> phcDisj x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion y x) -> phcDisj x (phcUnion z y).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion x y) -> phcDisj (phcUnion y z) x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion x y) -> phcDisj (phcUnion y z) x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj x y -> phcDisj z (phcUnion x y) -> phcDisj (phcUnion z y) x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion y x) -> phcDisj (phcUnion y z) x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcDisj y x -> phcDisj z (phcUnion y x) -> phcDisj (phcUnion z y) x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcUnion x (phcUnion y z) = phcUnion (phcUnion x y) z.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcUnion (phcUnion x y) z = phcUnion x (phcUnion y z).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcUnion x y = phcUnion y x.
Proof. intros. phcsolve. Qed.
Goal forall x, phcUnion x PHCfree = x.
Proof. intros. phcsolve. Qed.
Goal forall x, phcUnion PHCfree x = x.
Proof. intros. phcsolve. Qed.
Goal forall x, x = phcUnion x PHCfree.
Proof. intros. phcsolve. Qed.
Goal forall x, x = phcUnion PHCfree x.
Proof. intros. phcsolve. Qed.
Goal forall x v, phcUnion x (phIden v) = x.
Proof. intros. phcsolve. Qed.
Goal forall x v, phcUnion (phIden v) x = x.
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcUnion x (phcUnion y z) = phcUnion y (phcUnion x z).
Proof. intros. phcsolve. Qed.
Goal forall x y z, phcUnion (phcUnion x y) z = phcUnion (phcUnion x z) y.
Proof. intros. phcsolve. Qed.
Goal forall x y z w, phcUnion (phcUnion x z) (phcUnion y w) = phcUnion (phcUnion x y) (phcUnion z w).
Proof. intros. phcsolve. Qed.
Goal forall x y z w, phcUnion (phcUnion x y) (phcUnion z w) = phcUnion (phcUnion x z) (phcUnion y w).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcEntire x -> phcEntire (phcUnion x y).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj y x -> phcEntire x -> phcEntire (phcUnion x y).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj x y -> phcEntire y -> phcEntire (phcUnion x y).
Proof. intros. phcsolve. Qed.
Goal forall x y, phcDisj y x -> phcEntire y -> phcEntire (phcUnion x y).
Proof. intros. phcsolve. Qed.
Goal forall x y v, phDisj x y -> phcEntire (x v) -> phcEntire (phUnion x y v).
Proof. intros. phcsolve. Qed.
Goal forall x y v, phDisj y x -> phcEntire (x v) -> phcEntire (phUnion x y v).
Proof. intros. phcsolve. Qed.
Goal forall x y v, phDisj x y -> phcEntire (y v) -> phcEntire (phUnion x y v).
Proof. intros. phcsolve. Qed.
Goal forall x y v, phDisj y x -> phcEntire (y v) -> phcEntire (phUnion x y v).
Proof. intros. phcsolve. Qed.

Ltac ghcsolve :=
  clarify; match goal with
    | [|- ghcValid GHCfree] => apply ghcValid_free
    | [|- ghcDisj GHCfree GHCfree] => by apply ghcDisj_free_l, ghcValid_free
    | [|- ghcDisj ?x GHCfree] => apply ghcDisj_free_l; ghcsolve
    | [|- ghcDisj GHCfree ?x] => apply ghcDisj_free_r; ghcsolve
    | [H: ghcDisj ?x ?y |- ghcDisj ?x ?y] => exact H
    | [H: ghcDisj ?x ?y |- ghcDisj ?y ?x] => symmetry; exact H
    | [H: ghDisj ?x ?y |- ghcDisj (?x ?v) (?y ?v)] => by apply H
    | [H: ghDisj ?y ?x |- ghcDisj (?x ?v) (?y ?v)] => symmetry; by apply H
    | [H1: ghcDisj ?x ?y, H2: ghcDisj (ghcUnion ?x ?y) ?z |- ghcDisj ?y ?z] => apply ghcDisj_union_l with x; [exact H1|exact H2]
    | [H1: ghcDisj ?y ?z, H2: ghcDisj ?x (ghcUnion ?y ?z) |- ghcDisj ?x ?y] => apply ghcDisj_union_r with z; [exact H1|exact H2]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj (ghcUnion ?x ?y) ?z |- ghcDisj ?x (ghcUnion ?y ?z)] => apply ghcDisj_assoc_l; [exact H1|exact H2]
    | [H1: ghcDisj ?y ?z, H2: ghcDisj ?x (ghcUnion ?y ?z) |- ghcDisj (ghcUnion ?x ?y) ?z] => apply ghcDisj_assoc_r; [exact H1|exact H2]
    | [H: ghcDisj ?x ?y |- ghcValid (ghcUnion ?x ?y)] => by apply ghcUnion_valid
    | [H: ghcDisj ?y ?x |- ghcValid (ghcUnion ?x ?y)] => symmetry in H; by apply ghcUnion_valid
    | [H: ghcDisj ?x ?y |- ghcValid ?x] => by apply ghcDisj_valid_l with y
    | [H: ghcDisj ?x ?y |- ghcValid ?y] => by apply ghcDisj_valid_r with x
    | [H: ghcDisj ?x ?y |- ghcValid ?x /\ ghcValid ?y] => by apply ghcDisj_valid
    | [H: ghcDisj ?y ?x |- ghcValid ?x /\ ghcValid ?y] => apply ghcDisj_valid; by symmetry
    | [H1: ghcDisj ?y ?x, H2: ghcDisj (ghcUnion ?x ?y) ?z |- ghcDisj ?y ?z] => apply ghcDisj_union_l with x; [symmetry; exact H1|exact H2]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj (ghcUnion ?y ?x) ?z |- ghcDisj ?y ?z] => apply ghcDisj_union_l with x; [exact H1|by rewrite ghcUnion_comm]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj (ghcUnion ?x ?y) ?z |- ghcDisj ?z ?y] => symmetry; apply ghcDisj_union_l with x; [exact H1|exact H2]
    | [H1: ghcDisj ?z ?y, H2: ghcDisj ?x (ghcUnion ?y ?z) |- ghcDisj ?x ?y] => apply ghcDisj_union_r with z; [symmetry; exact H1|exact H2]
    | [H1: ghcDisj ?y ?z, H2: ghcDisj ?x (ghcUnion ?z ?y) |- ghcDisj ?x ?y] => apply ghcDisj_union_r with z; [exact H1|by rewrite ghcUnion_comm]
    | [H1: ghcDisj ?y ?z, H2: ghcDisj ?x (ghcUnion ?y ?z) |- ghcDisj ?y ?x] => symmetry; by apply ghcDisj_union_r with z
    | [H1: ghcDisj ?y ?x, H2: ghcDisj (ghcUnion ?x ?y) ?z |- ghcDisj ?x (ghcUnion ?y ?z)] => apply ghcDisj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj (ghcUnion ?y ?x) ?z |- ghcDisj ?x (ghcUnion ?y ?z)] => apply ghcDisj_assoc_l; [exact H1|by rewrite ghcUnion_comm]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj (ghcUnion ?x ?y) ?z |- ghcDisj ?x (ghcUnion ?z ?y)] => rewrite ghcUnion_comm; by apply ghcDisj_assoc_l
    | [H1: ghcDisj ?z ?y, H2: ghcDisj ?x (ghcUnion ?y ?z) |- ghcDisj (ghcUnion ?x ?y) ?z] => apply ghcDisj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: ghcDisj ?y ?z, H2: ghcDisj ?x (ghcUnion ?z ?y) |- ghcDisj (ghcUnion ?x ?y) ?z] => apply ghcDisj_assoc_r; [exact H1|by rewrite ghcUnion_comm]
    | [H1: ghcDisj ?y ?z, H2: ghcDisj ?x (ghcUnion ?y ?z) |- ghcDisj (ghcUnion ?y ?x) ?z] => rewrite ghcUnion_comm; by apply ghcDisj_assoc_r
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj ?y ?z] => symmetry in H2; by apply ghcDisj_union_l with x
    | [H1: ghcDisj ?y ?x, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj ?y ?z] => symmetry in H1; symmetry in H2; by apply ghcDisj_union_l with x
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?y ?x) |- ghcDisj ?y ?z] => symmetry in H2; apply ghcDisj_union_l with x; auto; rewrite ghcUnion_comm; auto; fail
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj ?z ?y] => symmetry; symmetry in H2; apply ghcDisj_union_l with x; auto; fail
    | [H1: ghcDisj ?y ?z, H2: ghcDisj (ghcUnion ?y ?z) ?x |- ghcDisj ?x ?y] => symmetry in H2; by apply ghcDisj_union_r with z
    | [H1: ghcDisj ?z ?y, H2: ghcDisj (ghcUnion ?y ?z) ?x |- ghcDisj ?x ?y] => symmetry in H1; symmetry in H2; by apply ghcDisj_union_r with z
    | [H1: ghcDisj ?y ?z, H2: ghcDisj (ghcUnion ?z ?y) ?x |- ghcDisj ?x ?y] => symmetry in H2; apply ghcDisj_union_r with z; auto; by rewrite ghcUnion_comm
    | [H1: ghcDisj ?y ?z, H2: ghcDisj (ghcUnion ?y ?z) ?x |- ghcDisj ?y ?x] => symmetry; symmetry in H2; by apply ghcDisj_union_r with z
    | [H1: ghcDisj ?y ?x, H2: ghcDisj (ghcUnion ?y ?x) ?z |- ghcDisj ?x (ghcUnion ?z ?y)] => rewrite ghcUnion_comm in H2; rewrite ghcUnion_comm; apply ghcDisj_assoc_l; [by symmetry|exact H2]
    | [H1: ghcDisj ?z ?y, H2: ghcDisj ?x (ghcUnion ?z ?y) |- ghcDisj (ghcUnion ?y ?x) ?z] => rewrite ghcUnion_comm in H2; rewrite ghcUnion_comm; apply ghcDisj_assoc_r; [by symmetry|exact H2]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj ?x (ghcUnion ?y ?z)] => symmetry in H2; by apply ghcDisj_assoc_l
    | [H1: ghcDisj ?y ?x, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj ?x (ghcUnion ?y ?z)] => symmetry in H1; symmetry in H2; by apply ghcDisj_assoc_l
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?y ?x) |- ghcDisj ?x (ghcUnion ?y ?z)] => apply ghcDisj_assoc_l; [exact H1|symmetry; by rewrite ghcUnion_comm]
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj ?x (ghcUnion ?z ?y)] => rewrite ghcUnion_comm; apply ghcDisj_assoc_l; [exact H1|by symmetry]
    | [H1: ghcDisj ?y ?x, H2: ghcDisj ?z (ghcUnion ?y ?x) |- ghcDisj ?x (ghcUnion ?y ?z)] => apply ghcDisj_assoc_l; [by symmetry|]; symmetry; rewrite ghcUnion_comm; auto; by symmetry
    | [H1: ghcDisj ?y ?x, H2: ghcDisj ?z (ghcUnion ?y ?x) |- ghcDisj ?x (ghcUnion ?z ?y)] => rewrite ghcUnion_comm in H2; rewrite ghcUnion_comm; apply ghcDisj_assoc_l; auto; by symmetry
    | [H1: ghcDisj ?y ?x, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj (ghcUnion ?y ?z) ?x] => symmetry; apply ghcDisj_assoc_l; by symmetry
    | [H1: ghcDisj ?x ?y, H2: ghcDisj ?z (ghcUnion ?x ?y) |- ghcDisj (ghcUnion ?z ?y) ?x] => apply ghcDisj_assoc_r; [by symmetry|by rewrite ghcUnion_comm]
    | [|- ghcUnion ?x (ghcUnion ?y ?z) = ghcUnion (ghcUnion ?x ?y) ?z] => by apply ghcUnion_assoc
    | [|- ghcUnion (ghcUnion ?x ?y) ?z = ghcUnion ?x (ghcUnion ?y ?z)] => symmetry; by apply ghcUnion_assoc
    | [|- ghcUnion ?x ?y = ghcUnion ?y ?x] => by apply ghcUnion_comm
    | [|- ghcUnion ?x GHCfree = ?x] => by apply ghcUnion_free_l
    | [|- ghcUnion GHCfree ?x = ?x] => by apply ghcUnion_free_r
    | [|- ?x = ghcUnion ?x GHCfree] => symmetry; by apply ghcUnion_free_l
    | [|- ?x = ghcUnion GHCfree ?x] => symmetry; by apply ghcUnion_free_r
    | [|- ghcUnion ?x (ghIden _) = ?x] => unfold ghIden; by apply ghcUnion_free_l
    | [|- ghcUnion (ghIden _) ?x = ?x] => unfold ghIden; by apply ghcUnion_free_r
    | [|- ghcUnion ?x (ghcUnion ?y ?z) = ghcUnion ?y (ghcUnion ?x ?z)] => by apply ghcUnion_swap_l
    | [|- ghcUnion (ghcUnion ?x ?y) ?z = ghcUnion (ghcUnion ?x ?z) ?y] => by apply ghcUnion_swap_r
    | [|- ghcUnion (ghcUnion ?x ?z) (ghcUnion ?y ?w) = ghcUnion (ghcUnion ?x ?y) (ghcUnion ?z ?w)] => by apply ghcUnion_compat
    | [H: ghcEntire ?x |- ghcEntire (ghcUnion ?x ?y)] => apply ghcEntire_union; [clear H; ghcsolve|by left]
    | [H: ghcEntire ?y |- ghcEntire (ghcUnion ?x ?y)] => apply ghcEntire_union; [clear H; ghcsolve|by right]
    | [H: ghcEntire (?x ?v) |- ghcEntire (ghUnion ?x ?y ?v)] => apply ghcEntire_union; [clear H; ghcsolve|by left]
    | [H: ghcEntire (?y ?v) |- ghcEntire (ghUnion ?x ?y ?v)] => apply ghcEntire_union; [clear H; ghcsolve|by right]
    | _ => fail
  end.

Goal ghcValid GHCfree.
Proof. ghcsolve. Qed.
Goal ghcDisj GHCfree GHCfree.
Proof. ghcsolve. Qed.
Goal forall x, ghcValid x -> ghcDisj x GHCfree.
Proof. intros. ghcsolve. Qed.
Goal forall x, ghcValid x -> ghcDisj GHCfree x.
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcDisj y x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj (ghcUnion x y) z -> ghcDisj y z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj x (ghcUnion y z) -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj (ghcUnion x y) z -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj x (ghcUnion y z) -> ghcDisj (ghcUnion x y) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcValid (ghcUnion x y).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj y x -> ghcValid (ghcUnion x y).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcValid x.
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcValid y.
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcValid x /\ ghcValid y.
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj y x -> ghcValid x /\ ghcValid y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj (ghcUnion x y) z -> ghcDisj y z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj (ghcUnion y x) z -> ghcDisj y z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj (ghcUnion x y) z -> ghcDisj z y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj z y -> ghcDisj x (ghcUnion y z) -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj x (ghcUnion z y) -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj x (ghcUnion y z) -> ghcDisj y x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj (ghcUnion x y) z -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj (ghcUnion y x) z -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj (ghcUnion x y) z -> ghcDisj x (ghcUnion z y).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj z y -> ghcDisj x (ghcUnion y z) -> ghcDisj (ghcUnion x y) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj x (ghcUnion z y) -> ghcDisj (ghcUnion x y) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj x (ghcUnion y z) -> ghcDisj (ghcUnion y x) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion x y) -> ghcDisj y z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion x y) -> ghcDisj y z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion y x) -> ghcDisj y z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion x y) -> ghcDisj z y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj (ghcUnion y z) x -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj z y -> ghcDisj (ghcUnion y z) x -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj (ghcUnion z y) x -> ghcDisj x y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y z -> ghcDisj (ghcUnion y z) x -> ghcDisj y x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj (ghcUnion y x) z -> ghcDisj x (ghcUnion z y).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj z y -> ghcDisj x (ghcUnion z y) -> ghcDisj (ghcUnion y x) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion x y) -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj z y -> ghcDisj x (ghcUnion z y) -> ghcDisj (ghcUnion y x) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion x y) -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion y x) -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion x y) -> ghcDisj x (ghcUnion z y).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion y x) -> ghcDisj x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion y x) -> ghcDisj x (ghcUnion z y).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion x y) -> ghcDisj (ghcUnion y z) x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion x y) -> ghcDisj (ghcUnion y z) x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj x y -> ghcDisj z (ghcUnion x y) -> ghcDisj (ghcUnion z y) x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion y x) -> ghcDisj (ghcUnion y z) x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcDisj y x -> ghcDisj z (ghcUnion y x) -> ghcDisj (ghcUnion z y) x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcUnion x (ghcUnion y z) = ghcUnion (ghcUnion x y) z.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcUnion (ghcUnion x y) z = ghcUnion x (ghcUnion y z).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcUnion x y = ghcUnion y x.
Proof. intros. ghcsolve. Qed.
Goal forall x, ghcUnion x GHCfree = x.
Proof. intros. ghcsolve. Qed.
Goal forall x, ghcUnion GHCfree x = x.
Proof. intros. ghcsolve. Qed.
Goal forall x, x = ghcUnion x GHCfree.
Proof. intros. ghcsolve. Qed.
Goal forall x, x = ghcUnion GHCfree x.
Proof. intros. ghcsolve. Qed.
Goal forall x v, ghcUnion x (ghIden v) = x.
Proof. intros. ghcsolve. Qed.
Goal forall x v, ghcUnion (ghIden v) x = x.
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcUnion x (ghcUnion y z) = ghcUnion y (ghcUnion x z).
Proof. intros. ghcsolve. Qed.
Goal forall x y z, ghcUnion (ghcUnion x y) z = ghcUnion (ghcUnion x z) y.
Proof. intros. ghcsolve. Qed.
Goal forall x y z w, ghcUnion (ghcUnion x z) (ghcUnion y w) = ghcUnion (ghcUnion x y) (ghcUnion z w).
Proof. intros. ghcsolve. Qed.
Goal forall x y z w, ghcUnion (ghcUnion x y) (ghcUnion z w) = ghcUnion (ghcUnion x z) (ghcUnion y w).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcEntire x -> ghcEntire (ghcUnion x y).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj y x -> ghcEntire x -> ghcEntire (ghcUnion x y).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj x y -> ghcEntire y -> ghcEntire (ghcUnion x y).
Proof. intros. ghcsolve. Qed.
Goal forall x y, ghcDisj y x -> ghcEntire y -> ghcEntire (ghcUnion x y).
Proof. intros. ghcsolve. Qed.
Goal forall x y v, ghDisj x y -> ghcEntire (x v) -> ghcEntire (ghUnion x y v).
Proof. intros. ghcsolve. Qed.
Goal forall x y v, ghDisj y x -> ghcEntire (x v) -> ghcEntire (ghUnion x y v).
Proof. intros. ghcsolve. Qed.
Goal forall x y v, ghDisj x y -> ghcEntire (y v) -> ghcEntire (ghUnion x y v).
Proof. intros. ghcsolve. Qed.
Goal forall x y v, ghDisj y x -> ghcEntire (y v) -> ghcEntire (ghUnion x y v).
Proof. intros. ghcsolve. Qed.



(** ** Permission heap *)

(** The following tactic, [phsolve], gives some proof automation
    for simple (but often occuring)  properties on validity
    and disjointness (and more) of permission heaps. *)

(** This tactic is defined simply as a table of patterns,
    and matching proofs for these patterns. *)

Ltac phsolve :=
  clarify; match goal with
    | [|- phValid phIden] => apply phValid_iden
    | [|- phDisj phIden phIden] => by apply phDisj_iden_l, phValid_iden
    | [|- phDisj ?x phIden] => apply phDisj_iden_l; phsolve
    | [|- phDisj phIden ?x] => apply phDisj_iden_r; phsolve
    | [H: phDisj ?x ?y |- phDisj ?x ?y] => exact H
    | [H: phDisj ?x ?y |- phDisj ?y ?x] => symmetry; exact H
    | [H1: phDisj ?x ?y, H2: phDisj (phUnion ?x ?y) ?z |- phDisj ?y ?z] => apply phDisj_union_l with x; [exact H1|exact H2]
    | [H1: phDisj ?y ?z, H2: phDisj ?x (phUnion ?y ?z) |- phDisj ?x ?y] => apply phDisj_union_r with z; [exact H1|exact H2]
    | [H1: phDisj ?x ?y, H2: phDisj (phUnion ?x ?y) ?z |- phDisj ?x (phUnion ?y ?z)] => apply phDisj_assoc_l; [exact H1|exact H2]
    | [H1: phDisj ?y ?z, H2: phDisj ?x (phUnion ?y ?z) |- phDisj (phUnion ?x ?y) ?z] => apply phDisj_assoc_r; [exact H1|exact H2]
    | [H: phDisj ?x ?y |- phValid (phUnion ?x ?y)] => by apply phUnion_valid
    | [H: phDisj ?y ?x |- phValid (phUnion ?x ?y)] => symmetry in H; by apply phUnion_valid
    | [H: phDisj ?x ?y |- phValid ?x] => by apply phDisj_valid_l with y
    | [H: phDisj ?x ?y |- phValid ?y] => by apply phDisj_valid_r with x
    | [H: phDisj ?x ?y |- phValid ?x /\ phValid ?y] => by apply phDisj_valid
    | [H: phDisj ?y ?x |- phValid ?x /\ phValid ?y] => apply phDisj_valid; by symmetry
    | [H1: phDisj ?y ?x, H2: phDisj (phUnion ?x ?y) ?z |- phDisj ?y ?z] => apply phDisj_union_l with x; [symmetry; exact H1|exact H2]
    | [H1: phDisj ?x ?y, H2: phDisj (phUnion ?y ?x) ?z |- phDisj ?y ?z] => apply phDisj_union_l with x; [exact H1|by rewrite phUnion_comm]
    | [H1: phDisj ?x ?y, H2: phDisj (phUnion ?x ?y) ?z |- phDisj ?z ?y] => symmetry; apply phDisj_union_l with x; [exact H1|exact H2]
    | [H1: phDisj ?z ?y, H2: phDisj ?x (phUnion ?y ?z) |- phDisj ?x ?y] => apply phDisj_union_r with z; [symmetry; exact H1|exact H2]
    | [H1: phDisj ?y ?z, H2: phDisj ?x (phUnion ?z ?y) |- phDisj ?x ?y] => apply phDisj_union_r with z; [exact H1|by rewrite phUnion_comm]
    | [H1: phDisj ?y ?z, H2: phDisj ?x (phUnion ?y ?z) |- phDisj ?y ?x] => symmetry; by apply phDisj_union_r with z
    | [H1: phDisj ?y ?x, H2: phDisj (phUnion ?x ?y) ?z |- phDisj ?x (phUnion ?y ?z)] => apply phDisj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: phDisj ?x ?y, H2: phDisj (phUnion ?y ?x) ?z |- phDisj ?x (phUnion ?y ?z)] => apply phDisj_assoc_l; [exact H1|by rewrite phUnion_comm]
    | [H1: phDisj ?x ?y, H2: phDisj (phUnion ?x ?y) ?z |- phDisj ?x (phUnion ?z ?y)] => rewrite phUnion_comm; by apply phDisj_assoc_l
    | [H1: phDisj ?z ?y, H2: phDisj ?x (phUnion ?y ?z) |- phDisj (phUnion ?x ?y) ?z] => apply phDisj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: phDisj ?y ?z, H2: phDisj ?x (phUnion ?z ?y) |- phDisj (phUnion ?x ?y) ?z] => apply phDisj_assoc_r; [exact H1|by rewrite phUnion_comm]
    | [H1: phDisj ?y ?z, H2: phDisj ?x (phUnion ?y ?z) |- phDisj (phUnion ?y ?x) ?z] => rewrite phUnion_comm; by apply phDisj_assoc_r
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?x ?y) |- phDisj ?y ?z] => symmetry in H2; by apply phDisj_union_l with x
    | [H1: phDisj ?y ?x, H2: phDisj ?z (phUnion ?x ?y) |- phDisj ?y ?z] => symmetry in H1; symmetry in H2; by apply phDisj_union_l with x
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?y ?x) |- phDisj ?y ?z] => symmetry in H2; apply phDisj_union_l with x; auto; rewrite phUnion_comm; auto; fail
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?x ?y) |- phDisj ?z ?y] => symmetry; symmetry in H2; apply phDisj_union_l with x; auto; fail
    | [H1: phDisj ?y ?z, H2: phDisj (phUnion ?y ?z) ?x |- phDisj ?x ?y] => symmetry in H2; by apply phDisj_union_r with z
    | [H1: phDisj ?z ?y, H2: phDisj (phUnion ?y ?z) ?x |- phDisj ?x ?y] => symmetry in H1; symmetry in H2; by apply phDisj_union_r with z
    | [H1: phDisj ?y ?z, H2: phDisj (phUnion ?z ?y) ?x |- phDisj ?x ?y] => symmetry in H2; apply phDisj_union_r with z; auto; by rewrite phUnion_comm
    | [H1: phDisj ?y ?z, H2: phDisj (phUnion ?y ?z) ?x |- phDisj ?y ?x] => symmetry; symmetry in H2; by apply phDisj_union_r with z
    | [H1: phDisj ?y ?x, H2: phDisj (phUnion ?y ?x) ?z |- phDisj ?x (phUnion ?z ?y)] => rewrite phUnion_comm in H2; rewrite phUnion_comm; apply phDisj_assoc_l; [by symmetry|exact H2]
    | [H1: phDisj ?z ?y, H2: phDisj ?x (phUnion ?z ?y) |- phDisj (phUnion ?y ?x) ?z] => rewrite phUnion_comm in H2; rewrite phUnion_comm; apply phDisj_assoc_r; [by symmetry|exact H2]
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?x ?y) |- phDisj ?x (phUnion ?y ?z)] => symmetry in H2; by apply phDisj_assoc_l
    | [H1: phDisj ?y ?x, H2: phDisj ?z (phUnion ?x ?y) |- phDisj ?x (phUnion ?y ?z)] => symmetry in H1; symmetry in H2; by apply phDisj_assoc_l
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?y ?x) |- phDisj ?x (phUnion ?y ?z)] => apply phDisj_assoc_l; [exact H1|symmetry; by rewrite phUnion_comm]
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?x ?y) |- phDisj ?x (phUnion ?z ?y)] => rewrite phUnion_comm; apply phDisj_assoc_l; [exact H1|by symmetry]
    | [H1: phDisj ?y ?x, H2: phDisj ?z (phUnion ?y ?x) |- phDisj ?x (phUnion ?y ?z)] => apply phDisj_assoc_l; [by symmetry|]; symmetry; rewrite phUnion_comm; auto; by symmetry
    | [H1: phDisj ?y ?x, H2: phDisj ?z (phUnion ?y ?x) |- phDisj ?x (phUnion ?z ?y)] => rewrite phUnion_comm in H2; rewrite phUnion_comm; apply phDisj_assoc_l; auto; by symmetry
    | [H1: phDisj ?y ?x, H2: phDisj ?z (phUnion ?x ?y) |- phDisj (phUnion ?y ?z) ?x] => symmetry; apply phDisj_assoc_l; by symmetry
    | [H1: phDisj ?x ?y, H2: phDisj ?z (phUnion ?x ?y) |- phDisj (phUnion ?z ?y) ?x] => apply phDisj_assoc_r; [by symmetry|by rewrite phUnion_comm]
    | [H: phDisj ?x ?y |- phcDisj (?x ?v) (?y ?v)] => by apply H
    | [H: phDisj ?y ?x |- phcDisj (?x ?v) (?y ?v)] => symmetry; by apply H
    | [|- phDisj (phUpdate _ ?l _) (phUpdate _ ?l _)] => apply phDisj_upd; [phcsolve|phsolve]
    | [|- phUnion (phUnion ?x ?y) ?z = phUnion ?x (phUnion ?y ?z)] => by apply phUnion_assoc
    | [|- phUnion ?x (phUnion ?y ?z) = phUnion (phUnion ?x ?y) ?z] => symmetry; by apply phUnion_assoc
    | [|- phUnion ?x ?y = phUnion ?y ?x] => by apply phUnion_comm
    | [|- phUnion ?x phIden = ?x] => by apply phUnion_iden_l
    | [|- phUnion phIden ?x = ?x] => by apply phUnion_iden_r
    | [|- phUnion ?x (phUnion ?y ?z) = phUnion ?y (phUnion ?x ?z)] => by apply phUnion_swap_l
    | [|- phUnion (phUnion ?x ?y) ?z = phUnion (phUnion ?x ?z) ?y] => by apply phUnion_swap_r
    | [|- phUnion (phUnion ?x ?z) (phUnion ?y ?w) = phUnion (phUnion ?x ?y) (phUnion ?z ?w)] => by apply phUnion_compat
    | [|- phUnion ?x ?y ?v = phcUnion (?x ?v) (?y ?v)] => by apply phUnion_cell
    | [|- phcUnion (?x ?v) (?y ?v) = phUnion ?x ?y ?v] => by apply phUnion_cell
    | [|- phcEntire (phUnion ?x ?y ?v)] => rewrite <- phUnion_cell; phcsolve
    | _ => fail
  end.


(** *** Unit tests *)

(** Below several unit tests are given for [pmesolve]. *)

Goal phValid phIden.
Proof. phsolve. Qed.
Goal phDisj phIden phIden.
Proof. phsolve. Qed.
Goal forall x, phValid x -> phDisj x phIden.
Proof. intros. phsolve. Qed.
Goal forall x, phValid x -> phDisj phIden x.
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj x y -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj x y -> phDisj y x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj (phUnion x y) z -> phDisj y z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj x (phUnion y z) -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj (phUnion x y) z -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj x (phUnion y z) -> phDisj (phUnion x y) z.
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj x y -> phValid (phUnion x y).
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj y x -> phValid (phUnion x y).
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj x y -> phValid x.
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj x y -> phValid y.
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj x y -> phValid x /\ phValid y.
Proof. intros. phsolve. Qed.
Goal forall x y, phDisj y x -> phValid x /\ phValid y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj (phUnion x y) z -> phDisj y z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj (phUnion y x) z -> phDisj y z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj (phUnion x y) z -> phDisj z y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj z y -> phDisj x (phUnion y z) -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj x (phUnion z y) -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj x (phUnion y z) -> phDisj y x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj (phUnion x y) z -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj (phUnion y x) z -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj (phUnion x y) z -> phDisj x (phUnion z y).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj z y -> phDisj x (phUnion y z) -> phDisj (phUnion x y) z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj x (phUnion z y) -> phDisj (phUnion x y) z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj x (phUnion y z) -> phDisj (phUnion y x) z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion x y) -> phDisj y z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion x y) -> phDisj y z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion y x) -> phDisj y z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion x y) -> phDisj z y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj (phUnion y z) x -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj z y -> phDisj (phUnion y z) x -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj (phUnion z y) x -> phDisj x y.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y z -> phDisj (phUnion y z) x -> phDisj y x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj (phUnion y x) z -> phDisj x (phUnion z y).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj z y -> phDisj x (phUnion z y) -> phDisj (phUnion y x) z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion x y) -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj z y -> phDisj x (phUnion z y) -> phDisj (phUnion y x) z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion x y) -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion y x) -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion x y) -> phDisj x (phUnion z y).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion y x) -> phDisj x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion y x) -> phDisj x (phUnion z y).
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion x y) -> phDisj (phUnion y z) x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion x y) -> phDisj (phUnion y z) x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj x y -> phDisj z (phUnion x y) -> phDisj (phUnion z y) x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion y x) -> phDisj (phUnion y z) x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phDisj y x -> phDisj z (phUnion y x) -> phDisj (phUnion z y) x.
Proof. intros. phsolve. Qed.
Goal forall x y v, phDisj x y -> phcDisj (x v) (y v).
Proof. intros. phsolve. Qed.
Goal forall x y v, phDisj y x -> phcDisj (x v) (y v).
Proof. intros. phsolve. Qed.
Goal forall x y l v w, phDisj x y -> phcDisj v w -> phDisj (phUpdate x l v) (phUpdate y l w).
Proof. intros. phsolve. Qed.
Goal forall x y z, phUnion x (phUnion y z) = phUnion (phUnion x y) z.
Proof. intros. phsolve. Qed.
Goal forall x y z, phUnion (phUnion x y) z = phUnion x (phUnion y z).
Proof. intros. phsolve. Qed.
Goal forall x y, phUnion x y = phUnion y x.
Proof. intros. phsolve. Qed.
Goal forall x, phUnion x phIden = x.
Proof. intros. phsolve. Qed.
Goal forall x, phUnion phIden x = x.
Proof. intros. phsolve. Qed.
Goal forall x y z, phUnion x (phUnion y z) = phUnion y (phUnion x z).
Proof. intros. phsolve. Qed.
Goal forall x y z, phUnion (phUnion x y) z = phUnion (phUnion x z) y.
Proof. intros. phsolve. Qed.
Goal forall x y z w, phUnion (phUnion x z) (phUnion y w) = phUnion (phUnion x y) (phUnion z w).
Proof. intros. phsolve. Qed.
Goal forall x y z w, phUnion (phUnion x y) (phUnion z w) = phUnion (phUnion x z) (phUnion y w).
Proof. intros. phsolve. Qed.
Goal forall x y v, phUnion x y v = phcUnion (x v) (y v).
Proof. intros. phsolve. Qed.
Goal forall x y v, phcUnion (x v) (y v) = phUnion x y v.
Proof. intros. phsolve. Qed.
Goal forall x y v, phcDisj (x v) (y v) -> phcEntire (x v) -> phcEntire (phUnion x y v).
Proof. intros. phsolve. Qed.


Ltac ghsolve :=
  clarify; match goal with
    | [|- ghValid ghIden] => apply ghValid_iden
    | [|- ghDisj ghIden ghIden] => by apply ghDisj_iden_l, ghValid_iden
    | [|- ghDisj ?x ghIden] => apply ghDisj_iden_l; ghsolve
    | [|- ghDisj ghIden ?x] => apply ghDisj_iden_r; ghsolve
    | [H: ghDisj ?x ?y |- ghDisj ?x ?y] => exact H
    | [H: ghDisj ?x ?y |- ghDisj ?y ?x] => symmetry; exact H
    | [H1: ghDisj ?x ?y, H2: ghDisj (ghUnion ?x ?y) ?z |- ghDisj ?y ?z] => apply ghDisj_union_l with x; [exact H1|exact H2]
    | [H1: ghDisj ?y ?z, H2: ghDisj ?x (ghUnion ?y ?z) |- ghDisj ?x ?y] => apply ghDisj_union_r with z; [exact H1|exact H2]
    | [H1: ghDisj ?x ?y, H2: ghDisj (ghUnion ?x ?y) ?z |- ghDisj ?x (ghUnion ?y ?z)] => apply ghDisj_assoc_l; [exact H1|exact H2]
    | [H1: ghDisj ?y ?z, H2: ghDisj ?x (ghUnion ?y ?z) |- ghDisj (ghUnion ?x ?y) ?z] => apply ghDisj_assoc_r; [exact H1|exact H2]
    | [H: ghDisj ?x ?y |- ghValid (ghUnion ?x ?y)] => by apply ghUnion_valid
    | [H: ghDisj ?y ?x |- ghValid (ghUnion ?x ?y)] => symmetry in H; by apply ghUnion_valid
    | [H: ghDisj ?x ?y |- ghValid ?x] => by apply ghDisj_valid_l with y
    | [H: ghDisj ?x ?y |- ghValid ?y] => by apply ghDisj_valid_r with x
    | [H: ghDisj ?x ?y |- ghValid ?x /\ ghValid ?y] => by apply ghDisj_valid
    | [H: ghDisj ?y ?x |- ghValid ?x /\ ghValid ?y] => apply ghDisj_valid; by symmetry
    | [H1: ghDisj ?y ?x, H2: ghDisj (ghUnion ?x ?y) ?z |- ghDisj ?y ?z] => apply ghDisj_union_l with x; [symmetry; exact H1|exact H2]
    | [H1: ghDisj ?x ?y, H2: ghDisj (ghUnion ?y ?x) ?z |- ghDisj ?y ?z] => apply ghDisj_union_l with x; [exact H1|by rewrite ghUnion_comm]
    | [H1: ghDisj ?x ?y, H2: ghDisj (ghUnion ?x ?y) ?z |- ghDisj ?z ?y] => symmetry; apply ghDisj_union_l with x; [exact H1|exact H2]
    | [H1: ghDisj ?z ?y, H2: ghDisj ?x (ghUnion ?y ?z) |- ghDisj ?x ?y] => apply ghDisj_union_r with z; [symmetry; exact H1|exact H2]
    | [H1: ghDisj ?y ?z, H2: ghDisj ?x (ghUnion ?z ?y) |- ghDisj ?x ?y] => apply ghDisj_union_r with z; [exact H1|by rewrite ghUnion_comm]
    | [H1: ghDisj ?y ?z, H2: ghDisj ?x (ghUnion ?y ?z) |- ghDisj ?y ?x] => symmetry; by apply ghDisj_union_r with z
    | [H1: ghDisj ?y ?x, H2: ghDisj (ghUnion ?x ?y) ?z |- ghDisj ?x (ghUnion ?y ?z)] => apply ghDisj_assoc_l; [symmetry; exact H1|exact H2]
    | [H1: ghDisj ?x ?y, H2: ghDisj (ghUnion ?y ?x) ?z |- ghDisj ?x (ghUnion ?y ?z)] => apply ghDisj_assoc_l; [exact H1|by rewrite ghUnion_comm]
    | [H1: ghDisj ?x ?y, H2: ghDisj (ghUnion ?x ?y) ?z |- ghDisj ?x (ghUnion ?z ?y)] => rewrite ghUnion_comm; by apply ghDisj_assoc_l
    | [H1: ghDisj ?z ?y, H2: ghDisj ?x (ghUnion ?y ?z) |- ghDisj (ghUnion ?x ?y) ?z] => apply ghDisj_assoc_r; [symmetry; exact H1|exact H2]
    | [H1: ghDisj ?y ?z, H2: ghDisj ?x (ghUnion ?z ?y) |- ghDisj (ghUnion ?x ?y) ?z] => apply ghDisj_assoc_r; [exact H1|by rewrite ghUnion_comm]
    | [H1: ghDisj ?y ?z, H2: ghDisj ?x (ghUnion ?y ?z) |- ghDisj (ghUnion ?y ?x) ?z] => rewrite ghUnion_comm; by apply ghDisj_assoc_r
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj ?y ?z] => symmetry in H2; by apply ghDisj_union_l with x
    | [H1: ghDisj ?y ?x, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj ?y ?z] => symmetry in H1; symmetry in H2; by apply ghDisj_union_l with x
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?y ?x) |- ghDisj ?y ?z] => symmetry in H2; apply ghDisj_union_l with x; auto; rewrite ghUnion_comm; auto; fail
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj ?z ?y] => symmetry; symmetry in H2; apply ghDisj_union_l with x; auto; fail
    | [H1: ghDisj ?y ?z, H2: ghDisj (ghUnion ?y ?z) ?x |- ghDisj ?x ?y] => symmetry in H2; by apply ghDisj_union_r with z
    | [H1: ghDisj ?z ?y, H2: ghDisj (ghUnion ?y ?z) ?x |- ghDisj ?x ?y] => symmetry in H1; symmetry in H2; by apply ghDisj_union_r with z
    | [H1: ghDisj ?y ?z, H2: ghDisj (ghUnion ?z ?y) ?x |- ghDisj ?x ?y] => symmetry in H2; apply ghDisj_union_r with z; auto; by rewrite ghUnion_comm
    | [H1: ghDisj ?y ?z, H2: ghDisj (ghUnion ?y ?z) ?x |- ghDisj ?y ?x] => symmetry; symmetry in H2; by apply ghDisj_union_r with z
    | [H1: ghDisj ?y ?x, H2: ghDisj (ghUnion ?y ?x) ?z |- ghDisj ?x (ghUnion ?z ?y)] => rewrite ghUnion_comm in H2; rewrite ghUnion_comm; apply ghDisj_assoc_l; [by symmetry|exact H2]
    | [H1: ghDisj ?z ?y, H2: ghDisj ?x (ghUnion ?z ?y) |- ghDisj (ghUnion ?y ?x) ?z] => rewrite ghUnion_comm in H2; rewrite ghUnion_comm; apply ghDisj_assoc_r; [by symmetry|exact H2]
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj ?x (ghUnion ?y ?z)] => symmetry in H2; by apply ghDisj_assoc_l
    | [H1: ghDisj ?y ?x, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj ?x (ghUnion ?y ?z)] => symmetry in H1; symmetry in H2; by apply ghDisj_assoc_l
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?y ?x) |- ghDisj ?x (ghUnion ?y ?z)] => apply ghDisj_assoc_l; [exact H1|symmetry; by rewrite ghUnion_comm]
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj ?x (ghUnion ?z ?y)] => rewrite ghUnion_comm; apply ghDisj_assoc_l; [exact H1|by symmetry]
    | [H1: ghDisj ?y ?x, H2: ghDisj ?z (ghUnion ?y ?x) |- ghDisj ?x (ghUnion ?y ?z)] => apply ghDisj_assoc_l; [by symmetry|]; symmetry; rewrite ghUnion_comm; auto; by symmetry
    | [H1: ghDisj ?y ?x, H2: ghDisj ?z (ghUnion ?y ?x) |- ghDisj ?x (ghUnion ?z ?y)] => rewrite ghUnion_comm in H2; rewrite ghUnion_comm; apply ghDisj_assoc_l; auto; by symmetry
    | [H1: ghDisj ?y ?x, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj (ghUnion ?y ?z) ?x] => symmetry; apply ghDisj_assoc_l; by symmetry
    | [H1: ghDisj ?x ?y, H2: ghDisj ?z (ghUnion ?x ?y) |- ghDisj (ghUnion ?z ?y) ?x] => apply ghDisj_assoc_r; [by symmetry|by rewrite ghUnion_comm]
    | [H: ghDisj ?x ?y |- ghcDisj (?x ?v) (?y ?v)] => by apply H
    | [H: ghDisj ?y ?x |- ghcDisj (?x ?v) (?y ?v)] => symmetry; by apply H
    | [|- ghDisj (ghUpdate _ ?l _) (ghUpdate _ ?l _)] => apply ghDisj_upd; [ghcsolve|ghsolve]
    | [|- ghUnion (ghUnion ?x ?y) ?z = ghUnion ?x (ghUnion ?y ?z)] => by apply ghUnion_assoc
    | [|- ghUnion ?x (ghUnion ?y ?z) = ghUnion (ghUnion ?x ?y) ?z] => symmetry; by apply ghUnion_assoc
    | [|- ghUnion ?x ?y = ghUnion ?y ?x] => by apply ghUnion_comm
    | [|- ghUnion ?x ghIden = ?x] => by apply ghUnion_iden_l
    | [|- ghUnion ghIden ?x = ?x] => by apply ghUnion_iden_r
    | [|- ghUnion ?x (ghUnion ?y ?z) = ghUnion ?y (ghUnion ?x ?z)] => by apply ghUnion_swap_l
    | [|- ghUnion (ghUnion ?x ?y) ?z = ghUnion (ghUnion ?x ?z) ?y] => by apply ghUnion_swap_r
    | [|- ghUnion (ghUnion ?x ?z) (ghUnion ?y ?w) = ghUnion (ghUnion ?x ?y) (ghUnion ?z ?w)] => by apply ghUnion_compat
    | [|- ghUnion ?x ?y ?v = ghcUnion (?x ?v) (?y ?v)] => by apply ghUnion_cell
    | [|- ghcUnion (?x ?v) (?y ?v) = ghUnion ?x ?y ?v] => by apply ghUnion_cell
    | [|- ghcEntire (ghUnion ?x ?y ?v)] => rewrite <- ghUnion_cell; ghcsolve
    | _ => fail
  end.


(** *** Unit tests *)

(** Below several unit tests are given for [pmesolve]. *)

Goal ghValid ghIden.
Proof. ghsolve. Qed.
Goal ghDisj ghIden ghIden.
Proof. ghsolve. Qed.
Goal forall x, ghValid x -> ghDisj x ghIden.
Proof. intros. ghsolve. Qed.
Goal forall x, ghValid x -> ghDisj ghIden x.
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj x y -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj x y -> ghDisj y x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj (ghUnion x y) z -> ghDisj y z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj x (ghUnion y z) -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj (ghUnion x y) z -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj x (ghUnion y z) -> ghDisj (ghUnion x y) z.
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj x y -> ghValid (ghUnion x y).
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj y x -> ghValid (ghUnion x y).
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj x y -> ghValid x.
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj x y -> ghValid y.
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj x y -> ghValid x /\ ghValid y.
Proof. intros. ghsolve. Qed.
Goal forall x y, ghDisj y x -> ghValid x /\ ghValid y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj (ghUnion x y) z -> ghDisj y z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj (ghUnion y x) z -> ghDisj y z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj (ghUnion x y) z -> ghDisj z y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj z y -> ghDisj x (ghUnion y z) -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj x (ghUnion z y) -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj x (ghUnion y z) -> ghDisj y x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj (ghUnion x y) z -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj (ghUnion y x) z -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj (ghUnion x y) z -> ghDisj x (ghUnion z y).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj z y -> ghDisj x (ghUnion y z) -> ghDisj (ghUnion x y) z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj x (ghUnion z y) -> ghDisj (ghUnion x y) z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj x (ghUnion y z) -> ghDisj (ghUnion y x) z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion x y) -> ghDisj y z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion x y) -> ghDisj y z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion y x) -> ghDisj y z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion x y) -> ghDisj z y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj (ghUnion y z) x -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj z y -> ghDisj (ghUnion y z) x -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj (ghUnion z y) x -> ghDisj x y.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y z -> ghDisj (ghUnion y z) x -> ghDisj y x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj (ghUnion y x) z -> ghDisj x (ghUnion z y).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj z y -> ghDisj x (ghUnion z y) -> ghDisj (ghUnion y x) z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion x y) -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj z y -> ghDisj x (ghUnion z y) -> ghDisj (ghUnion y x) z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion x y) -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion y x) -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion x y) -> ghDisj x (ghUnion z y).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion y x) -> ghDisj x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion y x) -> ghDisj x (ghUnion z y).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion x y) -> ghDisj (ghUnion y z) x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion x y) -> ghDisj (ghUnion y z) x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj x y -> ghDisj z (ghUnion x y) -> ghDisj (ghUnion z y) x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion y x) -> ghDisj (ghUnion y z) x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghDisj y x -> ghDisj z (ghUnion y x) -> ghDisj (ghUnion z y) x.
Proof. intros. ghsolve. Qed.
Goal forall x y v, ghDisj x y -> ghcDisj (x v) (y v).
Proof. intros. ghsolve. Qed.
Goal forall x y v, ghDisj y x -> ghcDisj (x v) (y v).
Proof. intros. ghsolve. Qed.
Goal forall x y l v w, ghDisj x y -> ghcDisj v w -> ghDisj (ghUpdate x l v) (ghUpdate y l w).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghUnion x (ghUnion y z) = ghUnion (ghUnion x y) z.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghUnion (ghUnion x y) z = ghUnion x (ghUnion y z).
Proof. intros. ghsolve. Qed.
Goal forall x y, ghUnion x y = ghUnion y x.
Proof. intros. ghsolve. Qed.
Goal forall x, ghUnion x ghIden = x.
Proof. intros. ghsolve. Qed.
Goal forall x, ghUnion ghIden x = x.
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghUnion x (ghUnion y z) = ghUnion y (ghUnion x z).
Proof. intros. ghsolve. Qed.
Goal forall x y z, ghUnion (ghUnion x y) z = ghUnion (ghUnion x z) y.
Proof. intros. ghsolve. Qed.
Goal forall x y z w, ghUnion (ghUnion x z) (ghUnion y w) = ghUnion (ghUnion x y) (ghUnion z w).
Proof. intros. ghsolve. Qed.
Goal forall x y z w, ghUnion (ghUnion x y) (ghUnion z w) = ghUnion (ghUnion x z) (ghUnion y w).
Proof. intros. ghsolve. Qed.
Goal forall x y v, ghUnion x y v = ghcUnion (x v) (y v).
Proof. intros. ghsolve. Qed.
Goal forall x y v, ghcUnion (x v) (y v) = ghUnion x y v.
Proof. intros. ghsolve. Qed.
Goal forall x y v, ghcDisj (x v) (y v) -> ghcEntire (x v) -> ghcEntire (ghUnion x y v).
Proof. intros. ghsolve. Qed.

End HeapSolver.
